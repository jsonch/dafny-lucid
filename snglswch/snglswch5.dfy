include "lucid_base.dfy"


/*
notes: 
   This version of the program is built as an extension of the LucidBase 
   module, which provides infrastructure for events, event queues, and handlers. 

   The biggest change in the handler functions themselves, compared to v4, 
   is that now the assertions reason about the presence of setFiltering events 
   in the switch's pending event queue rather than just using a flag variable 
   to indicate that a setFiltering is in flight. 

   The handler functions themselves have not changed much from previous versions. 
   The best place to start in reading this program is probably at the "Dispatch" 
   method. That is where control transfers from the simulation loop in 
   LucidBase to the event handlers in this program. Note that the 
   constraints on Dispatch are defined in lucid_base.dfy, not here. However, 
   the require and ensure clauses on Dispatch are the same as the require and 
   ensure clauses on each of the handler functions. (See next comment.)

   --- handler predicates ---  
   All event handlers should require and ensure the same sets of predicates.
   The predicates themselves are defined in LucidBase, but they 
   depend on a few application-specific predicates that are _declared_ 
   in LucidBase, but _defined_ in this program, as described below.
   requires: 
      requires correct_internal_time(cur_ev):
         the "time" and "natTime" variables 
         are equal to the time and natTime of the current event
      requires valid_interarrivals([cur_ev] + queue): 
         for all the events to be processed (including the current event):
            1. timestamps are monotonically increasing
            2. successive timestamps satisfy the inter-arrival constraint 
               defined in the application-specific "valid_interarrival"
      requires valid_event_times(this.gstate, [cur_ev] + this.queue)    
         all events to be processed have: 
            1. time (as bits) == time (as nat) % T
            2. satisfy the application-specific "valid_event_time"
      requires pre_dispatch(this.state, gstate, cur_ev, this.queue, this.lastNatTime)
         - this is the application-specific invariant that must 
           hold at the beginning of every event.
         - In this program, it has the parameter constraints, state invariant, 
           recirculation invariant, and one or two other little predicates 
           that may not be needed any more.

   ensures:
      ensures valid_interarrivals([cur_ev] + queue)
         - same definition as in require
      ensures valid_event_times(this.gstate, [cur_ev] + this.queue)    
         - same definition as in require
      ensures post_dispatch(state, gstate, queue, natTime)            
         - this sets up the pre_dispatch for the next event. It is just: 
          |queue| > 0 ==> 
            pre_dispatch(state, gstate, queue[0], queue[1..], queue[0].natTime)

Other notes: 
  "ghost state"
      In this version, I started splitting out some of the ghost state variables 
      and putting them into their own "GhostState" type. Right now, 
      GhostState only has natTimeOn. I could not get the verification to 
      work out when natTimeOn was a ghost variable in state. I think the 
      problem was related to the fact that the fields within state are 
      mutable variables. I could not figure out how to convince 
      the verifier that a change to "state" did _not_ change natTimeOn. 
      So it was easier to just take natTimeOn out of state and put it 
      into its own "ghost state" that has only immutable fields.
      Since the fields are immutable, you change ghost state by 
      making a new copy of it. e.g.: 
         gstate := gstate.(natTimeOn := new_val);
      Although I only needed to separate natTimeOn for this program, 
      it seems like it might be a nice convention to keep the 
      ghost state separate from concrete state. 

  Generate clunkiness
      The generate method is a bit more complicated to invoke than it 
      should be. I will fix this with some local changes that should 
      not affect your initial work.

  Generating non-recirculating events
      There's not yet a representation of 
      "forwarding a packet/event out of the switch". For now, I just 
      kept the "forwarded" return flag for processPacket as an indicator.
*/

module LucidProg refines LucidBase {

    datatype Event = 
      | SimulatedClockTick()
      | HardwareFailure()
      | ProcessPacket(dnsRequest: bool, uniqueSig: nat)
      | SetFiltering(on : bool)
   
    datatype GhostState = 
       | GhostState(natTimeOn : nat)

    class State ... {
      // Address State 
      var lastIntv : bits    // an interval, so first 8-i bits always zero
      var count : nat                           // counter for DNS replies
      var filtering : bool          // turns adaptive filtering on and off
      var timeOn : bits      // implementation of time filtering turned on
      var recircPending : bool          // a "semaphore" for recirculation
      ghost var requestSet : set<nat>   // pending requests, for filtering

      // ghost variables for reasoning about timeOn
      ghost var actualTimeOn : nat 
      const T : nat := 256

      

      ghost var preFilterSet : set<nat> // requestSet, before any deletion
      // ghost var recircSwitch : bool 

      constructor ()
            ensures (this.filtering == false)
            ensures (this.recircPending == false)
            ensures (fresh(this))
            ensures filtering == false
            ensures recircPending == false
            ensures lastIntv == 0
            ensures count == 0
            ensures timeOn == 0
            ensures actualTimeOn == 0
            // ensures natTimeOn == 0
            ensures requestSet == {}
      {
         filtering, recircPending := false, false;
         lastIntv, count, timeOn := 0, 0, 0;
         actualTimeOn := 0;
         // natTimeOn := 0;
         requestSet := {};
      }
    }
   // Parameters
   const I : nat := 16                          // interval length, < T 
   const i : nat := 4                                        // I = 2^i
   const Q : bits                          // maximum DNS response time
   const QRoff : bits                      // Q plus observation window
                                          // for turning filtering off
   const W : nat                      // Bloom-filter window size, >= Q
   const U : nat                               // upper count threshold
   const L : nat                               // lower count threshold

    class Handlers ... {

      constructor init ()
            requires Q > 0
            requires QRoff > Q
            requires W >= Q
            ensures (fresh(state))
            ensures (gstate == GhostState(0))
            // does not establish inter-event invariant
            // because the event queue is empty
      {     
             state := new State();   
             gstate := GhostState(0); 
             queue := [];
      } 

      predicate parameterConstraints ()      // from problem domain, ghost  
      {  I > 0 && QRoff > Q > 0  && W >= Q  }



      ghost predicate valid_interarrival(cur : LocEvent, next : LocEvent)
      {
         (next.natTime - cur.natTime < T - I)
      }


      ghost function valid_event_time(gs : GhostState, ev : LocEvent) : bool 
      {
         ev.natTime < gs.natTimeOn + T
      }

      /*** the inter-event invariant ***/
      ghost predicate pre_dispatch(s : State, gs : GhostState, cur_ev : LocEvent, ev_queue : seq<LocEvent>, lastNatTime : nat)
      {
      
         var natTime := cur_ev.natTime;
         parameterConstraints()
         && (natTime - lastNatTime < T - I)
         && stateInvariant(s, gs, cur_ev.time, cur_ev.natTime)
         // && (natTime < s.actualTimeOn + T) // now enforced by valid_event_time
         && recircInvariant(s, [cur_ev] + ev_queue)
         // && (  state.recircPending ==> (state.filtering == ! state.recircSwitch)  )
      }

      ghost predicate stateInvariant (state : State, gstate : GhostState, time : bits, natTime : nat)         // ghost
         reads state
      {
         // CHANGE: lastNatTime --> natTime because it doesn't make sense in 
         //         SetFiltering (it sets natTimeOn to the current time, not the last time)
              (  gstate.natTimeOn <= natTime  ) 
         && (  state.timeOn == gstate.natTimeOn % T  )
         && (  gstate.natTimeOn >= state.actualTimeOn  )
         && (  state.filtering ==> 
                  (protecting (state, gstate, natTime) <==> protectImplmnt (state, time))  )
         && (  ! state.filtering ==> state.requestSet == {}  )
      }

      ghost predicate protecting (state : State, gstate : GhostState, natTime : nat)  
      reads state                        // ghost
      {  state.filtering && (natTime >= gstate.natTimeOn + Q as nat)  }

      predicate protectImplmnt (state : State, time: bits)
      // protecting is a specification, using history variables.  This
      // is its implementation, which cannot use history variables.
      reads state
      {  state.filtering && elapsedTime (time, state.timeOn) >= Q  } 

      function elapsedTime (now: bits, origin: bits): (res: bits)
         // Function satisfies specification because of mod arithmetic.
            ensures now >= origin ==> res == (now - origin)
            ensures now < origin ==>                     // 0 is T as bits
               res == (now + T - origin)
      {  (now - origin) % T  }    // implemented as bit-vector subtraction  

      function interval (time: bits): bits
      {  time / I  }                           // implemented as time >> i

      lemma greater_time_on_preserves_valid_event_time(gs_old : GhostState, gs_new : GhostState, evs : seq<LocEvent>)
         requires gs_new.natTimeOn >= gs_old.natTimeOn 
         requires (forall i | 0 <= i < |evs| :: valid_event_time(gs_old, evs[i]))
         ensures (forall i | 0 <= i < |evs| :: valid_event_time(gs_new, evs[i]))

      method Dispatch(cur_ev : LocEvent)
      {  
         if 
            case cur_ev.e.ProcessPacket? => {var forwarded := processPacket(cur_ev);}
            case cur_ev.e.SetFiltering? => {setFiltering(cur_ev);}

            // "ghost" events that are just for verification. 
            // not sure if these should be events, or just functions 
            // that assert the proper start and end conditions
            case cur_ev.e.SimulatedClockTick? => {simulatedClockTick(cur_ev);}            
            case cur_ev.e.HardwareFailure? => {hardwareFailure(cur_ev);}
      }
      
      method simulatedClockTick(cur_ev : LocEvent)
         requires cur_ev.e.SimulatedClockTick?
         requires correct_internal_time(cur_ev)
         requires valid_interarrivals([cur_ev] + queue)
         requires valid_event_times(this.gstate, [cur_ev] + this.queue)    
         requires pre_dispatch(this.state, gstate, cur_ev, this.queue, this.lastNatTime)

         // requires (natTime + 1) < gstate.natTimeOn + T

         ensures valid_interarrivals([cur_ev] + queue)
         ensures valid_event_times(this.gstate, [cur_ev] + this.queue)    
         ensures post_dispatch(state, gstate, queue, natTime)
      {
         // NOTE: we don't want to propagate the (natTime + 1) < gstate.natTimeOn + T
         //       constraint all the way through the program, so in this method, we just 
         //       verify that the invariant holds when that constraint is true
         if (natTime + 1 < gstate.natTimeOn + T) {
            var timePlus : bits := (time + 1) % T;
            var natTimePlus : nat := natTime + 1;
            assert timePlus == natTimePlus % T;
            assert state.filtering ==>                                 // invariant
               (natTime >=gstate.natTimeOn + Q as nat <==> (time -state.timeOn) % T >= Q);
            // show time-sensitive invariant holds after clock tick
            assert state.filtering ==>
                  (protecting (state, gstate, natTimePlus) <==> protectImplmnt (state, timePlus));   
            var foo := 1; // for some reason my vscode doesn't like an if with only ghost ops in it
         }
         recirc_invariant_tail(state, [cur_ev] + queue);
      }


      method hardwareFailure (cur_ev : LocEvent)           // ghost
         modifies this.state, this`gstate, this`queue
         requires correct_internal_time(cur_ev)
         requires valid_interarrivals([cur_ev] + queue)
         requires valid_event_times(this.gstate, [cur_ev] + this.queue)    
         requires pre_dispatch(this.state, gstate, cur_ev, this.queue, this.lastNatTime)

         // requires (natTime + 1) < gstate.natTimeOn + T

         ensures valid_interarrivals([cur_ev] + queue)
         ensures valid_event_times(this.gstate, [cur_ev] + this.queue)    
         ensures post_dispatch(state, gstate, queue, natTime)
      { 
         // recirc_invariant_tail(state, [cur_ev] + queue);
         state.filtering, state.recircPending := false, false;
         // NOTE: we assume that the hardware failure "event" carries 
         //       the timestamp at which the hardware "starts back up"
         //       This lets us reuse all the existing post conditions.
         //       (i.e., set timeOn and associated variables to the 
         //       time of the event rather than 0)
         state.lastIntv, state.count, state.timeOn, state.actualTimeOn := 0, 0, time, natTime;
         state.requestSet := {};
         gstate := gstate.(natTimeOn := natTime);  
         queue := [];
      }

      method setFiltering(cur_ev : LocEvent) 
         requires cur_ev.e.SetFiltering?
         modifies this.state, this`gstate

         requires correct_internal_time(cur_ev)
         requires valid_interarrivals([cur_ev] + queue)
         requires valid_event_times(this.gstate, [cur_ev] + this.queue)    
         requires pre_dispatch(this.state, gstate, cur_ev, this.queue, this.lastNatTime)

         ensures valid_interarrivals([cur_ev] + queue)
         ensures valid_event_times(this.gstate, [cur_ev] + this.queue)    
         ensures post_dispatch(state, gstate, queue, natTime)
      {
         // goal: prove that no other events in the queue can be setFiltering events. 
         // steps: 
         // 1. this is a setFiltering event.
         // 2. by "LemmaCountSumGtFilterSeq" the current and pending events queue ([e] + event_queue) has at least one setFiltering.
         // 3. by "inter_event_invariant", state.recircPending is true
         // 4. by "inter_event_invariant", there is EXACTLY one setFiltering in ([e] + event_queue)
         // 5. by dafny's automated solver, since [e] is a setFiltering, there are no setFiltering events in event_queue
         assert recircInvariant(state, [cur_ev]+queue);
         assert count_f([cur_ev], is_setfiltering) == 1;
         LemmaCountSumGtFilterSeq([cur_ev], queue, is_setfiltering);
         assert count_f([cur_ev]+queue, is_setfiltering) >= 1;
         assert (state.recircPending);

         var tmpFiltering : bool := cur_ev.e.on;               // get memop . . . .
         state.filtering :=  cur_ev.e.on;                             // with update memop
         if tmpFiltering {
            var tmpTimeOn : bits := state.timeOn;           // get memop . . . .
            state.timeOn := time;                           // with update memop
            state.actualTimeOn := natTime;                              // ghost

            // state.natTimeOn := natTime;                                 // ghost
            // update the immutable ghost state
            ghost var new_gstate := gstate.(natTimeOn := natTime);
            valid_event_times_implies_forall(gstate, [cur_ev]+this.queue);
            greater_time_on_preserves_valid_event_time(gstate, new_gstate, [cur_ev] + this.queue);
            forall_implies_valid_event_times(new_gstate, [cur_ev] + this.queue);
            gstate := new_gstate;

            state.recircPending := false;                        // update memop
         }
         else {
            state.recircPending := false;                        // update memop
            state.requestSet := {};                              // update memop
            // we need to prove that there are no setfiltering events in the queue

         }
      }

      method processPacket (cur_ev : LocEvent) returns (forwarded: bool)  
         modifies this.state, this`queue, this`gstate
         requires cur_ev.e.ProcessPacket? 
         // same requirements as dispatch
         requires correct_internal_time(cur_ev)
         requires valid_interarrivals([cur_ev] + queue)
         requires valid_event_times(this.gstate, [cur_ev] + this.queue)    
         requires pre_dispatch(this.state, gstate, cur_ev, this.queue, this.lastNatTime)

         /* pasting in requirements from old version -- TODO: what's necessary? */
         requires natTime >= lastNatTime
         requires natTime - lastNatTime < T - I

         ensures valid_interarrivals([cur_ev] + queue)
         ensures valid_event_times(this.gstate, [cur_ev] + this.queue)    
         ensures post_dispatch(state, gstate, queue, natTime)


         ensures (  ! cur_ev.e.dnsRequest && protecting (state, gstate, natTime)
               && (! (cur_ev.e.uniqueSig in state.preFilterSet))      )
               ==> ! forwarded   // Adaptive Protection, needs exactness

         ensures ! forwarded ==>                           // Harmlessness
               (  ! cur_ev.e.dnsRequest && (! (cur_ev.e.uniqueSig in state.preFilterSet))  )
      {
         // 
         if (cur_ev.e.dnsRequest) {
            forwarded := processRequest(cur_ev);
         } else {
            state.preFilterSet := state.requestSet;                           // ghost  
            forwarded := processReply(cur_ev);
         }
      }

      method processRequest(cur_ev : LocEvent) returns (forwarded: bool)
         modifies this.state, this`queue
         requires cur_ev.e.ProcessPacket? 
         // same requirements as dispatch
         requires correct_internal_time(cur_ev)
         requires valid_interarrivals([cur_ev] + queue)
         requires valid_event_times(this.gstate, [cur_ev] + this.queue)    
         requires pre_dispatch(this.state, this.gstate, cur_ev, this.queue, this.lastNatTime)
         /* pasting in requirements from old version -- TODO: what's necessary? */
         requires cur_ev.e.dnsRequest
         requires natTime >= lastNatTime
         requires natTime - lastNatTime < T - I
         
         ensures forwarded
         ensures valid_interarrivals([cur_ev] + queue)
         ensures valid_event_times(this.gstate, [cur_ev] + this.queue)    
         ensures post_dispatch(state, gstate, queue, natTime)
      {
         recirc_invariant_tail(state, [cur_ev]+queue);
         var tmpFiltering : bool := state.filtering;                // get memop
         if (tmpFiltering) {  
            bloomFilterInsert (cur_ev.e.uniqueSig);                        // memop
            state.requestSet := state.requestSet + { cur_ev.e.uniqueSig }; }           // ghost
         forwarded := true;
      }

      method processReply (cur_ev : LocEvent) returns (forwarded: bool)
         modifies this.state, this`queue, this`gstate
         requires cur_ev.e.ProcessPacket? 
         // same requirements as dispatch
         requires correct_internal_time(cur_ev)
         requires valid_interarrivals([cur_ev] + queue)
         requires valid_event_times(this.gstate, [cur_ev] + this.queue)    
         requires pre_dispatch(this.state, gstate, cur_ev, this.queue, this.lastNatTime)
         /* pasting in requirements from old version -- TODO: what's necessary? */
         requires !cur_ev.e.dnsRequest
         requires natTime >= lastNatTime
         requires natTime - lastNatTime < T - I
         requires natTime < gstate.natTimeOn + T   
         requires state.preFilterSet == state.requestSet
      

         ensures valid_interarrivals([cur_ev] + queue)
         ensures valid_event_times(this.gstate, [cur_ev] + this.queue)    
         ensures post_dispatch(state, gstate, queue, natTime)
         ensures (  ! cur_ev.e.dnsRequest && protecting (state, gstate, natTime)
               && (! (cur_ev.e.uniqueSig in state.preFilterSet))      )
               ==> ! forwarded   // Adaptive Protection, needs exactness
         ensures ! forwarded ==>                           // Harmlessness
                  (  ! cur_ev.e.dnsRequest && (! (cur_ev.e.uniqueSig in state.preFilterSet))  )

      {
         recirc_invariant_tail(state, [cur_ev]+queue);

         // Changes to measurement state:
         // Increment or reset count.  If there is an interval with no reply
         // packets, then the count will not be reset for that interval.
         // However, the count will never include replies from more than one
         // interval.
         var oldCount : nat := 0;
         var tmpCount : nat;
         var tmpLastIntv : bits := state.lastIntv;          // get memop . . . .
         state.lastIntv := interval (time);                 // with update memop 
         if interval (time) != tmpLastIntv {
            oldCount := state.count;
            tmpCount := 1;                            // get memop . . . .
            state.count := 1;                               // with update memop
         }
         else {  
            tmpCount := state.count + 1;                    // get memop . . . .
            state.count := state.count + 1;                       // with update memop
         }

         // Changes to filtering state:
         // Filtering is turned on as soon as count reaches upper threshold.
         // (Note that in !filtering test of count, it should never exceed U, 
         // so this is defensive programming.)  There is no declarative 
         // specification of turning filtering off,  so we make the code as 
         // readable as possible.
         var tmpFiltering : bool := state.filtering;                // get memop
         var tmpTimeOn : bits;
         var tmpRecircPending : bool;

         if ! tmpFiltering {
            if tmpCount >= U {
               // time to turn filtering on
               tmpRecircPending := state.recircPending;     // get memop . . . .
               state.recircPending := true;                 // with update memop
               if ! tmpRecircPending {
                  // IF LUCID
                  // generate SetFiltering (true);
                  // ELSE
                  // state.recircSwitch := true;                           // ghost
                  // TODO: refactor so that generate doesn't need these extra arguments

                  ghost var old_queue := queue;
                  var t:nat := next_generate_time(natTime, queue);
                  var new_event := LocEvent(SetFiltering(true), t%T, t);
                  generate_time_is_valid(cur_ev, queue);
                  Generate(cur_ev, SetFiltering(true), t);
                  // assert queue == old_queue + [new_event];
                  // assert count_f(old_queue, is_setfiltering_true) == 0;
                  // assert count_f([new_event], is_setfiltering_true) == 1;
                  LemmaCountSumFilterSeq(old_queue, [new_event], is_setfiltering_true);
                  // assert count_f(old_queue, is_setfiltering) == 0;
                  // assert count_f([new_event], is_setfiltering) == 1;
                  LemmaCountSumFilterSeq(old_queue, [new_event], is_setfiltering);
                  // assert count_f(queue, is_setfiltering_true) == 1;
                  // assert count_f(queue, is_setfiltering) == 1;
                  assert post_dispatch(state, gstate, queue, natTime);  // to accelerate verification                
                  // FI
               }  // else recirc already generated, do nothing
            }  
         }
         else { // filtering
            if oldCount != 0 { // interval boundary crossed
               if oldCount >= L {
                  if elapsedTime (time, state.timeOn) >= Q        // get memop .
                     {  tmpTimeOn := (time - Q) % T;  }     // . . . . . .
                  else { tmpTimeOn := state.timeOn; }             // . . . . . .
                  if elapsedTime (time, state.timeOn) >= Q {      // with update
                     assert natTime - Q >= 0;
                     state.timeOn := (time - Q) % T;              // memop 

                     var new_gstate := gstate.(natTimeOn := natTime - Q); // ghost
                     // gstate.natTimeOn := natTime - Q;                    
                     // we need to prove that the event times are still valid with 
                     // respect to the updated ghost state. To do that, we convert 
                     // the sequence predicate into a into a forall predicate 
                     // using a lemma in the template, 
                     // apply a lemma in the user program to each item, 
                     // and finally convert from a forall predicate 
                     // back into a sequence predicate with another template lemma.
                     valid_event_times_implies_forall(gstate, [cur_ev]+this.queue);
                     greater_time_on_preserves_valid_event_time(gstate, new_gstate, [cur_ev] + this.queue);
                     forall_implies_valid_event_times(new_gstate, [cur_ev] + this.queue);
                     gstate := new_gstate;
                     assert valid_event_times(this.gstate, [cur_ev] + this.queue);
                     recirc_invariant_tail(state, [cur_ev]+queue); // we just need to know that 
                     // if the recirc invariant held on the input, it holds on the output
                     assert post_dispatch(state, gstate, queue, natTime);         // to accelerate verification          
                     // assert post_dispatch(state, gstate, queue, natTime);
                  }
                  else {
                     recirc_invariant_tail(state, [cur_ev]+queue);
                  }
                  assert post_dispatch(state, gstate, queue, natTime);
               }
               else { // oldCount < L
                  tmpTimeOn := state.timeOn;                        // get memop
                  if elapsedTime (time, tmpTimeOn) >= QRoff {
                     // time to turn filtering off
                     tmpRecircPending := state.recircPending;//get memop . . . .
                     state.recircPending := true;           // with update memop
                     if ! tmpRecircPending {
                        // IF LUCID
                        // generate SetFiltering (false);
                        // ELSE
                        // state.recircSwitch := false;                    // ghost
                        // TODO: refactor so that generate doesn't need these extra arguments
                        ghost var old_queue := queue;
                        var t:nat := next_generate_time(natTime, queue);
                        var new_event := LocEvent(SetFiltering(false), t%T, t);
                        generate_time_is_valid(cur_ev, queue);
                        Generate(cur_ev, SetFiltering(false), next_generate_time(natTime, queue));                        
                        LemmaCountSumFilterSeq(old_queue, [new_event], is_setfiltering_false);
                        LemmaCountSumFilterSeq(old_queue, [new_event], is_setfiltering);
                        assert post_dispatch(state, gstate, queue, natTime);            // to accelerate verification       
                        // FI
                     }  // else recirc already generated, do nothing
                  }
               }
            } // end boundary-crossing case
            else {  tmpTimeOn := state.timeOn; }                    // get memop
         } // end filtering case
         assert post_dispatch(state, gstate, queue, natTime);

         // Filtering decision:
         // if filtering off, it won't matter that timeOn not read
         if tmpFiltering && elapsedTime (time, tmpTimeOn) >= Q {
            assert post_dispatch(state, gstate, queue, natTime);
            forwarded := filter(cur_ev);
            assert post_dispatch(state, gstate, queue, natTime);
         }
         else {  forwarded := true; }
         assert post_dispatch(state, gstate, queue, natTime);
      }

      method filter
         (cur_ev : LocEvent) 
                                                returns (forwarded: bool)  
         requires cur_ev.e.ProcessPacket?
         modifies this.state
         requires ! cur_ev.e.dnsRequest
         requires protectImplmnt (state, time)
         requires state.preFilterSet == state.requestSet
         requires parameterConstraints ()
         requires stateInvariant (state, gstate, time, natTime)
         requires post_dispatch(state, gstate, queue, natTime)

         ensures protectImplmnt (state, time)
         ensures (   (! (cur_ev.e.uniqueSig in state.preFilterSet))      )
               ==> ! forwarded   // Adaptive Protection, needs exactness
         ensures ! forwarded ==>                           // Harmlessness
               (  ! cur_ev.e.dnsRequest && (! (cur_ev.e.uniqueSig in state.preFilterSet))  )
         ensures stateInvariant (state, gstate, time, natTime)
         ensures post_dispatch(state, gstate, queue, natTime)
      {
         forwarded := bloomFilterQuery (cur_ev.e.uniqueSig);               // memop
         if forwarded {      // if positive is false, has no effect; ghost
            state.requestSet := state.requestSet - { cur_ev.e.uniqueSig };             // ghost
         }
      }

      method {:extern} bloomFilterInsert (uniqueSig: nat)

      method {:extern} bloomFilterQuery (uniqueSig: nat)
                                                   returns (inSet: bool)
      // No false negatives:
      // A sliding-window Bloom filter automatically deletes set members
      // shortly after a guaranteed tenancy W.  You might imagine that
      // this would be a source of false negatives.  However, it is not,
      // because a request never needs to stay in the set longer than Q,
      // where Q <= W.
         ensures uniqueSig in state.requestSet ==> inSet
      // No false positives:
      // Not true, but used to prove Adaptive Protection as a sanity
      // check.  (If deleted, Adaptive Protection cannot be proved.)  This
      // property can be false for two reasons: (1) it is the nature of
      // a Bloom filter to yield false positives sometimes; (2) in a
      // sliding-window Bloom filter, there are no timely deletions, just
      // scheduled timeouts which can be delayed.
         ensures ! (uniqueSig in state.requestSet) ==> (! inSet)


   /****  recirculation invariant and friends ****/
      function is_setfiltering (e : LocEvent) : bool 
      {
         match e.e {
            case SetFiltering(_) => true
            case _ => false
         }
      }
      function is_setfiltering_true (e : LocEvent) : bool 
      {
         match e.e {
            case SetFiltering(true) => true
            case _ => false
         }
      }
      function is_setfiltering_false (e : LocEvent) : bool 
      {
         match e.e {
            case SetFiltering(false) => true
            case _ => false
         }
      }

      lemma recirc_invariant_tail(state : State, events : seq<LocEvent>)
         requires recircInvariant(state, events)
         ensures |events| > 0 ==> recircInvariant(state, events[1..])


      ghost predicate recircInvariant (state : State, events : seq<LocEvent>) 
      reads state 
      // this invariant is about the relationship between the recircPending 
      // semaphore and the setFiltering events that may appear in the queue. 
      // There are two parts to the invariant: 
      // 1. when recircPending is true, the invariant asserts that there's only one setFiltering event in the queue
      // 2. when there are setFiltering events in the queue, the invariant asserts that recircPending is true
      // I _think_ that both "directions" are necessary to verify the program. (But, this could probably be cleaned up a lot.)
      {
         (
            if state.recircPending
            then 
            (
               (|events| > 0)
               &&
               count_f(events, is_setfiltering) == 1
               &&
               (
                  if state.filtering
                  then
                  (
                     count_f(events, is_setfiltering_false) == 1
                  )
                  else
                  (
                     count_f(events, is_setfiltering_true) == 1
                  )
               )
            )
            else 
            (
               count_f(events, is_setfiltering) == 0
               && 
               count_f(events, is_setfiltering_false) == 0
               && 
               count_f(events, is_setfiltering_true) == 0
            )
         )
         &&
         (
            if ( count_f(events, is_setfiltering) >0)
            then (
               state.recircPending == true
            )
            else (
               state.recircPending == false
            )
         )
      }


    // helpers to reason about event queue contents
    function count_f<T>(ls : seq<T>, f : (T -> bool)) : int
    {
        if (ls == []) then 0
        else (
            if (f(ls[0]))
            then (1 + count_f(ls[1..], f))
            else (count_f(ls[1..], f))
        )
    }
    lemma LemmaCountSumFilterSeq<T>(a : seq<T>, b : seq<T>, f : (T -> bool))
    ensures count_f(a + b, f) == count_f(a, f) + count_f(b, f)

    lemma LemmaCountSumGtFilterSeq<T>(a : seq<T>, b : seq<T>, f : (T -> bool))
    ensures count_f(a + b, f) > count_f(a, f)
    ensures count_f(a + b, f) > count_f(b, f)





    }



}