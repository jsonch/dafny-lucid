include "lucid_base_rec.dfy"

module LucidProg refines LucidBase {

    datatype Event = 
      | NOOP()
      | ProcessPacket(dnsRequest: bool, uniqueSig: nat)
      | SetFiltering(on : bool)
      
      // | SetFiltering(on : bool)
      // | ProcessPacket(dnsRequest: bool, uniqueSig: nat)
      // | PacketOut() // optional.

   
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
      // ghost var natTimeOn : nat
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



      ghost predicate valid_next_event(cur : LocEvent, next : LocEvent)
      {
         (next.natTime - cur.natTime < T - I)
      }


      ghost function valid_event_time(gs : GhostState, ev : LocEvent) : bool 
      {
         ev.natTime < gs.natTimeOn + T
      }

      lemma greater_time_on_preserves_valid_event_time(gs_old : GhostState, gs_new : GhostState, evs : seq<LocEvent>)
         requires gs_new.natTimeOn >= gs_old.natTimeOn 
         requires (forall i | 0 <= i < |evs| :: valid_event_time(gs_old, evs[i]))
         ensures (forall i | 0 <= i < |evs| :: valid_event_time(gs_new, evs[i]))





      /*** the inter-event invariant ***/
      ghost predicate pre_dispatch(s : State, gs : GhostState, cur_ev : LocEvent, ev_queue : seq<LocEvent>, lastNatTime : nat)
      {
      
         var natTime := cur_ev.natTime;
         parameterConstraints()
         && (natTime - lastNatTime < T - I)
         && stateInvariant(s, gs, ev_queue, cur_ev.time, cur_ev.natTime, lastNatTime)
         // && (natTime < s.actualTimeOn + T)
         // Left off here. This is really weird requirement. 
         // the event's timestamp has to be within a rollover of 
         // actualTimeOn.
         // What if filtering never gets turned on?
         // Or, what if filtering turns on and never shuts off? 
         // In either case, I think there's a "hard" limit on the time that the events may have. 
         // they have to be within T of when filtering turned on.

         // Its not an inter-arrival limit. 
         // And it depends on the state. 
         // LEFT OFF HERE:
         // So lets try to work that in tomorrow. A "valid event" constraint that 
         // just forces all the events in the queue to have less than the current state's actualTimeOn + T, 
         // (maybe only if the current state says filtering is on?)
         // I think that will be okay-ish. 
         // The discuss doubts with Pamela
      }
      ghost predicate stateInvariant (state : State, gstate : GhostState, es : seq<LocEvent>, time : bits, natTime : nat, lastNatTime : nat)         // ghost
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
         // && (  state.recircPending ==> (state.filtering == ! state.recircSwitch)  )
         // && recircInvariant(state, es) // TODO: add recircInvariant back in
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





      method Dispatch(cur_ev : LocEvent)
      {  
         if 
            case cur_ev.e.NOOP? => {}
            case cur_ev.e.ProcessPacket? => {var forwarded := processPacket(cur_ev);}
            case cur_ev.e.SetFiltering? => {}
      }

      method setFiltering(cur_ev : LocEvent) 
         requires cur_ev.e.SetFiltering?
         modifies this.state, this`gstate

         requires correct_internal_time(cur_ev)
         requires valid_timestamps([cur_ev] + queue)
         requires ordered_timestamps([cur_ev] + queue)
         requires valid_event_times(this.gstate, [cur_ev] + this.queue)    
         requires valid_next_events([cur_ev] + this.queue)
         requires pre_dispatch(this.state, gstate, cur_ev, this.queue, this.lastNatTime)

         ensures valid_timestamps([cur_ev] + queue)
         ensures ordered_timestamps([cur_ev] + queue)
         ensures valid_event_times(this.gstate, [cur_ev] + this.queue)    
         ensures valid_next_events([cur_ev] + this.queue) // NOTE: this is the hard one!         
         ensures post_dispatch(state, gstate, queue, natTime)
      {
         var tmpFiltering : bool := cur_ev.e.on;               // get memop . . . .
         state.filtering :=  cur_ev.e.on;                             // with update memop
         if tmpFiltering {
            var tmpTimeOn : bits := state.timeOn;           // get memop . . . .
            assert time == natTime % T;
            state.timeOn := time;                           // with update memop
            state.actualTimeOn := natTime;                              // ghost
            ghost var new_gstate := gstate.(natTimeOn := natTime);
            assert new_gstate.natTimeOn == state.actualTimeOn;
            assert state.timeOn == new_gstate.natTimeOn % T;
            valid_event_times_implies_forall(gstate, [cur_ev]+this.queue);
            greater_time_on_preserves_valid_event_time(gstate, new_gstate, [cur_ev] + this.queue);
            forall_implies_valid_event_times(new_gstate, [cur_ev] + this.queue);
            gstate := new_gstate;
            assert (
               |queue| > 0 ==> 
               (
                  pre_dispatch(state, gstate, queue[0], queue[1..], cur_ev.natTime)
               )
            );


            // state.natTimeOn := natTime;                                 // ghost
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
         requires valid_timestamps([cur_ev] + queue)
         requires ordered_timestamps([cur_ev] + queue)
         requires valid_event_times(this.gstate, [cur_ev] + this.queue)    
         requires valid_next_events([cur_ev] + this.queue)
         requires pre_dispatch(this.state, gstate, cur_ev, this.queue, this.lastNatTime)

         /* pasting in requirements from old version -- TODO: what's necessary? */
         requires natTime >= lastNatTime
         requires natTime - lastNatTime < T - I

         ensures valid_timestamps([cur_ev] + queue)
         ensures ordered_timestamps([cur_ev] + queue)
         ensures valid_event_times(this.gstate, [cur_ev] + this.queue)    
         ensures valid_next_events([cur_ev] + this.queue) // NOTE: this is the hard one!         
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
         requires valid_timestamps([cur_ev] + queue)
         requires ordered_timestamps([cur_ev] + queue)
         requires valid_event_times(this.gstate, [cur_ev] + this.queue)    
         requires valid_next_events([cur_ev] + this.queue)
         requires pre_dispatch(this.state, this.gstate, cur_ev, this.queue, this.lastNatTime)
         /* pasting in requirements from old version -- TODO: what's necessary? */
         requires cur_ev.e.dnsRequest
         requires natTime >= lastNatTime
         requires natTime - lastNatTime < T - I
         
         ensures forwarded
         ensures valid_timestamps([cur_ev] + queue)
         ensures ordered_timestamps([cur_ev] + queue)
         ensures valid_event_times(this.gstate, [cur_ev] + this.queue)    
         ensures valid_next_events([cur_ev] + this.queue) // NOTE: this is the hard one!         
         ensures post_dispatch(state, gstate, queue, natTime)



      {
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
         requires valid_timestamps([cur_ev] + queue)
         requires ordered_timestamps([cur_ev] + queue)
         requires valid_event_times(this.gstate, [cur_ev] + this.queue)    
         requires valid_next_events([cur_ev] + this.queue)
         requires pre_dispatch(this.state, gstate, cur_ev, this.queue, this.lastNatTime)
         /* pasting in requirements from old version -- TODO: what's necessary? */
         requires !cur_ev.e.dnsRequest
         requires natTime >= lastNatTime
         requires natTime - lastNatTime < T - I
         requires natTime < gstate.natTimeOn + T   
         requires state.preFilterSet == state.requestSet
      

         ensures valid_timestamps([cur_ev] + queue)
         ensures ordered_timestamps([cur_ev] + queue)
         ensures valid_event_times(this.gstate, [cur_ev] + this.queue)    
         ensures valid_next_events([cur_ev] + this.queue) // NOTE: this is the hard one!         
         ensures post_dispatch(state, gstate, queue, natTime)
         ensures (  ! cur_ev.e.dnsRequest && protecting (state, gstate, natTime)
               && (! (cur_ev.e.uniqueSig in state.preFilterSet))      )
               ==> ! forwarded   // Adaptive Protection, needs exactness
         ensures ! forwarded ==>                           // Harmlessness
                  (  ! cur_ev.e.dnsRequest && (! (cur_ev.e.uniqueSig in state.preFilterSet))  )

      {

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
                  generate_time_is_valid(cur_ev, queue);
                  Generate(cur_ev, SetFiltering(true), next_generate_time(natTime, queue));
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
                     assert post_dispatch(state, gstate, queue, natTime);         // to accelerate verification          
                     // assert post_dispatch(state, gstate, queue, natTime);

                  }
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
                        generate_time_is_valid(cur_ev, queue);
                        Generate(cur_ev, SetFiltering(false), next_generate_time(natTime, queue));                        
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
            forwarded := filter(cur_ev);
         }
         else {  forwarded := true; }
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
         requires stateInvariant (state, gstate, queue, time, natTime, lastNatTime)
         ensures protectImplmnt (state, time)
         ensures (   (! (cur_ev.e.uniqueSig in state.preFilterSet))      )
               ==> ! forwarded   // Adaptive Protection, needs exactness
         ensures ! forwarded ==>                           // Harmlessness
               (  ! cur_ev.e.dnsRequest && (! (cur_ev.e.uniqueSig in state.preFilterSet))  )
         ensures stateInvariant (state, gstate, queue, time, natTime, lastNatTime)
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


    }



}