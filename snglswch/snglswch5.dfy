include "lucid_base.dfy"

// status: 
// - the invariants looks correct and verification succeeds
// 
// - the verification for the event queue needs to be updated, for setfilter events
// - the time invariant may be wrong, and isn't used

// - need to review the clock tick and hardware failure methods
// - want to simplify some of the predicates to not take a state argument
//    (if its a builtin anyway)
// - need to use Arrays and the Array memop
// - need to add "Send" and change the "forward" conditions to "send" conditions


module LucidProg refines LucidBase {

    datatype Event = 
      | SetFiltering(on : bool)
      | ProcessPacket(dnsRequest: bool, uniqueSig: nat)
      | PacketOut()

    class State ... {
      // Address State 
      var lastIntv : bits    // an interval, so first 8-i bits always zero
      var count : nat                           // counter for DNS replies
      var filtering : bool          // turns adaptive filtering on and off
      var timeOn : bits      // implementation of time filtering turned on
      var recircPending : bool          // a "semaphore" for recirculation
      ghost var requestSet : set<nat>   // pending requests, for filtering

      ghost var actualTimeOn : nat
      ghost var natTimeOn : nat

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
            ensures natTimeOn == 0
            ensures requestSet == {}
      {
         filtering, recircPending := false, false;
         lastIntv, count, timeOn := 0, 0, 0;
         actualTimeOn, natTimeOn := 0, 0;
         requestSet := {};
      }

    }
   // Parameters
   const T : nat := 256
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
            ensures (this.event_queue == [])
            // ensures time_invariant()
            ensures inter_event_invariant(state, event_queue)
      {     
             state := new State();   
             event_queue := [];
             natTime, lastNatTime := 1, 0;
             time := 1;
      } 
   
   

      predicate parameterConstraints ()      // from problem domain, ghost  
         // reads this
      {  I > 0 && QRoff > Q > 0  && W >= Q  }

      function is_setfiltering (e : Event) : bool 
      {
         match e {
            case SetFiltering(_) => true
            case _ => false
         }
      }
      function is_setfiltering_true (e : Event) : bool 
      {
         match e {
            case SetFiltering(true) => true
            case _ => false
         }
      }
      function is_setfiltering_false (e : Event) : bool 
      {
         match e {
            case SetFiltering(false) => true
            case _ => false
         }
      }


      ghost predicate recircInvariant (state : State, events : seq<Event>) 
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

      ghost predicate stateInvariant (state : State, es : seq<Event>)         // ghost
         reads this`natTime, this`lastNatTime, this`time
         reads state
      {
              (  state.natTimeOn <= natTime  ) // CHANGE: lastNatTime --> natTime
         // && (  state.timeOn == state.natTimeOn % T  )
         && (  state.natTimeOn >= state.actualTimeOn  )
         && (  state.filtering ==> 
                  (protecting (state, natTime) <==> protectImplmnt (state, time))  )
         && (  ! state.filtering ==> state.requestSet == {}  )
         // && (  state.recircPending ==> (state.filtering == ! state.recircSwitch)  )
         && recircInvariant(state, es)
      }

      ghost predicate protecting (state : State, natTime : nat)  
      reads state                        // ghost
      {  state.filtering && (natTime >= state.natTimeOn + Q as nat)  }

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

      ghost predicate inter_event_invariant(s : State, es : seq<Event>)
      {
         parameterConstraints() && stateInvariant(s, es) 
         && (natTime - lastNatTime < T - I)
         && (natTime < s.actualTimeOn + T)

      }

      method Dispatch(e : Event) 
      {
         if 
            case e.SetFiltering? => setFiltering(e);
            case e.ProcessPacket? => {
               var fwd := ProcessPacket(e);

            }
            case e.PacketOut? => {}

      }

      method ProcessPacket
         (e : Event)
                                                returns (forwarded: bool)  
         requires e.ProcessPacket? 
         modifies this.state
         modifies this`event_queue
         // requires time == natTime % T
         // Two packets can have the same timestamp.
            // requires natTime >= lastNatTime
         // There must be a packet between any two interval rollovers, so
         // that interval boundaries can be detected.  
            // requires natTime - lastNatTime < T - I
         // Constraint to make attack time spans measurable.
            // requires natTime < state.actualTimeOn + T
         requires parameterConstraints ()
         requires stateInvariant (state, event_queue)
         requires inter_event_invariant(state, [e] + event_queue)
         ensures (  ! e.dnsRequest && protecting (state, natTime)
               && (! (e.uniqueSig in state.preFilterSet))      )
               ==> ! forwarded   // Adaptive Protection, needs exactness
         ensures ! forwarded ==>                           // Harmlessness
               (  ! e.dnsRequest && (! (e.uniqueSig in state.preFilterSet))  )
         ensures stateInvariant (state, event_queue)
         ensures inter_event_invariant(state, event_queue)
      {
         if (e.dnsRequest) {  
            forwarded := 
               processRequest (e.dnsRequest, e.uniqueSig); 
         }
         else {
            state.preFilterSet := state.requestSet;                           // ghost  
            forwarded := 
            processReply (e.dnsRequest, e.uniqueSig); 
         }
      }

      method processRequest
         (dnsRequest: bool, uniqueSig: nat)
                                                returns (forwarded: bool)
         modifies this.state         
         // requires time == natTime % T
         // Two packets can have the same timestamp.
            // requires natTime >= lastNatTime
         requires dnsRequest
         requires parameterConstraints ()
         requires inter_event_invariant(state, event_queue)

         ensures dnsRequest
         ensures forwarded 
         ensures inter_event_invariant(state, event_queue)

      {
         var tmpFiltering : bool := state.filtering;                // get memop
         if (tmpFiltering) {  
            bloomFilterInsert (uniqueSig);                        // memop
            state.requestSet := state.requestSet + { uniqueSig }; }           // ghost
         forwarded := true;
      }

      method processReply 
         (dnsRequest: bool, uniqueSig: nat)
                                                returns (forwarded: bool)
         modifies this.state
         modifies this`event_queue
         // requires time == natTime % T
         // Two packets can have the same timestamp.
            // requires natTime >= lastNatTime
         // There must be a packet between any two interval rollovers, so
         // that interval boundaries can be detected.  
            // requires (natTime - lastNatTime) < (T - I)
         // Constraint to make attack time spans measurable.
            // requires natTime < state.actualTimeOn + T
         requires ! dnsRequest
         requires state.preFilterSet == state.requestSet
         requires parameterConstraints ()
         requires inter_event_invariant(state, event_queue)

         ensures ! dnsRequest
         ensures (  ! dnsRequest && protecting (state, natTime)
               && (! (uniqueSig in state.preFilterSet))    )
               ==> ! forwarded   // Adaptive Protection, needs exactness
         ensures ! forwarded ==>                           // Harmlessness
               (  ! dnsRequest && (! (uniqueSig in state.preFilterSet))  )
         ensures inter_event_invariant(state, event_queue)

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
                  ghost var old_event_queue := event_queue;
                  Generate(SetFiltering(true));
                  // NOTE:
                  // proof: after generating the event, there is only 1 setFiltering in the queue.
                  // steps: 
                  // 1. the event queue prior to the generate (old_event_queue) has no set filtering events. 
                  // 2. the sequence of a single set filtering event has 1 set filtering event. 
                  // 3. by "LemmaCountSumFilterSeq", old_event_queue+[SetFiltering(true)] has 1 set filtering event.
                  // 4. the new event queue is equal to old_event_queue+[SetFiltering(true)]
                  // 5. thus the new event queue has 1 set filtering event. 
                  // NOTE: all you should _really_ need to do here is apply the lemma
                  // assert count_f(old_event_queue, is_setfiltering) == 0;
                  // assert count_f([SetFiltering(true)], is_setfiltering) == 1;
                  LemmaCountSumFilterSeq(old_event_queue, [SetFiltering(true)], is_setfiltering);
                  // assert count_f(old_event_queue + [SetFiltering(true)], is_setfiltering) == 1;
                  // assert event_queue == old_event_queue + [SetFiltering(true)];
                  assert count_f(event_queue, is_setfiltering) == 1;
                  // NOTE: we also have to prove that there is only 1 setFiltering(true) event in the queue, 
                  //       because of how the invariant is structured, using the same mechanism.
                  LemmaCountSumFilterSeq(old_event_queue, [SetFiltering(true)], is_setfiltering_true);
                  assert count_f(event_queue, is_setfiltering_true) == 1;

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
                     state.timeOn := (time - Q) % T;              // memop 
                    state.natTimeOn := natTime - Q;                    // ghost
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
                        ghost var old_event_queue := event_queue;
                        Generate(SetFiltering(false));
                        // NOTE: Lemma + old_event_queue proves that there is only 1 
                        // setfiltering in the queue after the generate. Same 
                        // steps as the earlier case where we generate SetFiltering(true)
                        LemmaCountSumFilterSeq(old_event_queue, [SetFiltering(false)], is_setfiltering);
                        assert count_f(event_queue, is_setfiltering) == 1;
                        LemmaCountSumFilterSeq(old_event_queue, [SetFiltering(false)], is_setfiltering_false);
                        assert count_f(event_queue, is_setfiltering_false) == 1;
                        // FI
                     }  // else recirc already generated, do nothing
                  }
               }  
            } // end boundary-crossing case
            else {  tmpTimeOn := state.timeOn; }                    // get memop
         } // end filtering case

      // Filtering decision:
      // if filtering off, it won't matter that timeOn not read
         if tmpFiltering && elapsedTime (time, tmpTimeOn) >= Q {
            forwarded := filter (dnsRequest, uniqueSig);
         }
         else {  forwarded := true; }

      }


      method filter
         (dnsRequest: bool, uniqueSig: nat) 
                                                returns (forwarded: bool)  
         modifies this.state
         requires ! dnsRequest
         requires protectImplmnt (state, time)
         requires state.preFilterSet == state.requestSet
         requires parameterConstraints ()
         requires inter_event_invariant(state, event_queue)
         ensures protectImplmnt (state, time)
         ensures (   (! (uniqueSig in state.preFilterSet))      )
               ==> ! forwarded   // Adaptive Protection, needs exactness
         ensures ! forwarded ==>                           // Harmlessness
               (  ! dnsRequest && (! (uniqueSig in state.preFilterSet))  )
         ensures inter_event_invariant(state, event_queue)
      {
         forwarded := bloomFilterQuery (uniqueSig);               // memop
         if forwarded {      // if positive is false, has no effect; ghost
            state.requestSet := state.requestSet - { uniqueSig };             // ghost
         }
      }

      lemma LemmaFilterHead<T>(es : seq<T>, f : T -> bool)
         requires es != []
         requires count_f(es, f) == 1
         requires count_f([es[0]], f) == 1
         ensures count_f(es[1..], f) == 0

      method setFiltering (e : Event)
         requires e.SetFiltering?
         modifies this.state
         // requires time_invariant()
         // requires on == state.recircSwitch      // parameter gets ghost variable
         // requires time == natTime % T
         // Two packets can have the same timestamp.
         // requires natTime >= lastNatTime
         // requires state.recircPending
         requires parameterConstraints ()
         requires inter_event_invariant(state, [e] + event_queue)
         ensures ! state.recircPending
         // ensures time_invariant()
         ensures inter_event_invariant(state, event_queue)
      {
         // goal: prove that no other events in the queue can be setFiltering events. 
         // steps: 
         // 1. this is a setFiltering event.
         // 2. by "LemmaCountSumGtFilterSeq" the current and pending events queue ([e] + event_queue) has at least one setFiltering.
         // 3. by "inter_event_invariant", state.recircPending is true
         // 4. by "inter_event_invariant", there is EXACTLY one setFiltering in ([e] + event_queue)
         // 5. by dafny's automated solver, since [e] is a setFiltering, there are no setFiltering events in event_queue
         assert count_f([e], is_setfiltering) == 1; // 
         LemmaCountSumGtFilterSeq([e], event_queue, is_setfiltering);
         assert count_f([e]+event_queue, is_setfiltering) >= 1; // so by the lemma, the "current and pending events" queue 
         assert (state.recircPending);

         var tmpFiltering : bool := e.on;               // get memop . . . .
         state.filtering :=  e.on;                             // with update memop
         if tmpFiltering {
            var tmpTimeOn : bits := state.timeOn;           // get memop . . . .
            state.timeOn := time;                           // with update memop
            state.actualTimeOn := natTime;                              // ghost
            state.natTimeOn := natTime;                                 // ghost
            state.recircPending := false;                        // update memop
         }
         else {
            state.recircPending := false;                        // update memop
            state.requestSet := {};                              // update memop
            // we need to prove that there are no setfiltering events in the queue

         }
      }


      method HardwareFailure ()           // ghost
         modifies this.state // NEW
         modifies this
         requires parameterConstraints ()
      { 
         state.filtering, state.recircPending := false, false;
         state.lastIntv, state.count, state.timeOn, state.actualTimeOn, state.natTimeOn := 0, 0, 0, 0,0;
         state.actualTimeOn, state.natTimeOn := 0, 0;                         // ghost
         lastNatTime := natTime;                                  // ghost
         state.requestSet := {};                                        // ghost
      }

   //    method SimulatedClockTick ()         // ghost
   //       modifies state
   //       requires time == natTime % T
   //       requires natTime > lastNatTime
   //       // Constraint to make attack time spans measurable.
   //          requires natTime < state.actualTimeOn + T
   //       // This extra assumption leaves room for natTimePlus.  It is
   //       // necessary, which shows that the constraint to make time spans
   //       // measurable is necessary.
   //          requires (natTime + 1) < state.actualTimeOn + T
   //       requires parameterConstraints ()
   //       requires stateInvariant (state)
   //       requires inter_event_invariant(state, event_queue)
   //       ensures stateInvariant (state)
   // {
   //       var timePlus : bits := (time + 1) % T;
   //       var natTimePlus : nat := natTime + 1;
   //       assert timePlus == natTimePlus % T;
   //       assert state.filtering ==>                                 // invariant
   //          (natTime >=state.natTimeOn + Q as nat <==> (time -state.timeOn) % T >= Q);
   //       // show time-sensitive invariant holds after clock tick
   //       assert state.filtering ==>
   //             (protecting (state, natTimePlus) <==> protectImplmnt (state, timePlus));   
   //    }

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