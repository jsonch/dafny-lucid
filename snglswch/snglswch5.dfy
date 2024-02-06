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
      ghost var recircSwitch : bool 

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



      ghost predicate stateInvariant (state : State)         // ghost
         reads this`natTime, this`lastNatTime, this`time
         reads state
      {
              (  state.natTimeOn <= natTime  ) // CHANGE: lastNatTime --> natTime
         // && (  state.timeOn == state.natTimeOn % T  )
         && (  state.natTimeOn >= state.actualTimeOn  )
         && (  state.filtering ==> 
                  (protecting (state, natTime) <==> protectImplmnt (state, time))  )
         && (  ! state.filtering ==> state.requestSet == {}  )
         && (  state.recircPending ==> (state.filtering == ! state.recircSwitch)  )
         // TODO: the last part of this invariant, with the recirculation ghost variable, needs to be replaced with queue predicates
         // state.recircSwitch means "there is a recirc event in the queue"
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
         parameterConstraints() && stateInvariant(s) 
         && (natTime - lastNatTime < T - I)
         && (natTime < s.actualTimeOn + T)

      }

      method Dispatch(e : Event) 
      {
         if 
            case e.SetFiltering? => SetFiltering(e.on);
            case e.ProcessPacket? => {
               var fwd := ProcessPacket(e.dnsRequest, e.uniqueSig);

            }
            case e.PacketOut? => PacketOut();

      }
      method PacketOut() {}

      method ProcessPacket
         (dnsRequest: bool, uniqueSig: nat)
                                                returns (forwarded: bool)   
         modifies this.state
         // requires time == natTime % T
         // Two packets can have the same timestamp.
            // requires natTime >= lastNatTime
         // There must be a packet between any two interval rollovers, so
         // that interval boundaries can be detected.  
            // requires natTime - lastNatTime < T - I
         // Constraint to make attack time spans measurable.
            // requires natTime < state.actualTimeOn + T
         requires parameterConstraints ()
         requires stateInvariant (state)
         requires inter_event_invariant(state, event_queue)
         ensures (  ! dnsRequest && protecting (state, natTime)
               && (! (uniqueSig in state.preFilterSet))      )
               ==> ! forwarded   // Adaptive Protection, needs exactness
         ensures ! forwarded ==>                           // Harmlessness
               (  ! dnsRequest && (! (uniqueSig in state.preFilterSet))  )
         ensures stateInvariant (state)
         ensures inter_event_invariant(state, event_queue)
      {
         if (dnsRequest) {  
            forwarded := 
               processRequest (dnsRequest, uniqueSig); 
         }
         else {
            state.preFilterSet := state.requestSet;                           // ghost  
            forwarded := 
            processReply (dnsRequest, uniqueSig); 
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
         requires stateInvariant (state)
         requires inter_event_invariant(state, event_queue)

         ensures dnsRequest
         ensures forwarded 
         ensures stateInvariant (state)
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
         requires stateInvariant (state)
         requires inter_event_invariant(state, event_queue)

         ensures ! dnsRequest
         ensures (  ! dnsRequest && protecting (state, natTime)
               && (! (uniqueSig in state.preFilterSet))    )
               ==> ! forwarded   // Adaptive Protection, needs exactness
         ensures ! forwarded ==>                           // Harmlessness
               (  ! dnsRequest && (! (uniqueSig in state.preFilterSet))  )
         ensures stateInvariant (state)
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
                  state.recircSwitch := true;                           // ghost
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
                        state.recircSwitch := false;                    // ghost
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
         requires stateInvariant (state)
         requires inter_event_invariant(state, event_queue)
         ensures protectImplmnt (state, time)
         ensures (   (! (uniqueSig in state.preFilterSet))      )
               ==> ! forwarded   // Adaptive Protection, needs exactness
         ensures ! forwarded ==>                           // Harmlessness
               (  ! dnsRequest && (! (uniqueSig in state.preFilterSet))  )
         ensures stateInvariant (state)
         ensures inter_event_invariant(state, event_queue)
      {
         forwarded := bloomFilterQuery (uniqueSig);               // memop
         if forwarded {      // if positive is false, has no effect; ghost
            state.requestSet := state.requestSet - { uniqueSig };             // ghost
         }
      }

      method SetFiltering (on: bool)
         modifies this.state
         // requires time_invariant()
         // requires on == state.recircSwitch      // parameter gets ghost variable
         // requires time == natTime % T
         // Two packets can have the same timestamp.
         // requires natTime >= lastNatTime
         // requires state.recircPending
         requires parameterConstraints ()
         requires stateInvariant (state)
         requires inter_event_invariant(state, event_queue)
         ensures ! state.recircPending
         // ensures time_invariant()
         ensures stateInvariant(state)
         ensures inter_event_invariant(state, event_queue)
      {

         var tmpFiltering : bool := on;               // get memop . . . .
         state.filtering := on;                             // with update memop
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
         }
      }


      method HardwareFailure ()           // ghost
         modifies this.state // NEW
         modifies this
         requires parameterConstraints ()
         requires stateInvariant (state)
         ensures stateInvariant (state)
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