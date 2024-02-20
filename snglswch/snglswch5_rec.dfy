include "lucid_base_rec.dfy"

module LucidProg refines LucidBase {

    datatype Event = 
      // | NOOP()
      | ProcessPacket(dnsRequest: bool, uniqueSig: nat)
      
      // | SetFiltering(on : bool)
      // | ProcessPacket(dnsRequest: bool, uniqueSig: nat)
      // | PacketOut() // optional.

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
      ghost var natTimeOn : nat
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
            // does not establish inter-event invariant
            // because the event queue is empty
      {     
             state := new State();   
             queue := [];
      } 

      predicate parameterConstraints ()      // from problem domain, ghost  
      {  I > 0 && QRoff > Q > 0  && W >= Q  }


      ghost predicate valid_next_event(cur : LocEvent, next : LocEvent)
      {
         next.natTime - cur.natTime < T - I
      }


      /*** the inter-event invariant ***/
      ghost predicate inter_event_invariant(s : State, cur_ev : LocEvent, ev_queue : seq<LocEvent>, lastNatTime : nat)
      {
         var natTime := cur_ev.natTime;
         parameterConstraints()
         && (natTime - lastNatTime < T - I)
         // && (natTime < s.actualTimeOn + T) // TODO: I don't understand this predicate.
         // Seems like there are some input sequences that are valid, 
         // but for which this would not hold
      }
      ghost predicate stateInvariant (state : State, es : seq<Event>, time : bits, natTime : nat, lastNatTime : nat)         // ghost
         reads state
      {
         // CHANGE: lastNatTime --> natTime because it doesn't make sense in 
         //         SetFiltering (it sets natTimeOn to the current time, not the last time)
              (  state.natTimeOn <= natTime  ) 
         && (  state.timeOn == state.natTimeOn % T  )
         && (  state.natTimeOn >= state.actualTimeOn  )
         && (  state.filtering ==> 
                  (protecting (state, natTime) <==> protectImplmnt (state, time))  )
         && (  ! state.filtering ==> state.requestSet == {}  )
         // && (  state.recircPending ==> (state.filtering == ! state.recircSwitch)  )
         // && recircInvariant(state, es) // TODO: add recircInvariant back in
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

      method Dispatch(cur_ev : LocEvent)
      {
         assert cur_ev.natTime == this.natTime;
         assert this.time == (this.natTime % T);
         if
            // case cur_ev.e.NOOP? => {}
            case cur_ev.e.ProcessPacket? => {
               var fwd := processPacket(cur_ev);
            }
      }

      method processPacket (cur_ev : LocEvent) returns (forwarded: bool)  
         modifies this.state, this`queue
         requires cur_ev.e.ProcessPacket? 
         requires valid_event_queue([cur_ev] + this.queue)
         requires inter_event_invariant(state, cur_ev, this.queue, this.lastNatTime)
         requires cur_ev.natTime == this.natTime

         /* pasting in requirements from old version -- TODO: what's necessary? */
         requires time == natTime % T
         requires natTime >= lastNatTime
         requires natTime - lastNatTime < T - I

         // ensures (  ! cur_ev.e.dnsRequest && protecting (state, natTime)
         //       && (! (cur_ev.e.uniqueSig in state.preFilterSet))      )
         //       ==> ! forwarded   // Adaptive Protection, needs exactness
         // ensures ! forwarded ==>                           // Harmlessness
         //       (  ! e.dnsRequest && (! (e.uniqueSig in state.preFilterSet))  )
         ensures post_dispatch(state, queue, natTime)
         // requires natTime < state.actualTimeOn + T // See note in inter-event invariant
         ensures  valid_event_queue([cur_ev] + this.queue)
      {
         forwarded := false;
         // 
         valid_event_queue_implies_valid_head([cur_ev] + this.queue);
         assert (
            |queue| > 0 ==> 
               (inter_event_invariant(state, queue[0], queue[1..], natTime))
         );
         
      }
    }



}