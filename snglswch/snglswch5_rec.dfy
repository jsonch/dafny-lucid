include "lucid_base_rec.dfy"

module LucidProg refines LucidBase {

   datatype Event = 
      // | NOOP()
      | ProcessPacket(dnsRequest: bool, uniqueSig: nat)
      | SetFiltering(on : bool)

      // | SetFiltering(on : bool)
      // | ProcessPacket(dnsRequest: bool, uniqueSig: nat)
      // | PacketOut() // optional.


   class GState ... {
      ghost var requestSet : set<nat>   // pending requests, for filtering
      // ghost variables for reasoning about timeOn
      ghost var actualTimeOn : nat 
      ghost var natTimeOn : nat    
      ghost var preFilterSet : set<nat> // requestSet, before any deletion
      // ghost var recircSwitch : bool 

      ghost constructor ()
            ensures actualTimeOn == 0
            ensures natTimeOn == 0
            ensures requestSet == {}
      {
         actualTimeOn, natTimeOn := 0, 0;
         requestSet := {};
      }
   }

   class State ... {
      // Address State 
      var lastIntv : bits    // an interval, so first 8-i bits always zero
      var count : nat                           // counter for DNS replies
      var filtering : bool          // turns adaptive filtering on and off
      var timeOn : bits      // implementation of time filtering turned on
      var recircPending : bool          // a "semaphore" for recirculation



      constructor ()
            ensures (this.filtering == false)
            ensures (this.recircPending == false)
            ensures (fresh(this))
            ensures filtering == false
            ensures recircPending == false
            ensures lastIntv == 0
            ensures count == 0
            ensures timeOn == 0
      {
         filtering, recircPending := false, false;
         lastIntv, count, timeOn := 0, 0, 0;
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
            ensures (fresh(gState))
            // does not establish inter-event invariant
            // because the event queue is empty
      {     
             state := new State();   
             gState := new GState();
             queue := [];
      } 



      predicate parameterConstraints ()      // from problem domain, ghost  
      {  I > 0 && QRoff > Q > 0  && W >= Q  }


      ghost predicate valid_next_event(cur : LocEvent, next : LocEvent)
      {
         (next.natTime - cur.natTime < T - I)
      }


      /*** the inter-event invariant ***/
      ghost predicate inter_event_invariant(s : State, gs : GState, cur_ev : LocEvent, ev_queue : seq<LocEvent>, lastNatTime : nat)
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
      ghost predicate stateInvariant (state : State, gstate : GState, es : seq<LocEvent>, time : bits, natTime : nat, lastNatTime : nat)         // ghost
         reads state, gstate
      {
         // CHANGE: lastNatTime --> natTime because it doesn't make sense in 
         //         SetFiltering (it sets natTimeOn to the current time, not the last time)
              (  gstate.natTimeOn <= natTime  ) 
         && (  state.timeOn == gstate.natTimeOn % T  )
         && (  gstate.natTimeOn >= gstate.actualTimeOn  )
         && (  state.filtering ==> 
                  (protecting (state, gstate, natTime) <==> protectImplmnt (state, time))  )
         && (  ! state.filtering ==> gstate.requestSet == {}  )
         // && (  state.recircPending ==> (state.filtering == ! state.recircSwitch)  )
         // && recircInvariant(state, es) // TODO: add recircInvariant back in
      }

      ghost predicate protecting (state : State, gstate : GState, natTime : nat)  
      reads state, gstate
                              // ghost
      {  state.filtering && (natTime >= gstate.natTimeOn + Q as nat)  }

      predicate protectImplmnt (state : State, time: bits)
      reads state
      // protecting is a specification, using history variables.  This
      // is its implementation, which cannot use history variables.
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

      }




      method processPacket (cur_ev : LocEvent) returns (forwarded: bool)  
         modifies this.state, this`queue, this.gState
         requires cur_ev.e.ProcessPacket? 
         requires valid_event_queue([cur_ev] + this.queue)
         requires inter_event_invariant(state, gState, cur_ev, this.queue, this.lastNatTime)
         requires correct_internal_time(cur_ev)

         /* pasting in requirements from old version -- TODO: what's necessary? */
         requires natTime >= lastNatTime
         requires natTime - lastNatTime < T - I
         

         ensures (  ! cur_ev.e.dnsRequest && protecting (state, gState, natTime)
               && (! (cur_ev.e.uniqueSig in gState.preFilterSet))      )
               ==> ! forwarded   // Adaptive Protection, needs exactness

         // ensures ! forwarded ==>                           // Harmlessness
         //       (  ! e.dnsRequest && (! (e.uniqueSig in state.preFilterSet))  )
         // ensures post_dispatch(state, queue, natTime)
         // requires natTime < state.actualTimeOn + T // See note in inter-event invariant
         // ensures  valid_event_queue([cur_ev] + this.queue)
      {

         // 
         if (cur_ev.e.dnsRequest) {
            forwarded := false;
         } else {
            /* copy-pasted from processReply */

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
                     Generate(cur_ev, SetFiltering(true), next_generate_time(natTime, queue));                        
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
                        
                     /*
                        BREAKS HERE -- need state invariant!
                     */
                        assert natTime - Q >= 0;
                        state.timeOn := (time - Q) % T;              // memop 
                        gState.natTimeOn := natTime - Q;                    // ghost
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
                           Generate(cur_ev, SetFiltering(false), next_generate_time(natTime, queue));                        
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
               forwarded := false;//   filter (dnsRequest, uniqueSig);
            }
            else {  forwarded := true; }
         } // end !dnsRequest (processResponse body)

               // assert (prot_clause == prot_impl_clause);

               // assert (protecting (state, queue[0].natTime) <==> protectImplmnt (state, queue[0].time));
            // }
         

         // assert (
         //    |queue| > 0 ==> 
         //       (inter_event_invariant(state, queue[0], queue[1..], natTime))
         // );
         // assert post_dispatch (state, this.queue, cur_ev.natTime);
         
      }
    }



}