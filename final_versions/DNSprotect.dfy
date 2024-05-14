/*-------------------------------------------------------------------------
SINGLE-SWITCH ALGORITHM AND ITS SPECIFICATION (verified)

This is the algorithm to be implemented, in its most abstract and readable
form.

Ghost variables are history variables; they are used for domain knowledge 
and for specification, and need not be implemented.  As the model is 
refined, some of the current real variables will become ghost variables, 
as they are replaced in the implementation by more realistic or efficient 
real variables.

In the same vein, ghost methods, predicates, and functions are used for 
domain knowledge and specification, and are not implemented.

I would also like to call simulatedHardwareFailure a ghost method, but
it updates real variables, so Dafny does not allow this labeling.
-------------------------------------------------------------------------*/
include "lucidBase.dfy"

module LucidProg refines LucidBase {

   datatype Event =
    | ProcessPacket (dnsRequest: bool, uniqueSig: nat)
    | SimulatedClockTick ()
    | SimulatedHardwareFailure ()

class Program ... {

   // Parameters
   const I : nat                                         // interval length
   const Q : nat                               // maximum DNS response time
   const QRoff : nat    // Q plus observation window for stopping filtering
   const U : nat                                   // upper count threshold
   const L : nat                                   // lower count threshold

   // Address State
   var currentIntv : nat                            // the current interval
   var count : nat                               // counter for DNS replies
   var filtering : bool              // turns adaptive filtering on and off
   var timeOn : nat               // effective time filtering was turned on
   ghost var actualTimeOn : nat          // actual time filtering turned on
   var requestSet : set <nat>            // pending requests, for filtering
   ghost var preFilterSet : set <nat>        // requestSet, before deletion

   ghost predicate parameterConstraints ()           // from problem domain
      {  I > 0 && QRoff > Q > 0  }

   constructor ()
      ensures validQueue (queue)
      ensures parameterConstraints ()
      ensures stateInvariant (0)
   {
      queue := [];
      filtering := false;
      currentIntv, count, timeOn, actualTimeOn := 0, 0, 0, 0;
      requestSet := {};
   }

   ghost predicate protecting (time: nat) 
      reads this
   {  filtering && (time >= actualTimeOn + Q)  }

   predicate protectImplmnt (time: nat) 
      reads this
   {  filtering && (time >= timeOn + Q)  }

   ghost predicate stateInvariant (time: nat)
   {  (actualTimeOn <= timeOn)
   && (timeOn <= time)  
   && ((timeOn > actualTimeOn) ==> (time >= timeOn + Q))
   && (filtering ==> (protecting (time) <==> protectImplmnt (time)))
   && (! filtering ==> requestSet == {})
   } 

   method dispatch (e: TimedEvent) 
   {
      if
         case e.event.ProcessPacket? => 
         {  var forwarded := processPacket 
               (e.time, e.event.dnsRequest, e.event.uniqueSig);  }
         case e.event.SimulatedClockTick? => 
            {  simulatedClockTick (e.time);  }
         case e.event.SimulatedHardwareFailure? => 
            {  simulatedHardwareFailure (e.time);  }
   }

   method processPacket (time: nat, dnsRequest: bool, uniqueSig: nat) 
                                                  returns (forwarded: bool)
      modifies this
      requires parameterConstraints ()
      requires stateInvariant (time)
      ensures (  ! dnsRequest && protecting (time)
              && ! (uniqueSig in preFilterSet)   ) 
              ==> ! forwarded                        // Adaptive Protection
      ensures ! forwarded ==>                               // Harmlessness
              (  ! dnsRequest && ! (uniqueSig in preFilterSet)  )
      ensures stateInvariant (time)
   {
      if (dnsRequest) {  
         forwarded := processRequest (time, uniqueSig); }
      else { 
         preFilterSet := requestSet;                        // ghost update
         forwarded := processReply (time, uniqueSig); 
      }   
   }

   method processRequest (time: nat, uniqueSig: nat)
                                                  returns (forwarded: bool)
      modifies this
      requires parameterConstraints ()
      requires stateInvariant (time)
      ensures forwarded
      ensures stateInvariant (time)
   {
      if (filtering) {  requestSet := requestSet + { uniqueSig }; }
      forwarded := true;
   }

   function interval (time: nat): nat
      reads this
      requires parameterConstraints ()
   {  time / I  }

   method processReply (time: nat, uniqueSig: nat) returns (forwarded:bool)
      modifies this
      requires preFilterSet == requestSet
      requires parameterConstraints ()
      requires stateInvariant (time)
      ensures (  protecting (time) && ! (uniqueSig in preFilterSet)   )
              ==> ! forwarded                        // Adaptive Protection
      ensures ! forwarded ==>                               // Harmlessness
                 ! (uniqueSig in preFilterSet)
      ensures stateInvariant (time)
   {
   // Changes to measurement state:
   // If an interval boundary has been crossed, save the count in
   // oldCount, and reset the counter to 1 (for this reply).  Otherwise
   // simply increment the count.
   // If there is an interval with no reply packets, then the count
   // will not be reset for that interval.  However, the count will
   // never include replies from more than one interval.
      var oldCount : nat := 0;
      if interval (time) != currentIntv {
         oldCount := count;
         count := 1;
         currentIntv := interval (time);
      }
      else {  count := count + 1; }

   // Changes to filtering state:
   // Turning filtering on:
   // Filtering is turned on as soon as count reaches upper threshold.
   // (Note that in !filtering test of count, it should never exceed U, so
   // this is defensive programming.)
      if ! filtering {
         if count >= U {
            filtering := true;
            timeOn := time;
            actualTimeOn := time;                           // ghost update
            }
         }
   // Turning filtering off:
   // Consider the case that once protecting begins, the count in each
   // interval is less than L.  Then timeOn == actualTimeOn, and as soon as
   // QRoff time has elapsed, filtering can be turned off.  Now consider
   // the case in which protecting has begun, and the count in an interval
   // is high.  In this case timeOn is reset to what it would be if 
   // protecting had just become true.  Now there is no chance to turn 
   // filtering off until time Qroff elapses with no high counts.
      else { // filtering
         if ! protectImplmnt (time) { }         // too early to do anything
         else { // time Q has elapsed, we are now protecting
            if oldCount != 0 { // interval boundary crossed
               if (  oldCount < L
                  && (time - timeOn) >= QRoff
                  )
                  {  filtering := false;
                     requestSet := {};
                  }
               else { // checking if count is still high
                  if oldCount >= L { // count is too high, reset the
                                     // filtering clock back to the
                                     // time when protection begins
                     timeOn := time - Q;
                  }
               // count is low, just waiting for Woff to elapse
               }
            }  // end of case where interval boundary crossed
         }  // end of protecting case
      }  // end of filtering case

   // Filtering decision:
      if protectImplmnt (time) {
         forwarded := filter (time, uniqueSig);
      }
      else {  forwarded := true; }
   }

   method filter (time: nat, uniqueSig: nat) returns (forwarded: bool)
      modifies this
      requires protectImplmnt (time)
      requires preFilterSet == requestSet
      requires parameterConstraints ()
      requires stateInvariant (time)
      ensures     ! (uniqueSig in preFilterSet)
              ==> ! forwarded                        // Adaptive Protection
      ensures ! forwarded ==>                               // Harmlessness
                 ! (uniqueSig in preFilterSet)
      ensures stateInvariant (time)
   {
      if uniqueSig in requestSet {
         requestSet := requestSet - { uniqueSig };
         forwarded := true;
      }
      else {  forwarded := false; }
   }

   method simulatedHardwareFailure (time: nat)                     // ghost
      modifies this
      requires parameterConstraints ()
      requires stateInvariant (time)
      ensures stateInvariant (time)
   {
      filtering := false;
      currentIntv, count, timeOn, actualTimeOn := 0, 0, 0, 0;
      requestSet := {};
   }

   ghost method simulatedClockTick (time: nat)
      modifies this
      requires parameterConstraints ()
      requires stateInvariant (time)
      ensures stateInvariant (time)
   {
      var timePlus : nat := time + 1;
      assert stateInvariant (timePlus);
   }
}
}
