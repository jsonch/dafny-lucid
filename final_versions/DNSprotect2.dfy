/*-------------------------------------------------------------------------
SINGLE-SWITCH ALGORITHM AND ITS SPECIFICATION (verified)

This version is a refinement of the first version in two ways.  First, 
because timestamps (and all other variables) are implemented by bit 
vectors, they are bounded natural numbers.  Note that the only "nat" 
variables now are ghost variables.  Because nanosecond timestamps grow very
fast, verification requires an operating assumption that bounds the time 
spans to be measured.

Second, the request set is implemented by a sliding-window Bloom filter, so
requestSet becomes a ghost variable.  The real program uses external
methods, represented here by their specifications only.  A sliding-window 
Bloom filter written in P4 has been verified, so we know it is possible to
provide correct code for the external methods.  The Bloom filter gives 
approximate results, so the specifications of the external methods are 
weaker than the reference behavior of requestSet.  Verification shows 
exactly which behaviors we can and cannot guarantee, and why.

Cumulative rules for translation to Lucid:
1) Drop the declaration of any variable declared "ghost."
2) Drop any statement updating a ghost variable (labeled by comment).
3) Drop any method, predicate or function declared ghost or labeled ghost
   (by comment).
4) Fill in the bodies of extern methods with executable and correct code.
5) Translate the "dispatch" method into the Lucid equivalent.
-------------------------------------------------------------------------*/
include "lucidBase2.dfy"

module LucidProg refines LucidBase {
   
   type counter = x : int | 0 <= x < 1048576         // limit must exceed U

   datatype Event =
    | ProcessPacket (dnsRequest: bool, uniqueSig: nat)
    | SimulatedClockTick ()
    | SimulatedHardwareFailure ()

class Program ... {

   // Parameters
   const I : nat := 16             // interval length, < T and a power of 2
   const Q : bits                              // maximum DNS response time
   const QRoff : bits   // Q plus observation window for stopping filtering
   const W : nat                   // Bloom-filter window size, >= Q as nat
   const U : counter                               // upper count threshold
   const L : counter                               // lower count threshold

   // Address State
   var currentIntv : bits   // current interval, so first 4 bits are zeroes
   var count : counter                           // counter for DNS replies
   var filtering : bool              // turns adaptive filtering on and off
   ghost var timeOn : nat         // effective time filtering was turned on
   var timestampOn : bits                       // implementation of timeOn
   ghost var actualTimeOn : nat          // actual time filtering turned on
   var requestSet : set <nat>            // pending requests, for filtering
   ghost var preFilterSet : set <nat>        // requestSet, before deletion

   ghost predicate parameterConstraints ()           // from problem domain
      {  I > 0 && QRoff > Q > 0 && W >= Q && U < 1048576  }

   constructor ()
   {
      queue := [];
      lastTime := 0;
      filtering := false;
      currentIntv, count, timeOn, timestampOn, actualTimeOn := 0,0,0,0,0;
      requestSet := {};
   }

   ghost predicate protecting (time: nat) 
      reads this
   {  filtering && (time - actualTimeOn) >= Q as nat  }

   predicate protectImplmnt (timestamp: bits) 
      reads this
   {  filtering && elapsedTime (timestamp, timestampOn) >= Q  }

   function elapsedTime (now: bits, origin: bits): (res: bits)
      reads this
      // Function satisfies specification because of mod arithmetic.
         ensures now >= origin ==> res == (now - origin)
         ensures now < origin ==>                         // 0 is T as bits
            res == (now + T - origin)
   {  (now - origin) % T  }        // implemented as bit-vector subtraction

   ghost predicate stateInvariant (time: nat, timestamp: bits)
   {  (  timestampOn == timeOn % T  )
   && (  actualTimeOn <= timeOn  )
   && (  timeOn <= time  )
   && (  (timeOn > actualTimeOn) ==> (time >= timeOn + Q as nat)  )
   && (filtering ==> (protecting (time) <==> protectImplmnt (timestamp)))
   && (  ! filtering ==> requestSet == {}  )
   } 

   ghost predicate operatingAssumptions (e: TimedEvent) 
   {
      if      e.event.ProcessPacket?
      then       (filtering ==> e.time < actualTimeOn + T) 
              && (e.time - lastTime < T - I              ) 
      else if e.event.SimulatedClockTick?
      then    (filtering ==> (e.time + 1) < actualTimeOn + T) 
      else true
   }

   method dispatch (e: TimedEvent) 
   // Events generated randomly by simulateArrival can be ignored without
   // loss of validity, if they do not satisfy the operating assumptions.
   { 
      if {
         case e.event.ProcessPacket? =>
         {  var forwarded := processPacket 
              (e.time, e.timestamp, e.event.dnsRequest, e.event.uniqueSig);
         }
         case e.event.SimulatedClockTick? => 
            {  simulatedClockTick (e.time, e.timestamp);  }
         case e.event.SimulatedHardwareFailure? => 
            {  simulatedHardwareFailure (e.time, e.timestamp);  }
      }
   } 

   method processPacket (time: nat, timestamp: bits, dnsRequest: bool, 
                                  uniqueSig: nat) returns (forwarded: bool)
      modifies this
      requires timestamp == time % T
      // There must be a packet between any two interval rollovers, so
      // that interval boundaries can be detected.  Unfortunately, the
      // specification is not strong enough to cause verification to fail
      // without this operating assumption.
         requires time - lastTime < T - I
      // Note that there is no mechanism for dealing with counter overflow.
      // Below is the operating assumption to make attack time spans 
      // measurable.
         requires filtering ==> time < actualTimeOn + T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures (  ! dnsRequest && protecting (time)
              && ! (uniqueSig in preFilterSet)   ) 
              ==> ! forwarded                     // Adaptive Protection,
                                                  // needs exact requestSet
      ensures ! forwarded ==>                               // Harmlessness
              (  ! dnsRequest && ! (uniqueSig in preFilterSet)  )
      ensures stateInvariant (time, timestamp)
   {
      if (dnsRequest) {  
         forwarded := processRequest (time, timestamp, uniqueSig); }
      else { 
         preFilterSet := requestSet;                        // ghost update
         forwarded := processReply (time, timestamp, uniqueSig); 
      }   
   }

   method processRequest (time: nat, timestamp: bits, uniqueSig: nat)
                                                  returns (forwarded: bool)
      modifies this
      requires timestamp == time % T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures forwarded
      ensures stateInvariant (time, timestamp)
   {
      if (filtering) {  requestSet := requestSet + { uniqueSig }; }
      forwarded := true;
   }

   function interval (timestamp: bits): bits
      reads this
      requires parameterConstraints ()
   {  timestamp / I  }                    // implemented with a right-shift

   method processReply (time: nat, timestamp: bits, uniqueSig: nat) 
                                                  returns (forwarded: bool)
      modifies this
      requires preFilterSet == requestSet
      requires timestamp == time % T
      // There must be a packet between any two interval rollovers, so
      // that interval boundaries can be detected.  Unfortunately, the
      // specification is not strong enough to cause verification to fail
      // without this operating assumption.
         requires time - lastTime < T - I
      // Operating assumption to make attack time spans measurable.
         requires filtering ==> time < actualTimeOn + T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures (  protecting (time) && ! (uniqueSig in preFilterSet)   )
              ==> ! forwarded                     // Adaptive Protection,
                                                  // needs exact requestSet
      ensures ! forwarded ==>                               // Harmlessness
                 ! (uniqueSig in preFilterSet)
      ensures stateInvariant (time, timestamp)
   {
   // Changes to measurement state:
   // If an interval boundary has been crossed, save the count in
   // oldCount, and reset the counter to 1 (for this reply).  Otherwise
   // simply increment the count.
   // If there is an interval with no reply packets, then the count
   // will not be reset for that interval.  However, the count will
   // never include replies from more than one interval.
      var oldCount : nat := 0;
      if interval (timestamp) != currentIntv {
         oldCount := count;
         count := 1;
         currentIntv := interval (timestamp);
      }
      else {  if count < U { count := count + 1; }  }

   // Changes to filtering state:
   // Turning filtering on:
   // Filtering is turned on as soon as count reaches upper threshold.
   // (Note that in !filtering test of count, it should never exceed U, so
   // this is defensive programming.)
      if ! filtering {
         if count >= U {
            filtering := true;
            timestampOn := timestamp;
            timeOn := time;                                 // ghost update
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
         if ! protectImplmnt (timestamp) { }    // too early to do anything
         else { // time Q has elapsed, we are now protecting
            if oldCount != 0 { // interval boundary crossed
               if (  oldCount < L
                  && elapsedTime (timestamp, timestampOn) >= QRoff
                  )
                  {  filtering := false;
                     requestSet := {};
                  }
               else { // checking if count is still high
                  if oldCount >= L { // count is too high, reset the
                                     // filtering clock back to the
                                     // time when protection begins
                     timestampOn := (timestamp - Q) % T;
                     timeOn := time - Q;                    // ghost update
                  }
               // count is low, just waiting for Woff to elapse
               }
            }  // end of case where interval boundary crossed
         }  // end of protecting case
      }  // end of filtering case

   // Filtering decision:
      if protectImplmnt (timestamp) {
         forwarded := filter (time, timestamp, uniqueSig);
      }
      else {  forwarded := true; }
   }

   method filter (time: nat, timestamp: bits, uniqueSig: nat) 
                                                  returns (forwarded: bool)
      modifies this
      requires timestamp == time % T
      requires protectImplmnt (timestamp)
      requires preFilterSet == requestSet
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures     ! (uniqueSig in preFilterSet)
              ==> ! forwarded                     // Adaptive Protection,
                                                  // needs exact requestSet
      ensures ! forwarded ==>                               // Harmlessness
                 ! (uniqueSig in preFilterSet)
      ensures stateInvariant (time, timestamp)
   {
      if uniqueSig in requestSet {
         requestSet := requestSet - { uniqueSig };
         forwarded := true;
      }
      else {  forwarded := false; }
   }

   method simulatedHardwareFailure (time: nat, timestamp: bits)    // ghost
      modifies this
      requires timestamp == time % T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures stateInvariant (time, timestamp)
   {
      filtering := false;
      currentIntv, count, timeOn, timestampOn, actualTimeOn := 0,0,0,0,0;
      requestSet := {};
   }

   ghost method simulatedClockTick (time: nat, timestamp: bits)
      modifies this
      requires timestamp == time % T
      // Operating assumption to make attack time spans measurable.  
      // Without the "+ 1", the method cannot be verified.
         requires filtering ==> (time + 1) < actualTimeOn + T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures stateInvariant (time, timestamp)
   {
      var timePlus : nat := time + 1;
      var timestampPlus : bits := (timestamp + 1) % T;
      assert stateInvariant (timePlus, timestampPlus);
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
      ensures uniqueSig in requestSet ==> inSet
   // No false positives:
   // Not true, but used to prove Adaptive Protection as a sanity
   // check.  (If deleted, Adaptive Protection cannot be proved.)  This
   // property can be false for two reasons: (1) it is the nature of
   // a Bloom filter to yield false positives sometimes; (2) in a
   // sliding-window Bloom filter, there are no timely deletions, just
   // scheduled timeouts which can be delayed.
      ensures ! (uniqueSig in requestSet) ==> (! inSet)
}
}
