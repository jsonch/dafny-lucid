/*-------------------------------------------------------------------------
SINGLE-SWITCH ALGORITHM AND ITS SPECIFICATION (verified)

This version refines the third version by replacing Atomics with Arrays.
The changes are:
1) The state variables are now arrays, and there is a new parameter "A"
   that specifies the length of the arrays:
      var currentIntv : Array <bits>              // current interval
      var count : Array <counter>          // counter for DNS replies
      var filtering : Array <bool>   // turns adaptive filtering on and off
      var timestampOn : Array <bits>            // implementation of timeOn
      var recircPending : Array <bool>   // a "semaphore" for recirculation
2) The ghost variables that hold flow state are now sequences: 
      ghost var timeOn : seq<nat>         // effective time filtering was turned on
      ghost var actualTimeOn : seq<nat>          // actual time filtering turned on
      ghost var requestSet : seq<set<nat>>      // pending requests, for filtering
      ghost var preFilterSet : seq<set<nat>>        // requestSet, before deletion
2) A new predicate, "arraySizes", ensures that the arrays are the correct
   size. The predicate is declared in the base module and defined in the
   program module. It is used in both the base and program modules as 
   needed, i.e., whenever a method or submethod accesses an array.
3) All events and state-accessing functions are modified to take an
   additional argument, "addr : bits", which specifies the array
   index to be accessed. This parameter is passed to all "Array" 
   methods, e.g., Get, Set, as the index argument.
4) The stateInvariant predicate is modified to describe the contents 
   of every cell in the array. i.e., there are now "forall" quantifiers
   in front of every part of the predicate.


Cumulative rules for translation to Lucid:
1) Drop the declaration of any variable declared "ghost."
2) Drop any statement updating a ghost variable (labeled by comment).
3) Drop any method, predicate or function declared ghost or labeled ghost
   (by comment).
4) Fill in the bodies of extern methods with executable and correct code.  
5) Translate the "dispatch" method into the Lucid equivalent.  
In the following steps, refer to the Memop module in lucidBase3.dfy.
6) Declare all non-ghost state variables as StateVar data types.
   Initialize their values with the Atomic constructor.
7) Whenever a state variable is referred to in specifications or ghost 
   code, refer to it as "variable.val".
8) Whenever a state variable is read or written in executable code, it must
   be accessed through one of the three Memop methods Get, Set, or GetSet.
   Get and GetSet require temporary variables for returning the old (but
   possibly modified by the memcalc) value.
9) After adding the Memop methods, on every execution path, each state
   variable must be the subject of at most one Memop method.  The order of
   these Memop methods must be consistent with a particular total ordering
   of the state variables.
10)If (9) cannot be obeyed, then the second access to a state variable,
   for processing the same packet, must become the first access to the
   state variable in processing a recirculation packet (see next).
11)Every dispatched event returns a recirculation command.  If the event
   needs no recirculation packet, return:
      recirc := RecircCmd (false, Non());
   If the event needs a recirculation packet, return:
      recirc := RecircCmd (true, OtherEvent (arg)); 
   Then the Lucid base will generate a timed OtherEvent and add it to the
   queue.

In some cases, it may be useful to define an invariant that relates the
state variables to the state of the queue.  This is straightforward, but
only if the strict separation between the base and program is violated.  
The easy way to do this is to put program-specific information in the base.
   As an example, this program satisfies the invariant that there is 
exactly one recirculation packet in the queue, if and only if 
"recircPending" is true.  But this invariant only holds between calls of
"pickNextEvent" in the base. 

???
TODO
can you verify the PLUS specs?
???
-------------------------------------------------------------------------*/
include "lucidBase4.dfy"

/*
   Adding arrays.
*/

module LucidProg refines LucidBase {
   import opened Array
   
   type counter = x : int | 0 <= x < 1048576         // limit must exceed U

   datatype Event =
    | ProcessPacket (addr : bits, dnsRequest: bool, uniqueSig: nat)
    | SetFiltering (addr : bits, toWhat: bool)
    | SimulatedClockTick ()
    | SimulatedHardwareFailure ()
    | Non ()

class Program ... {

   // Parameters
   const I : nat := 16             // interval length, < T and a power of 2
   const Q : bits                              // maximum DNS response time
   const QRoff : bits   // Q plus observation window for stopping filtering
   const W : nat                   // Bloom-filter window size, >= Q as nat
   const U : counter                               // upper count threshold
   const L : counter                               // lower count threshold
   const A : nat := 256 // array length -- must match the bits type

   // Address State
   var currentIntv : Array <bits>              // current interval
   var count : Array <counter>          // counter for DNS replies
   var filtering : Array <bool>   // turns adaptive filtering on and off
   ghost var timeOn : seq<nat>         // effective time filtering was turned on
   var timestampOn : Array <bits>            // implementation of timeOn
   ghost var actualTimeOn : seq<nat>          // actual time filtering turned on
   var recircPending : Array <bool>   // a "semaphore" for recirculation
   ghost var forwarded: bool            // used to specify filtering result
   ghost var requestSet : seq<set<nat>>      // pending requests, for filtering
   ghost var preFilterSet : seq<set<nat>>        // requestSet, before deletion
   
   // Array size constraints
   ghost predicate arraySizes ()
      {        
         |currentIntv.cells| == A
      && |count.cells| == A      
      && |filtering.cells| == A
      && |timestampOn.cells| == A
      && |recircPending.cells| == A
      && |timeOn| == A
      && |actualTimeOn| == A
      && |requestSet| == A
      && |preFilterSet| == A
      }

   ghost predicate parameterConstraints ()           // from problem domain
      {  I > 0 && QRoff > Q > 0 && W >= Q && U < 1048576  }

   constructor ()
   {
      queue := [];
      lastTime := 0;
      filtering := Create (A, false);
      recircPending := Create (A, false);
      timeOn := seq(A, i => 0);
      actualTimeOn := seq(A, i => 0);
      currentIntv, timestampOn := Create (A, 0), Create (A, 0);
      count := Create(A, 0);
      requestSet := seq(A, i => {});
      preFilterSet := seq(A, i => {});
   }

   ghost predicate protecting (addr : bits, time: nat) 
      requires arraySizes ()
      reads this
   {  filtering.cells[addr] && (time - actualTimeOn[addr]) >= Q as nat  }

   ghost predicate protectImplmnt (addr: bits, timestamp: bits) 
   // memops caused refactoring, which replaced this predicate
      requires arraySizes ()
      reads this
   {  filtering.cells[addr] && elapsedTime (timestamp, timestampOn.cells[addr]) >= Q  }

   function elapsedTime (now: bits, origin: bits): (res: bits)
      reads this
      // Function satisfies specification because of mod arithmetic.
         ensures now >= origin ==> res == (now - origin)
         ensures now < origin ==>                         // 0 is T as bits
            res == (now + T - origin)
   {  (now - origin) % T  }        // implemented as bit-vector subtraction


   ghost predicate stateInvariant (time: nat, timestamp: bits)
   {  (  forall i :: 0 <= i < A ==> timestampOn.cells[i] == timeOn[i] % T  )
   && (  forall i :: 0 <= i < A ==> actualTimeOn[i] <= timeOn[i]  )
   && (  forall i :: 0 <= i < A ==> timeOn[i] <= time  )
   && (  forall i :: 0 <= i < A ==> (timeOn[i] > actualTimeOn[i]) ==> (time >= timeOn[i] + Q as nat)  )
   && (  forall i :: 0 <= i < A ==>
            filtering.cells[i] ==> 
               (protecting (i, time) <==> protectImplmnt (i, timestamp)))
   && (  forall i :: 0 <= i < A ==> ! filtering.cells[i] ==> requestSet[i] == {}  )
   && (  arraySizes () )
   }


   ghost predicate operatingAssumptions (e: TimedEvent) 
   // There cannot be restrictions on recirculation events, i.e.,
   // SetFiltering events, because they were already chosen by the program.
   {
      if      e.event.ProcessPacket?
      then       (filtering.cells[e.event.addr] ==> e.time < actualTimeOn[e.event.addr] + T) 
              && (e.time - lastTime < T - I              ) 
      else if e.event.SimulatedClockTick?
      then    (forall addr :: 0 <= addr < A ==> 
         filtering.cells[addr] ==> (e.time + 1) < actualTimeOn[addr] + T) 
      else true
   }

   method dispatch (e: TimedEvent) returns (recirc: RecircCmd)
   {  
      recirc := RecircCmd (false, Non());
      if {
         case e.event.ProcessPacket? => 
         {  recirc := processPacket 
               (e.event.addr, e.time,e.timestamp, e.event.dnsRequest, e.event.uniqueSig);
         }
         case e.event.SetFiltering? => 
            setFiltering (e.event.addr, e.time, e.timestamp, e.event.toWhat);
         case e.event.SimulatedClockTick? => 
            simulatedClockTick (e.time, e.timestamp);
         case e.event.SimulatedHardwareFailure? => 
            simulatedHardwareFailure (e.time, e.timestamp);
         case e.event.Non? => 
      }
   } 

   method processPacket (addr: bits, time: nat, timestamp: bits, dnsRequest: bool, 
                                uniqueSig: nat) returns (recirc: RecircCmd)
      modifies this
      requires arraySizes ()
      // There must be a packet between any two interval rollovers, so
      // that interval boundaries can be detected.  Unfortunately, the
      // specification is not strong enough to cause verification to fail
      // without this operating assumption.
         requires time - lastTime < T - I
      // Note that there is no mechanism for dealing with counter overflow.
      // Below is the operating assumption to make attack time spans 
      // measurable.
         requires filtering.cells[addr] ==> time < actualTimeOn[addr] + T
      requires timestamp == time % T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures arraySizes ()
      ensures (  ! dnsRequest && protecting (addr, time)
              && ! (uniqueSig in preFilterSet[addr])   ) 
              ==> ! forwarded                     // Adaptive Protection,
                                                  // needs exact requestSet
      ensures ! forwarded ==>                               // Harmlessness
              (  ! dnsRequest && ! (uniqueSig in preFilterSet[addr])  )
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures stateInvariant (time, timestamp)
   {
      if (dnsRequest) {  
         forwarded := processRequest (addr, time, timestamp, uniqueSig); // ghost
         recirc := RecircCmd (false, Non()); 
      }
      else { 
         preFilterSet := requestSet;                        // ghost update
         forwarded, recirc := processReply (addr, time, timestamp, uniqueSig); 
      }   
   }


   method processRequest (addr : bits, time: nat, timestamp: bits, uniqueSig: nat)
                                                  returns (forwarded: bool)
      modifies this
      requires arraySizes ()
      requires timestamp == time % T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures forwarded
      ensures arraySizes ()
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures stateInvariant (time, timestamp)

   {
      var tmpFiltering : bool := Get (filtering, addr, nocalc, true);
      if (tmpFiltering) {
         bloomFilterInsert (addr, uniqueSig);
         requestSet := requestSet[addr := requestSet[addr] + {uniqueSig}];  
                 // ghost update
      }
      forwarded := true;                                    // ghost update
   }

   function interval (timestamp: bits): bits
      reads this
      requires parameterConstraints ()
   {  timestamp / I  }                    // implemented with a right-shift
 
   function upperBoundedIncr (count: counter, unused: counter) : counter
   // this is a custom memcalc
   {  if count < U then (count + 1) else (count)  }

   function newTime (memVal: bits, timestamp: bits): bits
   // this is a custom memcalc
   {  if (timestamp - memVal) % T >= Q then (timestamp - Q) % T
      else memVal
   }

   // left off here: 
   // I don't think this will scale if we have "forall" predicates throughout 
   // the program that verify the state of the entire program, even parts
   // of the state that this packet did not modify. We need the stateInvariant 
   // to be fore one single slice of state, not the entire state. 
   // So it has to either take an address or the event. 

   method processReply (addr: bits, time: nat, timestamp: bits, uniqueSig: nat) 
                               returns (forwarded: bool, recirc: RecircCmd)
      modifies this
      modifies this`timeOn
      requires arraySizes ()
      requires preFilterSet == requestSet
      // There must be a packet between any two interval rollovers, so
      // that interval boundaries can be detected.  Unfortunately, the
      // specification is not strong enough to cause verification to fail
      // without this operating assumption.
         requires time - lastTime < T - I
      // Operating assumption to make attack time spans measurable.
         requires filtering.cells[addr] ==> time < actualTimeOn[addr] + T
      requires timestamp == time % T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures arraySizes ()
      ensures (  protecting (addr, time) && ! (uniqueSig in preFilterSet[addr])   )
              ==> ! forwarded                     // Adaptive Protection,
                                                  // needs exact requestSet
      ensures ! forwarded ==>                               // Harmlessness
                 ! (uniqueSig in preFilterSet[addr])
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures stateInvariant (time, timestamp)
   {
   // Changes to measurement state:
   // If an interval boundary has been crossed, save the count in
   // oldCount, and reset the counter to 1 (for this reply).  Otherwise
   // simply increment the count.
   // If there is an interval with no reply packets, then the count
   // will not be reset for that interval.  However, the count will
   // never include replies from more than one interval.
      var oldCount : counter := 0;
      var tmpCurrentIntv : bits;
      var tmpCount : counter; 
      tmpCurrentIntv, currentIntv := GetSet (
         currentIntv, addr, nocalc, 0, swapcalc, interval (timestamp) );
      if interval (timestamp) != tmpCurrentIntv {
         oldCount, count := GetSet ( count, addr,nocalc, 0, swapcalc, 1 );
      }
      else {
         count := Set (count, addr,upperBoundedIncr, 0);
      }
      tmpCount := count.cells[addr];

   // Changes to filtering state:
   // Turning filtering on:
   // Filtering is turned on as soon as count reaches upper threshold.
   // (Note that in !filtering test of count, it should never exceed U, so
   // this is defensive programming.)
      var tmpFiltering : bool := Get (filtering, addr, nocalc, true);
      var tmpTimestampOn : bits;
      if ! tmpFiltering {
         if tmpCount >= U { // time to turn filtering on
            var tmpRecircPending : bool;
            tmpRecircPending, recircPending := GetSet (
               recircPending, addr, nocalc, true, swapcalc, true);
            if ! tmpRecircPending {
               recirc := RecircCmd (true, SetFiltering(addr, true));
            }
            // else recirc already generated, do nothing
            else {  recirc := RecircCmd (false, Non());  }
         }
         else {  recirc := RecircCmd (false, Non());  }
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
         if oldCount > 0 { // interval boundary crossed
            if oldCount >= L {

               ghost var oldTimestampOn := timestampOn.cells[addr];        // ghost
               tmpTimestampOn, timestampOn := GetSet (
                  timestampOn, addr, newTime, timestamp, newTime, timestamp);
               if oldTimestampOn != tmpTimestampOn {               // ghost
                  timeOn := timeOn[addr := time - Q]; // ghost update
               }

               recirc := RecircCmd (false, Non());
            }
            else { // oldCount < L

               tmpTimestampOn := Get (timestampOn, addr, nocalc, 0);
               if (timestamp - tmpTimestampOn) % T >= QRoff {
                  // time to turn filtering off
                  var tmpRecircPending : bool;
                  tmpRecircPending, recircPending := GetSet (
                     recircPending, addr, nocalc, true, swapcalc, true);
                  if ! tmpRecircPending {
                     recirc := RecircCmd (true, SetFiltering(addr, false));
                  }
                  // else recirc already generated, do nothing
                  else {  recirc := RecircCmd (false, Non());  }
               }
            // count is low, just waiting for Woff to elapse
            recirc := RecircCmd (false, Non());
            }
         }  // end of case where interval boundary crossed
         else {  tmpTimestampOn := Get (timestampOn, addr, nocalc, 0);
                 recirc := RecircCmd (false, Non());           }
      }  // end of filtering case
   // Filtering decision:
      if tmpFiltering && (time - tmpTimestampOn) % T >= Q {
         forwarded := filter (addr, time, timestamp, uniqueSig);
      }
      else {  forwarded := true; }
   }

   method filter (addr : bits, time: nat, timestamp: bits, uniqueSig: nat) 
                                                  returns (forwarded: bool)
      modifies this
      requires arraySizes ()
      requires protectImplmnt (addr, timestamp)
      requires preFilterSet == requestSet
      requires timestamp == time % T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures arraySizes ()
      ensures     ! (uniqueSig in preFilterSet[addr])
              ==> ! forwarded                     // Adaptive Protection,
                                                  // needs exact requestSet
      ensures ! forwarded ==>                               // Harmlessness
                 ! (uniqueSig in preFilterSet[addr])
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures arraySizes ()
      ensures stateInvariant (time, timestamp)
   {
      forwarded := bloomFilterQuery (addr, uniqueSig);
      if forwarded {                 // if positive is false, has no effect
         requestSet := requestSet[addr := requestSet[addr] - { uniqueSig }];          // ghost update
      }
   }


   method setFiltering (addr : bits, time: nat, timestamp: bits, toWhat: bool) 
      modifies this
      requires timestamp == time % T
      requires parameterConstraints ()
      requires arraySizes ()
      requires stateInvariant (time, timestamp)
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures arraySizes ()
      ensures stateInvariant (time, timestamp)
   {
      filtering := Set (filtering, addr, swapcalc, toWhat);
      if toWhat {
      timestampOn := Set (timestampOn, addr, swapcalc, timestamp);
         timeOn := timeOn[addr := time]; // ghost update
         actualTimeOn := actualTimeOn[addr := time]; // ghost update
      }
      else { requestSet := requestSet[addr := {}]; }                           // ghost update
      recircPending := Set (recircPending, addr, swapcalc, false);

   }

   method simulatedClockTick (time: nat, timestamp: bits)          // ghost
      modifies this
      requires timestamp == time % T
      requires arraySizes ()
      // Operating assumption to make attack time spans measurable.  
      // Without the "+ 1", the method cannot be verified.
         requires (forall addr :: 0 <= addr < A ==> 
            filtering.cells[addr] ==> (time + 1) < actualTimeOn[addr] + T)
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures arraySizes ()
      ensures stateInvariant (time, timestamp)
   {
      var timePlus : nat := time + 1;
      var timestampPlus : bits := (timestamp + 1) % T;
      assert stateInvariant (timePlus, timestampPlus);
   }

   method simulatedHardwareFailure (time: nat, timestamp: bits)    // ghost
      modifies this
      requires arraySizes ()
      requires timestamp == time % T
      requires parameterConstraints ()
      requires stateInvariant (time, timestamp)
      ensures unchanged(this`queue) ensures unchanged(this`lastTime)
      ensures arraySizes ()
      ensures stateInvariant (time, timestamp)
   {
      filtering, recircPending := Create (A, false), Create (A, false);
      timeOn, actualTimeOn := seq(A, _ => 0), seq(A, _ => 0);
      currentIntv, timestampOn := Create(A, 0), Create (A, 0);
      count := Create (A,0);
      requestSet := seq(A, _ => {});
   }

   method {:extern} bloomFilterInsert (addr : bits, uniqueSig: nat)

   method {:extern} bloomFilterQuery (addr : bits, uniqueSig: nat)
                                                  returns (inSet: bool)
   requires arraySizes ()
   // No false negatives:
   // A sliding-window Bloom filter automatically deletes set members
   // shortly after a guaranteed tenancy W.  You might imagine that
   // this would be a source of false negatives.  However, it is not,
   // because a request never needs to stay in the set longer than Q,
   // where Q <= W.
      ensures uniqueSig in requestSet[addr] ==> inSet
   // No false positives:
   // Not true, but used to prove Adaptive Protection as a sanity
   // check.  (If deleted, Adaptive Protection cannot be proved.)  This
   // property can be false for two reasons: (1) it is the nature of
   // a Bloom filter to yield false positives sometimes; (2) in a
   // sliding-window Bloom filter, there are no timely deletions, just
   // scheduled timeouts which can be delayed.
      ensures ! (uniqueSig in requestSet[addr]) ==> (! inSet)
}
}
