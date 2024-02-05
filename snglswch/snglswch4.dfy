/*---------------------------------------------------------------------
SINGLE-SWITCH ALGORITHM AND FULL SPECIFICATION, with 
LUCID-LIKE MEMOPS, and
TRANSLATABLE CODE FOR PACKET RECIRCULATION (verified)

This version is derived from Version 3 by adding packet recirculation
to avoid second accesses to the same state variable while processing
one packet.  Dafny code will be translated to Lucid by means of ifdefs.

If a state variable is written more than once in processing a packet,
or is written after it is read, the later writes must be performed in
processing a recirculation packet.  Needless to say, this introduces
delays in state changes that must be reasoned about.

The techniques documented here require that, for a given type of
recirculation packet (where the "type" can be defined by arguments as
well as a general type), only one is recirculating at a time.  A state
variable acts as a semaphore to ensure this.  If single recirculation
is not sufficient for the problem domain, then the techniques must be
extended.

Each general type of recirculation packet (more general than in the
previous paragraph) requires a declared event and a handler for it.
The generate statements in Lucid correspond to Dafny assignments to
ghost variables, saving the arguments of the generated packet.  There
now only one set of these ghost variables, which is why there can only
be one packet in recirculation.
 
Translation of the Dafny program into Lucid must ensure two things: (i)
the result is a compilable Lucid program, and (ii) Dafny verification
correctly captures the semantics of the Lucid program.  So there are
both translation rules and syntactic checks on the Ludafny program.

Cumulative rules for translation to Lucid:
1) Drop the declaration of any variable labeled "ghost."
2) Drop any statement assigning a value to a ghost variable.  Dafny
   does this automatically, and verifies that ghost variables are not
   used in executable statements.  For convenient translation, these
   statements are labeled "// ghost" in the right margin.
3) Drop any method or function labeled "ghost," either at the
   beginning or end of the line where it is declared.  In Dafny, a
   predicate or function is automatically a ghost, while a predicate
   method or function method is not.
4) Fill in the bodies of extern methods with executable and correct
   code.
5) Rules for recirculation packets:
   In general, ifdefs are used for recirculation packets.  So the
   actual code translation is easy, but the constraints are more
   elaborate.
   a) A type of recirculation packet must be declared as follows:
      // IF LUCID
      // event Recirc (int arg1, bool arg2)
      // FI
   b) Then there must be one or more ifdefs to generate the packets:
      // IF LUCID
      // generate Recirc (addr, true);
      // ELSE
      recircArg1 ;= addr;           // ghost
      recircArg2 := true;           // ghost
      // FI
      The Lucid code must be a generate statement that matches the
      declaration, and the Dafny code must be non-implementable code
      using history variables to save the packet arguments.
   c) And there must also be one event handler:
      // IF LUCID
      // handle Recirc (int arg1, bool arg2)
      // ELSE
      method handleRecirc (arg1: int, arg2: bool)
      // FI
      The Lucid handler must match the declaration.  The Dafny method
      may have additional arguments.  It must have arguments to match
      the declaration.  Furthermore, the method specification must
      contain the following statements:
      requires arg1 == recircArg1
      requires arg2 == recircArg2
6) Do a syntactic check to ensure that on all execution paths, the       
   state variables are accessed at most once for each, and in the same 
   order.  Note that this check could be done with Dafny verification, 
   but it seems too messy.
---------------------------------------------------------------------*/

type bits = x : int | 0 <= x < 256                 // number must match
                                                   // the parameter T
class AddressState
{  // Parameters
   const T : nat := 256
   const I : nat := 16                          // interval length, < T 
   const i : nat := 4                                        // I = 2^i
   const Q : bits                          // maximum DNS response time
   const QRoff : bits                      // Q plus observation window
                                           // for turning filtering off
   const W : nat                      // Bloom-filter window size, >= Q
   const U : nat                               // upper count threshold
   const L : nat                               // lower count threshold
   // Address State 
   var lastIntv : bits    // an interval, so first 8-i bits always zero
   var count : nat                           // counter for DNS replies
   var filtering : bool          // turns adaptive filtering on and off
   var timeOn : bits      // implementation of time filtering turned on
   var recircPending : bool          // a "semaphore" for recirculation
   ghost var requestSet : set<nat>   // pending requests, for filtering
   ghost var preFilterSet : set<nat> // requestSet, before any deletion
   ghost var lastNatTime : nat
   ghost var actualTimeOn : nat
   ghost var natTimeOn : nat
   ghost var recircSwitch : bool 
   // Recirculation Events
   // IF LUCID
   // event SetFiltering (bool on)     // declares recirculation packet
   // FI

   constructor ()
   {
      filtering, recircPending := false, false;
      lastIntv, count, timeOn := 0, 0, 0;
      lastNatTime, actualTimeOn, natTimeOn := 0, 0, 0;         // ghost
      requestSet := {};                                        // ghost
   }

   ghost predicate stateInvariant (time: bits, natTime: nat)         // ghost
      reads this
   {     (  natTimeOn <= lastNatTime  )
      && (  timeOn == natTimeOn % T  )
      && (  natTimeOn >= actualTimeOn  )
      && (  filtering ==> 
               (protecting (natTime) <==> protectImplmnt (time))  )
      && (  ! filtering ==> requestSet == {}  )
      && (  recircPending ==> (filtering == ! recircSwitch)  )
   }

   ghost predicate protecting (natTime: nat)                         // ghost
      reads this
   {  filtering && (natTime >= natTimeOn + Q as nat)  }

   predicate protectImplmnt (time: bits)
   // protecting is a specification, using history variables.  This
   // is its implementation, which cannot use history variables.
      reads this
   {  filtering && elapsedTime (time, timeOn) >= Q  } 

   function elapsedTime (now: bits, origin: bits): (res: bits)
      reads this
      // Function satisfies specification because of mod arithmetic.
         ensures now >= origin ==> res == (now - origin)
         ensures now < origin ==>                     // 0 is T as bits
            res == (now + T - origin)
   {  (now - origin) % T  }    // implemented as bit-vector subtraction  

   function interval (time: bits): bits
      reads this
   {  time / I  }                           // implemented as time >> i

   method ProcessPacket
      (time: bits, natTime: nat, dnsRequest: bool, uniqueSig: nat)
                                              returns (forwarded: bool)   
      modifies this
      requires time == natTime % T
      // Two packets can have the same timestamp.
         requires natTime >= lastNatTime
      // There must be a packet between any two interval rollovers, so
      // that interval boundaries can be detected.  
         requires natTime - lastNatTime < T - I
      // Constraint to make attack time spans measurable.
         requires natTime < actualTimeOn + T
      requires parameterConstraints ()
      requires stateInvariant (time, natTime)
      ensures (  ! dnsRequest && protecting (natTime)
              && (! (uniqueSig in preFilterSet))      )
              ==> ! forwarded   // Adaptive Protection, needs exactness
      ensures ! forwarded ==>                           // Harmlessness
              (  ! dnsRequest && (! (uniqueSig in preFilterSet))  )
      ensures stateInvariant (time, natTime)
   {
      if (dnsRequest) {  
         forwarded := 
            processRequest (time, natTime, dnsRequest, uniqueSig); 
      }
      else {
         preFilterSet := requestSet;                           // ghost  
         forwarded := 
           processReply (time, natTime, dnsRequest, uniqueSig); 
      }
   }

   method processRequest
      (time: bits, natTime: nat, dnsRequest: bool, uniqueSig: nat)
                                              returns (forwarded: bool)
      modifies this
      requires time == natTime % T
      // Two packets can have the same timestamp.
         requires natTime >= lastNatTime
      requires dnsRequest
      requires parameterConstraints ()
      requires stateInvariant (time, natTime)
      ensures dnsRequest
      ensures forwarded 
      ensures stateInvariant (time, natTime)
   {
      var tmpFiltering : bool := filtering;                // get memop
      if (tmpFiltering) {  
         bloomFilterInsert (uniqueSig);                        // memop
         requestSet := requestSet + { uniqueSig }; }           // ghost
      forwarded := true;
      lastNatTime := natTime;                                  // ghost
   }

   method processReply 
      (time: bits, natTime: nat, dnsRequest: bool, uniqueSig: nat)
                                              returns (forwarded: bool)
      modifies this
      requires time == natTime % T
      // Two packets can have the same timestamp.
         requires natTime >= lastNatTime
      // There must be a packet between any two interval rollovers, so
      // that interval boundaries can be detected.  
         requires (natTime - lastNatTime) < (T - I)
      // Constraint to make attack time spans measurable.
         requires natTime < actualTimeOn + T
      requires ! dnsRequest
      requires preFilterSet == requestSet
      requires parameterConstraints ()
      requires stateInvariant (time, natTime)
      ensures ! dnsRequest
      ensures (  ! dnsRequest && protecting (natTime)
              && (! (uniqueSig in preFilterSet))    )
              ==> ! forwarded   // Adaptive Protection, needs exactness
      ensures ! forwarded ==>                           // Harmlessness
              (  ! dnsRequest && (! (uniqueSig in preFilterSet))  )
      ensures stateInvariant (time, natTime)
   {

   // Changes to measurement state:
   // Increment or reset count.  If there is an interval with no reply
   // packets, then the count will not be reset for that interval.
   // However, the count will never include replies from more than one
   // interval.
      var oldCount : nat := 0;
      var tmpCount : nat;
      var tmpLastIntv : bits := lastIntv;          // get memop . . . .
      lastIntv := interval (time);                 // with update memop 
      if interval (time) != tmpLastIntv {
         oldCount := count;
         tmpCount := 1;                            // get memop . . . .
         count := 1;                               // with update memop
      }
      else {  
         tmpCount := count + 1;                    // get memop . . . .
         count := count + 1;                       // with update memop
      }

   // Changes to filtering state:
   // Filtering is turned on as soon as count reaches upper threshold.
   // (Note that in !filtering test of count, it should never exceed U, 
   // so this is defensive programming.)  There is no declarative 
   // specification of turning filtering off,  so we make the code as 
   // readable as possible.
      var tmpFiltering : bool := filtering;                // get memop
      var tmpTimeOn : bits;
      var tmpRecircPending : bool;
      if ! tmpFiltering {
         if tmpCount >= U {
            // time to turn filtering on
            tmpRecircPending := recircPending;     // get memop . . . .
            recircPending := true;                 // with update memop
            if ! tmpRecircPending {
               // IF LUCID
               // generate SetFiltering (true);
               // ELSE
               recircSwitch := true;                           // ghost
               // FI
            }  // else recirc already generated, do nothing
         }
      }
      else { // filtering
         if oldCount != 0 { // interval boundary crossed
            if oldCount >= L {
               if elapsedTime (time, timeOn) >= Q        // get memop .
                  {  tmpTimeOn := (time - Q) % T;  }     // . . . . . .
               else { tmpTimeOn := timeOn; }             // . . . . . .
               if elapsedTime (time, timeOn) >= Q {      // with update
                  timeOn := (time - Q) % T;              // memop 
                  natTimeOn := natTime - Q;                    // ghost
               }                                           
            }
            else { // oldCount < L
               tmpTimeOn := timeOn;                        // get memop
               if elapsedTime (time, tmpTimeOn) >= QRoff {
                  // time to turn filtering off
                  tmpRecircPending := recircPending;//get memop . . . .
                  recircPending := true;           // with update memop
                  if ! tmpRecircPending {
                     // IF LUCID
                     // generate SetFiltering (false);
                     // ELSE
                     recircSwitch := false;                    // ghost
                     // FI
                  }  // else recirc already generated, do nothing
               }
            }  
         } // end boundary-crossing case
         else {  tmpTimeOn := timeOn; }                    // get memop
      } // end filtering case
      lastNatTime := natTime;                                  // ghost

   // Filtering decision:
   // if filtering off, it won't matter that timeOn not read
      if tmpFiltering && elapsedTime (time, tmpTimeOn) >= Q {
         forwarded := filter (time, natTime, dnsRequest, uniqueSig);
      }
      else {  forwarded := true; }
   }

   method filter
      (time: bits, natTime: nat, dnsRequest: bool, uniqueSig: nat) 
                                              returns (forwarded: bool)  
      modifies this
      requires ! dnsRequest
      requires protectImplmnt (time)
      requires preFilterSet == requestSet
      requires parameterConstraints ()
      requires stateInvariant (time, natTime)
      ensures protectImplmnt (time)
      ensures (   (! (uniqueSig in preFilterSet))      )
              ==> ! forwarded   // Adaptive Protection, needs exactness
      ensures ! forwarded ==>                           // Harmlessness
              (  ! dnsRequest && (! (uniqueSig in preFilterSet))  )
      ensures stateInvariant (time, natTime)
   {
      forwarded := bloomFilterQuery (uniqueSig);               // memop
      if forwarded {      // if positive is false, has no effect; ghost
         requestSet := requestSet - { uniqueSig };             // ghost
      }
   }

   // IF LUCID
   // handle SetFiltering (bool on)
   // ELSE
   method handleSetFiltering (time: bits, natTime: nat, on: bool)
   // FI
      modifies this
      requires on == recircSwitch      // parameter gets ghost variable
      requires time == natTime % T
      // Two packets can have the same timestamp.
         requires natTime >= lastNatTime
      requires recircPending
      requires parameterConstraints ()
      requires stateInvariant (time, natTime)
      ensures ! recircPending
      ensures stateInvariant (time, natTime)
   {
      var tmpFiltering : bool := on;               // get memop . . . .
      filtering := on;                             // with update memop
      if tmpFiltering {
         var tmpTimeOn : bits := timeOn;           // get memop . . . .
         timeOn := time;                           // with update memop
         actualTimeOn := natTime;                              // ghost
         natTimeOn := natTime;                                 // ghost
         recircPending := false;                        // update memop
      }
      else {
         recircPending := false;                        // update memop
         requestSet := {};                              // update memop
      }
      lastNatTime := natTime;                                  // ghost
   }

   predicate parameterConstraints ()      // from problem domain, ghost  
      reads this
   {  I > 0 && QRoff > Q > 0  && W >= Q  }

   method HardwareFailure (time: bits, natTime: nat)           // ghost
      modifies this
      requires parameterConstraints ()
      requires stateInvariant (time, natTime)
      ensures stateInvariant (time, natTime)
   { 
      filtering, recircPending := false, false;
      lastIntv, count, timeOn, actualTimeOn, natTimeOn := 0, 0, 0, 0,0;
      actualTimeOn, natTimeOn := 0, 0;                         // ghost
      lastNatTime := natTime;                                  // ghost
      requestSet := {};                                        // ghost
   }

   method SimulatedClockTick (time: bits, natTime:nat)         // ghost
      modifies this
      requires time == natTime % T
      requires natTime > lastNatTime
      // Constraint to make attack time spans measurable.
         requires natTime < actualTimeOn + T
      // This extra assumption leaves room for natTimePlus.  It is
      // necessary, which shows that the constraint to make time spans
      // measurable is necessary.
         requires (natTime + 1) < actualTimeOn + T
      requires parameterConstraints ()
      requires stateInvariant (time, natTime)
      ensures stateInvariant (time, natTime)
  {
      var timePlus : bits := (time + 1) % T;
      var natTimePlus : nat := natTime + 1;
      assert timePlus == natTimePlus % T;
      assert filtering ==>                                 // invariant
         (natTime >=natTimeOn + Q as nat <==> (time -timeOn) % T >= Q);
      // show time-sensitive invariant holds after clock tick
      assert filtering ==>
             (protecting (natTimePlus) <==> protectImplmnt (timePlus));   
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
