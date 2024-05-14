abstract module LucidBase {

   type Event (==)

   type bits = x : int | 0 <= x < 256      // number must match parameter T

   datatype TimedEvent = 
      TimedEvent (event: Event, time: nat, timestamp: bits)

   datatype RecircCmd = RecircCmd (generate: bool, event: Event)

   class Program {
      const T : nat := 256               // number must match limit on bits
      var queue : seq <TimedEvent>
      var lastTime : nat

      ghost predicate parameterConstraints ()  // may be defined in program
         reads this

      ghost predicate arraySizes ()  // may be defined in program
         reads this

      ghost predicate stateInvariant (time: nat, timestamp: bits) // define
         reads this                                           // in program
         requires timestamp == time % T
         requires arraySizes ()

      ghost predicate validQueue (q: seq <TimedEvent>)   // queue invariant
      // In a valid queue, times and timestamps match, and time is 
      // nondecreasing.
      {   
         match |q| {
            case 0 => true
            case _ =>  
               (  forall j | 0 <= j < |q| :: 
                     q[j].timestamp == q[j].time % T  )
            && (  forall j | 0 <= j < |q|-1 :: 
                     q[j].time <= q[j+1].time         )
      }  }
      
      ghost predicate operatingAssumptions (e: TimedEvent)        // may be
         reads this                                   // defined in program
         requires arraySizes ()

      constructor ()                          // must be defined in program
         ensures validQueue (queue)
         ensures parameterConstraints ()
         ensures arraySizes ()
         ensures stateInvariant (0, 0)

      method simulateArrival ()
         modifies this`queue
         requires validQueue (queue)
         ensures validQueue (queue)
         ensures |queue| == |old(queue)| + 1
         ensures queue[0..|old(queue)|] == old(queue)

      method pickNextEvent (q: seq <TimedEvent>)
         modifies this
         requires |queue| > 0
         requires q == queue
         requires validQueue (q)
         requires parameterConstraints ()
         requires arraySizes ()
         requires stateInvariant (q[0].time, q[0].timestamp)
         // If the head of the queue does not satisfy the operating
         // assumptions, then this execution is permanently blocked (but
         // other valid executions will proceed).
            requires operatingAssumptions (q[0])
         ensures validQueue (queue)
      {  
         var recirc := dispatch(q[0]);
         if recirc.generate { generateRecircEvent (recirc.event); }
         this.queue := q[1..];
         lastTime := q[0].time;
      }

      method dispatch (e: TimedEvent) returns (recirc: RecircCmd)
         modifies this                        // must be defined in program
         requires e.timestamp == e.time % T
         requires |queue| > 0
         requires arraySizes ()
         requires operatingAssumptions (e)
         requires validQueue(queue)
         requires parameterConstraints ()
         requires stateInvariant (e.time, e.timestamp)
         ensures unchanged(this`queue) ensures unchanged(this`lastTime)
         ensures validQueue (queue)

      method generateRecircEvent (e: Event)
         modifies this`queue
         requires validQueue (queue)
         requires |queue| > 0              // because method is called just
                    // after dispatch, when dispatched event still in queue
         ensures validQueue (queue)
      {
         var recircEvent: TimedEvent;
         var recircTimestamp: bits;
         if |queue[1..]| == 0 {
            recircTimestamp := (queue[0].time + 1) % T;
            recircEvent := 
               TimedEvent (e, queue[0].time + 1, recircTimestamp);
         } 
         else {
            recircTimestamp := (queue[|queue|-1].time + 1) % T;
            recircEvent := 
               TimedEvent (e, queue[|queue|-1].time + 1, recircTimestamp);
         }
         queue := queue + [recircEvent];
      }
   }
}

module Array {
   type bits = x : int | 0 <= x < 256      // number must match parameter T
   type memcalc<!t> = (t, t) -> t

   // NEW: an "ArrayVar" is like a "StateVar", except its inner val 
   // is a sequence of type "t" values instead of a single type "t" value.
   datatype Array<t> = Atomic (cells: seq<t>) 


   // NEW: added a "Create" function to create an array of a given size
   function Create<t> (n: nat, init: t) : Array<t>
   {
      Atomic(seq(n, (_ => init)))
   }

   // NEW: Get, Set, and GetSet now take an index as the second argument
   // the functions are the same as in Memop, but use the index to access
   // the appropriate element of the array.
   method Get<t> (s:Array<t>, idx:bits, mget: memcalc, garg: t) returns (oldVal:t)
   requires 0 <= idx < |s.cells|
   ensures oldVal == mget(s.cells[idx], garg)
   {  
      oldVal := mget (s.cells[idx], garg);
   }

   method Set<t> (s: Array<t>, idx:bits, mset: memcalc, sarg: t)
                                              returns (newVal: Array<t>)
   requires 0 <= idx < |s.cells|
   ensures |newVal.cells| == |s.cells|
   // NEW: the following line says that newVal is the same as s, except
   // that newVal.val[idx] is updated to be mset(s.val[idx], sarg)
   ensures newVal.cells == s.cells[idx := mset(s.cells[idx], sarg)]
   {  
      var newCell := mset (s.cells[idx], sarg);
      newVal := Atomic (s.cells[idx := mset(s.cells[idx], sarg)]);
      // must be called so that s := newVal;
   }

   method GetSet<t> (s: Array<t>, idx: bits,
                                     mget: memcalc, garg: t,
                                     mset: memcalc, sarg: t)
                                   returns (oldVal: t, newVal: Array<t>)
   requires 0 <= idx < |s.cells|
   ensures oldVal == mget(s.cells[idx], garg)
   ensures newVal.cells == s.cells[idx := mset(s.cells[idx], sarg)]
   {  
      oldVal := mget (s.cells[idx], garg);
      newVal := Atomic (s.cells[idx := mset(s.cells[idx], sarg)]);
      // must be called so that s := newVal;
   }

   // generic memcalcs
   function nocalc<t> (oldVal: t, newArg: t) : t {  oldVal  }
   function swapcalc<t> (oldVal: t, newArg: t) : t {  newArg  }
}
