abstract module LucidBase {

   type Event (==)

   type bits = x : int | 0 <= x < 256      // number must match parameter T

   datatype TimedEvent = 
      TimedEvent (event: Event, time: nat, timestamp: bits)

   class Program {
      const T : nat := 256               // number must match limit on bits
      var queue : seq <TimedEvent>
      var lastTime : nat

      ghost predicate parameterConstraints ()  // may be defined in program
         reads this

      ghost predicate stateInvariant (time: nat, timestamp: bits) // define
         reads this                                           // in program
         requires timestamp == time % T

      ghost predicate validQueue (q: seq <TimedEvent>)   // queue invariant
      // In a valid queue, times and timestamps match, and time is 
      // nondecreasing.
      {
         match |q| {
            case 0 => true
            case 1 => q[0].timestamp == q[0].time % T
            case _ => (  q[0].timestamp == q[0].time % T
                      && q[0].time <= q[1].time && validQueue (q[1..])  )
         }            
      }        
      
      ghost predicate operatingAssumptions (e: TimedEvent)        // may be
         reads this                                   // defined in program

      constructor ()                          // must be defined in program
         ensures validQueue (queue)
         ensures parameterConstraints ()
         ensures stateInvariant (0, 0)

      method simulateArrival (q: seq <TimedEvent>)
         modifies this`queue
         requires q == queue
         requires validQueue (q)
         ensures validQueue (queue)
         ensures |queue| == |q| + 1
         ensures queue[0..|q|] == q

      method pickNextEvent (q: seq <TimedEvent>)
         modifies this
         requires q == queue
         requires |q| > 0
         requires validQueue (q)
         requires parameterConstraints ()
         requires stateInvariant (q[0].time, q[0].timestamp)
         // If the head of the queue does not satisfy the operating
         // assumptions, then this execution is permanently blocked (but
         // other valid executions will proceed).
            requires operatingAssumptions (q[0])
         ensures validQueue (queue)
         ensures |queue| == |q| - 1
      {  
         dispatch(q[0]);
         this.queue := q[1..];
         lastTime := q[0].time;
      }

      method dispatch (e: TimedEvent)         // must be defined in program
         modifies this
         requires e.timestamp == e.time % T
         requires parameterConstraints ()
         requires operatingAssumptions (e)
         requires stateInvariant (e.time, e.timestamp)
   }
}
