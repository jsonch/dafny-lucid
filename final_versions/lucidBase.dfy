abstract module LucidBase {

   type Event (==)

   datatype TimedEvent = TimedEvent (event: Event, time: nat)

   class Program {
      var queue : seq <TimedEvent>

      ghost predicate parameterConstraints () // must be defined in program
         reads this

      ghost predicate stateInvariant (time: nat)       // define in program
         reads this

      ghost predicate validQueue (q: seq <TimedEvent>)   // queue invariant
      {
         match |q| {
            case 0 => true
            case 1 => true
            case _ => q[0].time <= q[1].time && validQueue (q [1..])
         }            
      }        
        
      constructor ()                          // must be defined in program
         ensures validQueue (queue)
         ensures parameterConstraints ()
         ensures stateInvariant (0)

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
         requires stateInvariant (q[0].time)
         ensures validQueue (queue)
         ensures |queue| == |q| - 1
      {  
         dispatch(q[0]);
         this.queue := q[1..];
      }

      method dispatch (e: TimedEvent)         // must be defined in program
         modifies this
         requires parameterConstraints ()
         requires stateInvariant (e.time)
   }
}
