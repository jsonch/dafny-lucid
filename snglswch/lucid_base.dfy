/*  1/31/24
    TODO: update this
    This module encodes the semantics of event-based processing in Lucid. 
    To write a Lucid-compatible Dafny program, extend this module 
    with a concrete implementation that defines: 
    --- OUTDATED: instructions below do not reflect 2/24 changes ---

    1. datatype Event
        - should include one datatype constructor for each event
    2. class State
        - declare one "var" for each global in the lucid program
        - extend the constructor to initialize each global var
    3. class Handlers
        - define a handler method for each event
            - invariants: a handler must ensure two invariants:
                1. "inter_event_invariant"
                2. "valid_generate"
            - builtins: a handler should use the builtins: 
                - "Generate(e)" to generate an event e for later processing.
                - "Array_<get | set | update>" to update state. (NOT IMPLEMENTED YET)
        - extend the "Dispatch(e : Event)" method to call the appropriate handler 
          for each event. This should basically just be a switch / case statement.
        - extend the "inter_event_invariant" with whatever conditions your program 
          needs to hold in between events. This invariant relates the mutable state 
          of the program to the contents of the event queue. 
          - By default, the invariant is empty.
          - Dispatch requires inter_event_invariant to hold at the start of each 
            event's processing, and ensures that it holds after it completes
        - extend the constructor to ensure the "inter_event_invariant"
            - we cannot make the base constructor ensure the invariant because 


TODO: 
    1. add in arrays + memops
*/


abstract module LucidBase {
   type bits = x : int | 0 <= x < 256                 // number must match
                                                      // the parameter T
   const T : nat := 256

    type Event(==)
    datatype EventTime = EventTime(time : bits, ghost natTime : nat)
    class State {
        constructor () 
            ensures fresh(this)
        { }
    }

    
    // helpers to reason about event queue contents
    function count_f<T>(ls : seq<T>, f : (T -> bool)) : int
    {
        if (ls == []) then 0
        else (
            if (f(ls[0]))
            then (1 + count_f(ls[1..], f))
            else (count_f(ls[1..], f))
        )
    }
    lemma LemmaCountSumFilterSeq<T>(a : seq<T>, b : seq<T>, f : (T -> bool))
    ensures count_f(a + b, f) == count_f(a, f) + count_f(b, f)

    lemma LemmaCountSumGtFilterSeq<T>(a : seq<T>, b : seq<T>, f : (T -> bool))
    ensures count_f(a + b, f) > count_f(a, f)
    ensures count_f(a + b, f) > count_f(b, f)


    class Handlers {
        var state : State
        var event_queue : seq<Event>
        var event_times : seq<EventTime>
        var last_event_nattime : nat // the arrival time of the last event queued thus far
        var out_queue : seq<Event>
        
        ghost var lastNatTime : nat

        ghost var natTime : nat
        ghost var time : bits

        /******* event time predicates  *******/

        ghost function base_inter_event_time_invariant(eventTimes: seq<EventTime>) : bool
            // if the eventTimes is non-empty, then invariant holding for all the 
            // event times must imply that the invariant holds for the tail of the 
            // event times
            // ensures base_inter_event_time_invariant(eventTimes) ==> 
            ensures (|eventTimes| > 0) ==> base_inter_event_time_invariant(eventTimes) ==>  base_inter_event_time_invariant(eventTimes[1..])
        {
            match |eventTimes| {
                // emtpy queue -- fine
                case 0 => true
                // 1 element in queue -- bit time must be correct
                case 1 => 
                        (eventTimes[0].time == eventTimes[0].natTime % T)
                    &&  base_inter_event_time_invariant(eventTimes[1..])
                // multiple elements in queue -- bit time must be correct and ordering preserved for first two elements
                case _ => 
                        (eventTimes[0].time == eventTimes[0].natTime % T)
                    &&  (eventTimes[0].natTime <= eventTimes[1].natTime)
                    &&  base_inter_event_time_invariant(eventTimes[1..])
            }
        }

        ghost function user_inter_event_time_invariant(eventTimes : seq<EventTime>) : bool
            // the user-provided event timing invariant must preserve the 
            // base event timing invariant
            // ensures (inter_event_time_invariant(eventTimes) ==> base_inter_event_time_invariant(eventTimes))
            ensures (|eventTimes| > 0) ==> user_inter_event_time_invariant(eventTimes) ==> user_inter_event_time_invariant(eventTimes[1..])


        ghost predicate event_timing_invariant(eventTimes : seq<EventTime>)
            reads this`lastNatTime
        {
            base_inter_event_time_invariant(eventTimes)
            && user_inter_event_time_invariant(eventTimes)
            // && (forall i :: 0 <= i < |eventTimes| ==> eventTimes[i].natTime >= lastNatTime)            
            && (|eventTimes| > 0 ==> eventTimes[0].natTime >= lastNatTime)
        } 

        /***  the primary inter-event invariant ***/
        // this should: 
        // always hold on q.pre_handler_contents
        // hold on q.contents before and after handler execution
        ghost predicate inter_event_invariant(s : State, es : seq<Event>, ts : seq<EventTime>, lastNatTime : nat)
            reads s
        
        constructor()
            ensures (fresh(state))
            ensures (this.event_queue == [])
            ensures (|this.event_times| == |this.event_queue|)
            ensures event_timing_invariant(this.event_times)

        //     {
        //      state := new State();   
        //      event_queue := [];
        //      natTime, lastNatTime := 1, 0;
        //      time := 1;
        //     }

        // run the program on the event queue for up to "r" events
        method Run(r : int)
            modifies this.state, this`event_queue, this`out_queue, this`event_times,
            this`lastNatTime, this`natTime, this`time
            requires |event_queue| >  0
            requires |event_queue| == |event_times|
            requires time == event_times[0].time
            requires natTime == event_times[0].natTime
            requires lastNatTime < natTime
            requires event_timing_invariant(event_times)
            requires inter_event_invariant(state, event_queue, event_times, lastNatTime)
        {
            var i := 0;
            assert(inter_event_invariant(state, event_queue, event_times, lastNatTime));
            while(i < r)
            invariant inter_event_invariant(state, event_queue, event_times, lastNatTime)
            invariant |event_queue| == |event_times|
            invariant event_timing_invariant(event_times)
            {
                if (event_queue != []){
                    var e, new_event_queue := dequeue(event_queue);     
                    var et, new_event_times := dequeue(event_times);

                    assert inter_event_invariant(state, event_queue, event_times, lastNatTime);
                    event_queue := new_event_queue;
                    event_times := new_event_times;
                    // before dispatch, time == et.time and natTime == et.natTime
                    time := et.time; 
                    natTime := et.natTime;
                    Dispatch(e, et);
                    lastNatTime := et.natTime;

                }
                i := i + 1;
            }
        }

        // A program must extend this function to handle events in a way that is 
        // consistent with the inter event invariant. 
        // Note that this function is not allowed to modify time variables.
        // dispatch ensures that invariants hold for the state that the system
        // will be in after the current iteration of the run loop completes. 
        // So the system may not yet be in that "state" when dispatch finishes, 
        // but it will be soon.
        method Dispatch(e : Event, t : EventTime)
            modifies this.state, this`event_queue, this`out_queue, this`event_times
            // requires time_invariant()
            requires (inter_event_invariant(state, [e]+event_queue, [t] + event_times, this.lastNatTime))
            requires |event_queue| == |event_times|
            requires event_timing_invariant([t] + event_times)


            ensures |old(this.event_queue)| <= |this.event_queue|
            ensures (old(this.event_queue) == this.event_queue[0..|old(this.event_queue)|])
            ensures inter_event_invariant(state, event_queue, event_times, t.natTime) // CHANGE: this now holds with the _next_ lastNatTime
            ensures |event_queue| == |event_times|
            ensures |old(this.event_times)| <= |this.event_times|
            ensures (old(this.event_times) == this.event_times[0..|old(this.event_times)|])
            ensures |event_times| > 0 ==> t.natTime <= event_times[0].natTime
            // why the above line is here:
            /*
            if |old_event_times| == 0: 
                - et is the time of the last event to be processed
                - lastNatTime <= et.natTime
                - lastNatTime <= event_times[0]
                - we want to say something about et.natTime and event_times
                - but we can't -- there's no relationship
                - any newly-generated event will have time >= lastNatTime                        
                - generate has to set time = cur_time + 1, not lastNatTime + 1
                - what guarantee does that translate to for dispatch? 
                - just that et <= event_times[0] !
            */

            ensures event_timing_invariant(event_times)

        // Queue an event to be processed 1 time-unit after the last event in the queue. 
        method Generate(e : Event)
            modifies this`event_queue
            modifies this`event_times
            requires |event_queue| == |event_times|
            ensures |event_queue| == |event_times|
            ensures (this.event_queue == old(this.event_queue) + [e])
            {
                this.event_queue := this.event_queue + [e];
                var nat_time := if (|event_times| == 0) then 1 else (event_times[|event_times| -1].natTime + 1);
                var time  := if (|event_times| == 0) then 1 else ((event_times[|event_times| -1].time + 1) % T);
                var event_time := EventTime(time, nat_time);
                this.event_times := this.event_times + [event_time];
            }
        // Queue an event to send out into the network.
        // this might be a noop?
        method Send(e : Event) 
            modifies this`out_queue
            ensures out_queue == old(out_queue) + [e]
            {
                out_queue := out_queue + [e];
            }


        // function seq_contains(es : seq<Event>, f : Event -> bool) : bool
        //     {exists e :: f(e) && (e in es)}  
        // NOT NEEDED
        ghost predicate valid_generate(oldq : seq<Event>, newq : seq<Event>)
        {
            ((|oldq| - 1)<= |newq| <= |oldq|)
            && 
            ( 
                // if the oldq had more than 1 element in it, 
                // the tail is the start of newq
                |oldq| > 0 ==> 
                    (oldq[1..] == newq[0..(|oldq|-1)])
            )
            // (|newq| >= |oldq|) && (newq[0..|oldq|] == oldq)
        }

        // private helpers
        method dequeue<T>(es : seq<T>) returns (e : T, es2 : seq<T>)
            requires (|es| > 0)
            ensures (es == [e] + es2)
            {e := es[0]; es2 := es[1..];}
    }
}


