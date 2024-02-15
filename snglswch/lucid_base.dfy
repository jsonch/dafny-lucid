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
    1. figure out how to express the invariant "there's only ever one event matching f(e) in the queue"
    2. add in arrays + memops
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
        
        // time-related state
        var time : bits
        ghost var natTime : nat
        ghost var lastNatTime : nat

        /******* event time predicates  *******/

        ghost predicate TimeIsNonDecreasing(eventTimes: seq<EventTime>)
        // natural event times are non decreasing
        {
            forall i :: 1 <= i < |eventTimes| ==> eventTimes[i].natTime >= eventTimes[i - 1].natTime
        }    
        ghost predicate TimestampIsCorrect(eventTimes: seq<EventTime>)
        // bit event time equals natural event time mod T
        {
            forall i :: 0 <= i < |eventTimes| ==> eventTimes[i].time == eventTimes[i].natTime % T   
        }
        ghost predicate TimeEqNatTime(time : bits, natTime : nat) {
            time == natTime % T
        }
        ghost predicate NatTimeOrder(natTime1 : nat, natTime2 : nat) {
            natTime1 <= natTime2
        }

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
        {
            base_inter_event_time_invariant(eventTimes)
            && user_inter_event_time_invariant(eventTimes)
        } 

        // this should: 
        // always hold on q.pre_handler_contents
        // hold on q.contents before and after handler execution
        ghost predicate inter_event_invariant(s : State, es : seq<Event>, time : bits, natTime : nat, lastNatTime : nat)
            reads s

        // ghost predicate time_invariant()
        //     reads this`time, this`natTime, this`lastNatTime

        // ghost predicate queue_invariant(s : State, es : seq<Event>, time : bits, natTime : nat, lastNatTime : nat)
        //     reads this`event_queue
        //     ensures inter_event_invariant(s, es, time, natTime, lastNatTime)


        constructor()
            ensures (fresh(state))
            ensures (this.event_queue == [])
            ensures time == natTime % T
            ensures natTime >= lastNatTime
            ensures (|this.event_times| == |this.event_queue|)
            ensures event_timing_invariant(this.event_times)

            // ensures time_invariant()
        //     // ensures (inter_event_invariant(state, event_queue))
        //     // ensures (empty_implies_inter(state, event_queue))
        //     {
        //      state := new State();   
        //      event_queue := [];
        //      natTime, lastNatTime := 1, 0;
        //      time := 1;
        //     }

        // the next queued event doesn't run before the current time
        ghost predicate next_event_is_later(ev_times : seq<EventTime>)
        reads this`natTime
        {
            match |ev_times| {
                case 0 => true
                case _ => ev_times[0].natTime >= natTime
            }
        }    
        // run the program on event e and up to "r" recirculated events
        method Run(e : Event, r : int)
            modifies this.state, this`event_queue, this`out_queue, this`event_times,
            this`natTime, this`time, this`lastNatTime
            requires |event_queue| == |event_times|
            requires time == natTime % T
            requires natTime >= lastNatTime
            requires next_event_is_later(event_times)
            requires event_timing_invariant(event_times)
            requires inter_event_invariant(state, event_queue, this.time, this.natTime, this.lastNatTime)
        {
            var i := 0;
            assert(inter_event_invariant(state, event_queue, this.time, this.natTime, this.lastNatTime));
            // assert time_invariant();
            while(i < r)
            invariant inter_event_invariant(state, event_queue, this.time, this.natTime, this.lastNatTime)
            invariant time == natTime % T
            invariant natTime >= lastNatTime
            invariant |event_queue| == |event_times|
            invariant event_timing_invariant(event_times)
            // invariant next_event_is_later(event_times)
            {
                // call the user-defined "Dispatch" function to handle the event. 
                // the effects of dispatch are to: 
                // 1. change state values; 2. change queue contents (current event gets dequeued automatically, more may be added by generate).
                if (event_queue != []){
                    // assert event_timing_invariant(event_times);
                    var e, new_event_queue := dequeue(event_queue);     
                    var et, new_event_times := dequeue(event_times);
                    /*
                        inter_event_inv(events, time) ==> 
                            // the inter event invariant starts with the current event before dispatch, 
                            // and the next event after dispatch. 

                    */
                    assert(inter_event_invariant(state, event_queue, this.time, this.natTime, this.lastNatTime));
                    // assert(inter_event_invariant(state, event_queue, et.time, et.natTime, this.natTime));
                    // assert inter_event_time_invariant(new_event_times);  
                    // update time vars
                    // lastNatTime := natTime;
                    // natTime := et.natTime;
                    // time := et.time;
                    assert time == natTime % T;
                    assert(inter_event_invariant(state, event_queue, this.time, this.natTime, this.lastNatTime));
                    event_queue := new_event_queue;
                    event_times := new_event_times;
                    // assert event_timing_invariant(event_times);
                    // assert events_run_later(event_times);
                    // assert inter_event_time_invariant(event_times);  
                    Dispatch(e, et);

                }
                i := i + 1;
            }
        }

        // A program must extend this function to handle events in a way that is 
        // consistent with the inter event invariant. 
        // Note that this function is not allowed to modify time variables.
        method Dispatch(e : Event, t : EventTime)
            modifies this.state, this`event_queue, this`out_queue, this`event_times
            // requires time_invariant()
            requires time == natTime % T
            requires natTime >= lastNatTime
            requires |event_queue| == |event_times|
            requires event_timing_invariant(event_times)
            requires (inter_event_invariant(state, [e]+event_queue, this.time, this.natTime, this.lastNatTime))
            // requires  next_event_is_later([t] + event_times)
            // ensures time_invariant()
            ensures event_timing_invariant(event_times)
            ensures time == natTime % T
            ensures natTime >= lastNatTime
            ensures |event_queue| == |event_times|
            // ensures inter_event_time_invariant(event_times)
            ensures inter_event_invariant(state, event_queue, this.time, this.natTime, this.lastNatTime)
            // ensures valid_generate(old(event_queue), event_queue)

        // The program has to exend this function to update the clock in a way that 
        // is consistent with its invariant.
        // method ClockTick()
        //     modifies this`time, this`natTime, this`lastNatTime
        //     requires time_invariant()
        //     requires inter_event_invariant(state, event_queue, this.time, this.natTime, this.lastNatTime)
        //     ensures time_invariant()
        //     ensures  inter_event_invariant(state, event_queue, this.time, this.natTime, this.lastNatTime)


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


