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

    type Event(==)

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
        var out_queue : seq<Event>
        
        // time-related state
        var time : bits
        ghost var natTime : nat
        ghost var lastNatTime : nat
        
        constructor()
            ensures (fresh(state))
            ensures (this.event_queue == [])
            ensures time_invariant()
        //     // ensures (inter_event_invariant(state, event_queue))
        //     // ensures (empty_implies_inter(state, event_queue))
        //     {
        //      state := new State();   
        //      event_queue := [];
        //      natTime, lastNatTime := 1, 0;
        //      time := 1;
        //     }
            
        // this should: 
        // always hold on q.pre_handler_contents
        // hold on q.contents before and after handler execution
        ghost predicate inter_event_invariant(s : State, es : seq<Event>)
            reads s
            reads this`time, this`natTime, this`lastNatTime

        ghost predicate time_invariant()
            reads this`time, this`natTime, this`lastNatTime


        // A program must extend this function to handle events in a way that is 
        // consistent with the inter event invariant. 
        // Note that this function is not allowed to modify time variables.
        method Dispatch(e : Event)
            modifies this.state, this`event_queue, this`out_queue
            requires time_invariant()
            requires (inter_event_invariant(state, [e]+event_queue))
            ensures time_invariant()
            ensures inter_event_invariant(state, event_queue)
            // ensures valid_generate(old(event_queue), event_queue)

        // The program has to exend this function to update the clock in a way that 
        // is consistent with its invariant.
        method ClockTick()
            modifies this`time, this`natTime, this`lastNatTime
            requires time_invariant()
            requires inter_event_invariant(state, event_queue)
            ensures time_invariant()
            ensures  inter_event_invariant(state, event_queue)


        // Queue an event to be processed in the future. 
        method Generate(e : Event)
            modifies this`event_queue
            ensures (this.event_queue == old(this.event_queue) + [e])
            {
                this.event_queue := this.event_queue + [e];
            }
        // Queue an event to send out into the network.
        // I think this might be a noop.
        method Send(e : Event) 
            modifies this`out_queue
            ensures out_queue == old(out_queue) + [e]
            {
                out_queue := out_queue + [e];
            }

        // run the program on event e and up to "r" recirculated events
        method Run(e : Event, r : int)
            modifies this.state, this`event_queue, this`out_queue, 
            this`natTime, this`time, this`lastNatTime
            requires inter_event_invariant(state, event_queue)
            requires time_invariant()
        {
            var i := 0;
            assert(inter_event_invariant(state, event_queue));
            assert time_invariant();
            while(i < r)
            invariant inter_event_invariant(state, event_queue)
            invariant time_invariant()
            {
                // first, call the user-defined "Dispatch" function to handle the event. 
                // the effects of dispatch are to: 
                // 1. change state values; 2. change queue contents (current event gets dequeued automatically, more may be added by generate).
                if (event_queue != []){
                    var e, new_event_queue := dequeue(event_queue);        
                    event_queue := new_event_queue;
                    Dispatch(e);
                }
                // now, call the user function to update time in a
                // way that is consistent with the program's assumptions
                ClockTick();
                i := i + 1;
            }
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
        method dequeue(es : seq<Event>) returns (e : Event, es2 : seq<Event>)
            requires (|es| > 0)
            ensures (es == [e] + es2)
            {e := es[0]; es2 := es[1..];}
    }
}


