/*  1/31/24
    This module encodes the semantics of event-based processing in Lucid. 
    To write a Lucid-compatible Dafny program, extend this module 
    with a concrete implementation that defines: 
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
    type Event(==)

    class State {
        constructor () 
            ensures fresh(this)
        { }
    }

    class Handlers {
        var state : State
        var event_queue : seq<Event>
        var out_queue : seq<Event>
        constructor()
            ensures (fresh(state))
            ensures (this.event_queue == [])
            // ensures (inter_event_invariant(state, event_queue))
            // ensures (empty_implies_inter(state, event_queue))
            {                
             state := new State();   
             event_queue := [];
            }
            
        // this should: 
        // always hold on q.pre_handler_contents
        // hold on q.contents before and after handler execution
        ghost predicate inter_event_invariant(s : State, es : seq<Event>)
            reads s

        // Dispatch is the entry point. It parses the event and calls the appropriate handler.
        // It must be extended by the user to handle the events that they have defined. 
        method Dispatch(e : Event)
            // Important: these modify clauses limit the user's ability to modify the state of the program. 
            // specifically, they can't modify the input queue, only the output queue.
            modifies this.state, this`event_queue, this`out_queue
            requires (inter_event_invariant(state, [e]+event_queue))
            ensures inter_event_invariant(this.state, event_queue)
            ensures valid_generate(old(event_queue), event_queue)

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
            // 
            modifies this`out_queue
            {
                out_queue := out_queue + [e];
            }


        // run the program on event e and up to "r" recirculated events
        method Run(e : Event, r : int)
            modifies this.state, this`event_queue, this`out_queue
            requires |event_queue| == 0
            requires inter_event_invariant(state, [e])
        {
            var i := 0;
            event_queue := [e];
            while(i < r)
            invariant inter_event_invariant(state, event_queue)
            {
                if (event_queue != []){
                    // the main execution loop is basically: 
                    // 1. dequeue an event
                    // 2. dispatch the event, calling the appropriate handler
                    // 3. push any generated events back onto the queue
                    // we have to structure the code carefully to maintain the inter-event invariant.
                    ghost var pre_dequeue := event_queue;
                    var e, new_event_queue := dequeue(event_queue);        
                    assert (pre_dequeue == [e] + new_event_queue);
                    assert (inter_event_invariant(state, pre_dequeue));                    
                    assert (inter_event_invariant(state, [e]+new_event_queue));
                    event_queue := new_event_queue;
                    assert (inter_event_invariant(state, [e]+event_queue));
                    Dispatch(e);
                    // now, we have some generated events on output. 
                    // Push them back to the input and make sure the invariant holds. 
                    assert (inter_event_invariant(state, event_queue));
            }
                i := i + 1;
            }
        }

        // misc helpers 
        function seq_contains(es : seq<Event>, f : Event -> bool) : bool
            {exists e :: f(e) && (e in es)}  
        ghost predicate valid_generate(oldq : seq<Event>, newq : seq<Event>)
        {
            (|newq| >= |oldq|) && (newq[0..|oldq|] == oldq)
        }

        // private helpers
        method dequeue(es : seq<Event>) returns (e : Event, es2 : seq<Event>)
            requires (|es| > 0)
            ensures (es == [e] + es2)
            {e := es[0]; es2 := es[1..];}
    }
}


