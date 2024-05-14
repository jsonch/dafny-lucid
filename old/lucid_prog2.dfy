/* 
    a non-trivial interpacket invariant, which demands 
    that the counter starts at 0 and then is toggled between 
    0 and 1 with an alternating sequence of SetZero and SetOne
    events. 
*/
include "lucid_base.dfy"

module LucidProg refines LucidBase {
    // 1. Define events as constructors for the "Event" datatype
    datatype Event = 
        | SetOne()
        | SetZero()

    // 2. Define program state by refining the state class.
    class State ... {
        var counter : int
        constructor() 
            ensures (this.counter == 0)
            ensures (fresh(this))
        {
            counter := 0;
        }
    }
    // 3. Define event handlers by refining the handlers class.
    class Handlers ... {        

        method setOne(e: Event)
            requires (e.SetOne?)
            modifies state, `event_queue, `out_queue
            requires (inter_event_invariant(state, [e]+event_queue))
            ensures (inter_event_invariant(state, event_queue))
            ensures (valid_generate(old(event_queue), event_queue))
        {
            state.counter := 1;
            Generate(SetZero());
        }
        method setZero(e: Event)
            requires (e.SetZero?)
            modifies state, `event_queue, `out_queue
            requires (inter_event_invariant(state, [e]+event_queue))
            ensures (inter_event_invariant(state, event_queue))
            ensures (valid_generate(old(event_queue), event_queue))
        {
            state.counter := 0;
            Generate(SetOne());
        }


        method Dispatch(e : Event)
        {
            if
                case e.SetOne? => setOne(e);
                case e.SetZero? => setZero(e);
        }
        /* The cool part: 
            this invariant says that the counter should start at 0, 
            toggle between 0 -> 1 -> 0 -> ... with a pattern of strictly 
            alternating SetOne and SetZero events, and the counter should 
            end on Zero when all the events are processed. 
            - if there are no events in the queue, the counter should be 0
            - if there's one event in the queue, and its a SetZero, the counter should be 1
            - if there's one event in the queue, and its a SetOne, the counter should be 0
            - there should never be more than 1 event in the queue */

        ghost predicate inter_event_invariant(s : State, es : seq<Event>)
        {   
            match |es| {
                case 0 => s.counter == 0
                case 1 => (
                    match es[0] {
                        case SetZero() => (s.counter == 1)
                        case SetOne() => (s.counter == 0)
                    }
                )
                case _ => false
            }
        }
        constructor()
            ensures (inter_event_invariant(state, event_queue))            
    }
}

method Main() {
    var prog := new LucidProg.Handlers();
    var input_event := LucidProg.SetOne();
    prog.Run(input_event, 10);
}
