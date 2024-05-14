/* 
user code 
*/
include "lucid_base.dfy"

module LucidProg refines LucidBase {
    // 1. Define events as constructors for the "Event" datatype
    datatype Event = 
        | ProcessPacket(addr : int)

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

        method processPacket(e: Event)
            requires (e.ProcessPacket?)
            modifies state, `event_queue, `out_queue
            requires (inter_event_invariant(state, [e]+event_queue))
            ensures (inter_event_invariant(state, event_queue))
            ensures (valid_generate(old(event_queue), event_queue))
        {
            state.counter := state.counter + 1;
            Send(e);
        }
        method Dispatch(e : Event)
        {
            if
                case e.ProcessPacket? => processPacket(e);
        }
        // the inter-event variant doesn't matter for this program
        ghost predicate inter_event_invariant(s : State, es : seq<Event>)
        {true}

    }
}

method Main() {
    var prog := new LucidProg.Handlers();
    var input_event := LucidProg.ProcessPacket(1);
    prog.Run(input_event, 10);
}
