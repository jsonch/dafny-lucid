/* 
    starting to model filtering from the self-driving firewall
*/
include "lucid_base.dfy"

module LucidProg refines LucidBase {
    // 1. Define events as constructors for the "Event" datatype
    datatype Event = 
        | ProcessReply(addr : int)
        | SetFiltering(addr : int, newval: bool)

    // 2. Define program state by refining the state class.
    class State ... {
        var filtering : bool
        var recircPending : bool
        constructor() 
            ensures (this.filtering == false)
            ensures (this.recircPending == false)
            ensures (fresh(this))
        {
            filtering, recircPending := false, false;
        }
    }
    // 3. Define event handlers by refining the handlers class.
    class Handlers ... {        

        method processReply(e: Event)
            requires (e.ProcessReply?)
            modifies state, `event_queue
            requires (inter_event_invariant(state, [e]+event_queue))
            ensures (inter_event_invariant(state, event_queue))
            ensures (valid_generate(old(event_queue), event_queue))
        {
            // processreply generates a setfiltering if state.filtering is false and recircpending is false.
            // if we are not filtering, and there is no SetFilter event pending, start filtering
            if (state.filtering == false) {
                print ("handling processReply -- requesting to start filtering\n");
                if (state.recircPending == false) {
                    state.recircPending := true;
                    var new_e := SetFiltering(e.addr, true);
                    assert (is_setfiltering_true(new_e));
                    Generate(new_e);
                }
                else { }
            } 
            else {
                if (state.recircPending == true) { } 
                else{ }
            }
        }
        method setFiltering(e:Event)
            requires e.SetFiltering?
            modifies state
            requires (inter_event_invariant(state, [e]+event_queue))

            ensures (inter_event_invariant(state, event_queue))
            ensures (valid_generate(old(event_queue), event_queue))
        {            
            print ("handling setFiltering -- turning off recircPending guard.\n");
            state.filtering := e.newval;
            state.recircPending := false;
        }

        method Dispatch(e : Event)
        {
            if
                case e.ProcessReply? => processReply(e);
                case e.SetFiltering? => setFiltering(e);
        }

        // Inside the handlers class, the first verification-related task is to 
        // define an inter-event invariant -- a predicate over the state of the program 
        // (mutable state and the event queue) that is preserved by the handlers.
        ghost predicate inter_event_invariant(s : State, es : seq<Event>)
        {
            // a simple example: when the semaphore is set, the queue contains a setfiltering.
            ((s.recircPending == true) ==> seq_contains(es, is_setfiltering_true))
        }


        ghost function is_setfiltering_true(e : Event) : bool {
            match e {
                case SetFiltering(_, true) => true
                case _ => false
            }
        }

        // Extend the constructor to ensure that the inter-event invariant 
        // holds at startup.
        constructor()
            ensures (inter_event_invariant(state, event_queue))


    }
}

method Main() {
    var prog := new LucidProg.Handlers();
    var input_event := LucidProg.ProcessReply(1);
    prog.Run(input_event, 10);
}
