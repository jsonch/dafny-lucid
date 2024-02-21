// This one seems like it will work! 
// Phrasing it as a recursive method
// made it a _lot_ easier to reason about

abstract module LucidBase {
    type bits = x : int | 0 <= x < 256                 // number must match
    const T : nat := 256
    type Event (==)
    datatype LocEvent = LocEvent(e : Event, time : bits, natTime : nat)
    
    class State {
        constructor () 
            ensures fresh(this)
        { }
    }
    class Handlers {


        // state and event queue are mutable for user-facing abstractions
        var state : State
        var queue : seq<LocEvent> // event * timestamp

        var time    : bits // We need time as a class variable because we want an 
                           // imperative way of getting the current time in the program code. 
                           // i.e., in Lucid, we don't "look at the timestamp on the event", 
                           // we call "Sys.time()"
        var natTime : nat
        var lastNatTime : nat

        /***   user-defined predicates   ***/
        // the event "next" is a valid event to come after "cur"
        ghost predicate valid_next_event(cur : LocEvent, next : LocEvent)
        ghost predicate valid_next_events(ev_queue : seq<LocEvent>)
        {
            match |ev_queue| {
                case 0 => true
                case 1 => true
                case _ => 
                   valid_next_event(ev_queue[0], ev_queue[1])
                    && valid_next_events(ev_queue[1..])
            }            
        }
        // the time of event "ev" is valid with respect to some program state "s"
        ghost function valid_event_time(s : State, ev : LocEvent) : bool
            reads s
        ghost function valid_event_times(s : State, ev_queue : seq<LocEvent>) : bool
            reads s
        {
            match |ev_queue| {
                case 0 => true
                case 1 => valid_event_time(s, ev_queue[0])
                case _ => valid_event_time(s, ev_queue[0]) && valid_event_times(s, ev_queue[1..])                
            }
        }

        // pre_dispatch is guaranteed to hold at the beginning of every event handler's execution
        ghost predicate pre_dispatch(s : State, cur_ev : LocEvent, ev_queue : seq<LocEvent>, lastNatTime : nat)
            reads s

        // post_dispatch must hold at the end of every event handler's execution
        // it just says that if the updated queue is not empty, 
        // pre_dispatch holds for the next event on the updated state
        ghost predicate post_dispatch(updated_s : State, updated_queue : seq<LocEvent>, updated_lastNatTime : nat)
            reads updated_s
        {
                |updated_queue| > 0 ==> 
                        pre_dispatch(updated_s, updated_queue[0], updated_queue[1..], updated_lastNatTime)            
        }
        



        // natural and bit representations of timestamps match
        ghost function valid_timestamps(ev_queue : seq<LocEvent>) : bool
        {
            match |ev_queue| {
                case 0 => true
                case 1 => ev_queue[0].time == (ev_queue[0].natTime % T)
                case _ => 
                    ev_queue[0].time == (ev_queue[0].natTime % T)
                    && valid_timestamps(ev_queue[1..])
            }
        }
        ghost function ordered_timestamps(ev_queue : seq<LocEvent>) : bool
        {
            match |ev_queue| {
                case 0 => true
                case 1 => true
                case _ => 
                    ev_queue[0].natTime <= ev_queue[1].natTime
                    && ordered_timestamps(ev_queue[1..])
            }            
        }

        predicate correct_internal_time(cur_ev : LocEvent)
            reads this`natTime, this`time
        {
            this.natTime == cur_ev.natTime
            && this.time    == cur_ev.time
            && this.time    == this.natTime % T            
        }

        // if the queue has at least 2 events, 
        // the second event is a valid event to come after the first
        lemma valid_event_queue_implies_valid_head(ev_queue : seq<LocEvent>)
            requires valid_next_events(ev_queue)
            ensures (match |ev_queue| {
                case 0 => true
                case 1 => true
                case _ => valid_next_event(ev_queue[0], ev_queue[1])})
        lemma valid_event_queue_implies_valid_tail(ev_queue : seq<LocEvent>)
            requires valid_next_events(ev_queue)
            requires |ev_queue| > 0
            ensures valid_next_events(ev_queue[1..])
        lemma valid_queue_append(ev_queue : seq<LocEvent>, ev : LocEvent)
            requires valid_next_events(ev_queue)
            requires |ev_queue| > 0 ==> valid_next_event(ev_queue[|ev_queue|-1], ev)
            ensures valid_next_events(ev_queue + [ev])            

        lemma valid_queue_prepend(ev : LocEvent, ev_queue : seq<LocEvent>)
            requires valid_next_events(ev_queue)
            requires |ev_queue| > 0 ==> valid_next_event(ev, ev_queue[0])
            ensures valid_next_events([ev] + ev_queue)            


        // lemma valid_event_queue_implies_valid_time(ev_queue : seq<LocEvent>)
        //     requires valid_event_queue(ev_queue)
        //     ensures  |ev_queue| > 0 ==> ev_queue[0].time == ev_queue[0].natTime % T

        constructor ()

        method ProcessEvent(i : nat, eq : seq<LocEvent>) returns (j : nat)
            requires |eq| > 0
            requires valid_next_events(eq)
            requires valid_event_times(this.state, eq)
            requires pre_dispatch(this.state, eq[0], eq[1..], lastNatTime)
            requires valid_timestamps(eq)
            requires ordered_timestamps(eq)
            requires lastNatTime <= eq[0].natTime
            requires this.natTime == eq[0].natTime
            requires this.time == eq[0].time
            modifies this`queue, this.state, this`lastNatTime, this`natTime, this`time
        {
            if (i <= 0) {
                j := 0;
            }
            else {
                var ev_head := eq[0];
                var eq_tail := eq[1..];
                this.queue := eq_tail;
                assert pre_dispatch(this.state, ev_head, queue, lastNatTime);                
                Dispatch(ev_head);
                // if the queue is now empty, we are done
                if (queue == []) {
                    j := i-1;
                }
                // the queue is not empty. So we recurse.
                else {
                    // assert valid_event_queue([ev_head] + queue);
                    // prove that the head of the queue is a valid next event 
                    // for event we just processed.
                    valid_event_queue_implies_valid_head([ev_head] + queue);

                    // assert valid_next_event(ev_head, queue[0]);
                    // because of dispatch's implication assertion, the event invariant 
                    // holds for the head of the queue, with the tail of the queue as the new queue.
                    // assert (user_event_invariant(this.state, this.queue[0], this.queue[1..]));
                    // also, because dispatch guarantees that the 
                    // sequence [event_just_processed] + new_event_queue
                    // is a valid sequence, we know that the new event queue 
                    // by itself is a valid sequence
                    valid_event_queue_implies_valid_tail([ev_head]+queue);
                    // assert valid_event_queue(queue);
                    // assert valid_event_queue(queue[1..]);
                    // so now we can just update the times and recurse!
                    this.lastNatTime := natTime;
                    this.natTime := queue[0].natTime;
                    this.time := queue[0].time;
                    j := ProcessEvent(i-1, this.queue);
                }
            }
        }

        method Dispatch(cur_ev : LocEvent)
            modifies this.state, this`queue
            requires correct_internal_time(cur_ev)

            requires valid_timestamps([cur_ev] + queue)
            requires ordered_timestamps([cur_ev] + queue)
            requires valid_event_times(this.state, [cur_ev] + this.queue)    
            requires valid_next_events([cur_ev] + this.queue)
            requires pre_dispatch(this.state, cur_ev, this.queue, this.lastNatTime)

            ensures valid_timestamps([cur_ev] + queue)
            ensures ordered_timestamps([cur_ev] + queue)
            ensures valid_next_events([cur_ev] + this.queue)
            ensures valid_event_times(this.state, [cur_ev] + this.queue)
            ensures post_dispatch(state, queue, natTime)
            // alternative post_dispatch: 
            // ensures (
            //     |queue| > 0 ==> 
            //         (forall ev : LocEvent | valid_next_event(cur_ev, ev) :: inter_event_invariant(this.state, ev, this.queue[1..], cur_ev.natTime))
            // )



        function next_generate_time(cur_natTime : nat, q : seq<LocEvent>) : nat
        {
            match (|q|) {
                case 0 => cur_natTime
                case _ => q[(|q|-1)].natTime
            }
        }

        var gen__out_natTime : nat
        // TODO: the verification in generate is complicated and somewhat disorganized. 
        // How much is necessary?
        method Generate(cur_ev : LocEvent, e : Event, out_natTime : nat)
            requires valid_next_events([cur_ev]+queue)
            // if the queue is non-empty, then this is a valid event to attach at the end of it
            requires |queue| > 0 ==> valid_next_event(queue[|queue|-1], LocEvent(e, out_natTime % T, out_natTime))
            // if the queue is empty, the event is valid to arrive immediately after the current event
            requires |queue| == 0 ==> valid_next_event(cur_ev, LocEvent(e, out_natTime % T, out_natTime))
            modifies this`queue
            ensures valid_next_events([cur_ev] + queue)
            // ensures valid_event_queue_implies_valid_head([cur_ev] + this.queue)
        {
            var out_ev   := LocEvent(e, out_natTime % T, out_natTime);
            // how do we know that this random event is a valid next event, 
            // we don't know what the condition is.
            assert (|queue| > 0 ==> valid_next_event(queue[|queue|-1], out_ev)  );

            var new_queue   := queue + [out_ev];
            valid_event_queue_implies_valid_tail([cur_ev]+queue);                        
            valid_queue_append(queue, out_ev);
            valid_event_queue_implies_valid_head([cur_ev] + queue);
            assert |queue| > 0 ==> valid_next_event(cur_ev, queue[0]);
            queue := new_queue;
            assert valid_next_event(cur_ev, queue[0]);
            assert valid_next_events(queue);
            valid_queue_prepend(cur_ev, queue);
            assert valid_next_events([cur_ev] + queue);
            // we've changed the queue. So we have to prove that the condition still holds.                         
            valid_event_queue_implies_valid_head([cur_ev] + this.queue);


        }
    }



}