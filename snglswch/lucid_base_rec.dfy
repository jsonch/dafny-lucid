// This one seems like it will work! 
// Phrasing it as a recursive method
// made it a _lot_ easier to reason about

abstract module LucidBase {
    type bits = x : int | 0 <= x < 256                 // number must match
    const T : nat := 256
    type Event (==)
    datatype LocEvent = LocEvent(e : Event, time : bits, natTime : nat)

    class GState {
        ghost constructor ()
            ensures fresh(this)
        { }
    }

    class State {
        constructor () 
            ensures fresh(this)
        { }
    }
    class Handlers {


        // state and event queue are mutable for user-facing abstractions
        var state : State
        ghost var gState : GState
        var queue : seq<LocEvent> // event * timestamp

        var time    : bits // We need time as a class variable because we want an 
                           // imperative way of getting the current time in the program code. 
                           // i.e., in Lucid, we don't "look at the timestamp on the event", 
                           // we call "Sys.time()"
        var natTime : nat
        var lastNatTime : nat

        /***   user-defined predicates   ***/
        // an invariant over the last event that was processed, the current event, and the remaining events
        ghost predicate inter_event_invariant(s : State, gs : GState, cur_ev : LocEvent, ev_queue : seq<LocEvent>, lastNatTime : nat)
            reads s, gs

        // post_dispatch must hold at the end of every event handler's execution
        ghost predicate post_dispatch(s : State, gs : GState, updated_queue : seq<LocEvent>, processed_event_natTime : nat)
            reads s, gs
        {
                |updated_queue| > 0 ==> 
                        inter_event_invariant(s, gs, updated_queue[0], updated_queue[1..], processed_event_natTime)            
        }
        // a predicate that must hold over the entire event queue before and after 
        // dispatch, that defines the pairs of events that we may see
        ghost predicate valid_next_event(cur : LocEvent, next : LocEvent)
        

        ghost predicate valid_event_queue(ev_queue : seq<LocEvent>)
        {
            (forall i | 1 <= i < |ev_queue| :: (
                valid_next_event(ev_queue[i-1], ev_queue[i])
                && ev_queue[i-1].natTime <= ev_queue[i].natTime)
            )
            && 
            (forall i | 0 <= i < |ev_queue| - 1 :: 
                ev_queue[i].time == (ev_queue[i].natTime % T))
        }

        // if the queue has at least 2 events, 
        // the second event is a valid event to come after the first
        lemma valid_event_queue_implies_valid_head(ev_queue : seq<LocEvent>)
            requires valid_event_queue(ev_queue)
            ensures (match |ev_queue| {
                case 0 => true
                case 1 => true
                case _ => valid_next_event(ev_queue[0], ev_queue[1])})
        lemma valid_event_queue_implies_valid_tail(ev_queue : seq<LocEvent>)
            requires valid_event_queue(ev_queue)
            requires |ev_queue| > 0
            ensures valid_event_queue(ev_queue[1..])
        lemma valid_queue_append(ev_queue : seq<LocEvent>, ev : LocEvent)
            requires valid_event_queue(ev_queue)
            requires |ev_queue| > 0 ==> valid_next_event(ev_queue[|ev_queue|-1], ev)
            ensures valid_event_queue(ev_queue + [ev])            

        lemma valid_queue_prepend(ev : LocEvent, ev_queue : seq<LocEvent>)
            requires valid_event_queue(ev_queue)
            requires |ev_queue| > 0 ==> valid_next_event(ev, ev_queue[0])
            ensures valid_event_queue([ev] + ev_queue)            

        lemma valid_event_queue_implies_valid_time(ev_queue : seq<LocEvent>)
            requires valid_event_queue(ev_queue)
            ensures  |ev_queue| > 0 ==> ev_queue[0].time == ev_queue[0].natTime % T

        constructor ()

        method ProcessEvent(i : nat, eq : seq<LocEvent>) returns (j : nat)
            requires |eq| > 0
            requires valid_event_queue(eq)
            requires inter_event_invariant(this.state, this.gState, eq[0], eq[1..], lastNatTime)
            requires lastNatTime <= eq[0].natTime
            requires this.natTime == eq[0].natTime
            requires this.time == eq[0].time
            modifies this`queue, this.state, this`lastNatTime, this`natTime, this`time, this.gState
        {
            
            valid_event_queue_implies_valid_time(eq);
            assert (eq[0].time == eq[0].natTime % T);
            if (i <= 0) {
                j := 0;
            }
            else {
                var ev_head := eq[0];
                var eq_tail := eq[1..];
                this.queue := eq_tail;
                assert inter_event_invariant(this.state, this.gState, ev_head, queue, lastNatTime);                
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

        predicate correct_internal_time(cur_ev : LocEvent)
            reads this`natTime, this`time
        {
            this.natTime == cur_ev.natTime
            && this.time    == cur_ev.time
            && this.time    == this.natTime % T            
        }
        method Dispatch(cur_ev : LocEvent)
            modifies this.state, this.gState, this`queue
            // at the start of dispatch, the user event invariant must hold for the current event
            requires inter_event_invariant(this.state, this.gState, cur_ev, this.queue, this.lastNatTime)
            // and the event must be part of a valid sequence of events
            requires valid_event_queue([cur_ev] + this.queue)
            requires correct_internal_time(cur_ev)
            requires this.natTime >= this.lastNatTime
            // after processing, if the queue has more items in it to process, 
            // then the user event invariant holds over:
            //   - the new state
            //   - any event ev that is a valid next event from the current event
            //   - the queue of remaining packets after the first one
            // essentially, this is saying: 
            //   no matter what the next event is, the invariant will hold in 
            //   the current state and the remaining event queue
            // ensures (
            //     |queue| > 0 ==> 
            //         (forall ev : LocEvent | valid_next_event(cur_ev, ev) :: inter_event_invariant(this.state, ev, this.queue[1..], cur_ev.natTime))
            // )
            /* 
                maybe we can do something weaker / simpler: 
                if there's an event in the queue, then it must be a valid next event and the inter-event invariant must hold?
            */
            ensures post_dispatch(state, gState, queue, natTime)
            // and the event must still be part of a valid sequence of events
            // is this necessary any more?
            ensures  valid_event_queue([cur_ev] + this.queue)


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
            requires valid_event_queue([cur_ev]+queue)
            // if the queue is non-empty, then this is a valid event to attach at the end of it
            requires |queue| > 0 ==> valid_next_event(queue[|queue|-1], LocEvent(e, out_natTime % T, out_natTime))
            // if the queue is empty, the event is valid to arrive immediately after the current event
            requires |queue| == 0 ==> valid_next_event(cur_ev, LocEvent(e, out_natTime % T, out_natTime))
            modifies this`queue
            ensures valid_event_queue([cur_ev] + queue)
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
            assert valid_event_queue(queue);
            valid_queue_prepend(cur_ev, queue);
            assert valid_event_queue([cur_ev] + queue);
            // we've changed the queue. So we have to prove that the condition still holds.                         
            valid_event_queue_implies_valid_head([cur_ev] + this.queue);


        }
    }



}