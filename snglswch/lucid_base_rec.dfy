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
    class Handlers { // maybe should be "prog" or something. Not just handlers, really.


        // state and event queue are mutable for user-facing abstractions
        var state : State
        var queue : seq<LocEvent> // event * timestamp
        var natTime : nat
        var lastNatTime : nat

        /***   user-defined predicates   ***/
        // an invariant over the last event that was processed, the current event, and the remaining events
        ghost predicate inter_event_invariant(s : State, cur_ev : LocEvent, ev_queue : seq<LocEvent>, lastNatTime : nat)
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

        lemma valid_event_queue_implies_valid_head(ev_queue : seq<LocEvent>)
            requires valid_event_queue(ev_queue)
            requires |ev_queue| > 1
            ensures valid_next_event(ev_queue[0], ev_queue[1])

        lemma valid_event_queue_implies_valid_tail(ev_queue : seq<LocEvent>)
            requires valid_event_queue(ev_queue)
            requires |ev_queue| > 1
            ensures valid_event_queue(ev_queue[1..])

        constructor ()

        method ProcessEvent(i : nat, eq : seq<LocEvent>) returns (j : nat)
            requires |eq| > 0
            requires valid_event_queue(eq)
            requires inter_event_invariant(this.state, eq[0], eq[1..], lastNatTime)
            requires lastNatTime <= eq[0].natTime
            requires this.natTime == eq[0].natTime
            modifies this`queue, this`state, this`lastNatTime, this`natTime
        {
            if (i <= 0) {
                j := 0;
            }
            else {
                var ev_head := eq[0];
                var eq_tail := eq[1..];
                this.queue := eq_tail;
                assert inter_event_invariant(this.state, ev_head, queue, lastNatTime);                
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
                    j := ProcessEvent(i-1, this.queue);
                }
            }
        }


        method Dispatch(cur_ev : LocEvent)
            modifies this`state, this`queue
            // at the start of dispatch, the user event invariant must hold for the current event
            requires inter_event_invariant(this.state, cur_ev, this.queue, this.lastNatTime)
            // and the event must be part of a valid sequence of events
            requires valid_event_queue([cur_ev] + this.queue)
            // after processing, if the queue has more items in it to process, 
            // then the user event invariant holds over:
            //   - the new state
            //   - any event ev that is a valid next event from the current event
            //   - the queue of remaining packets after the first one
            // essentially, this is saying: 
            //   no matter what the next event is, the invariant will hold in 
            //   the current state and the remaining event queue
            ensures (
                |queue| > 0 ==> 
                    (forall ev : LocEvent | valid_next_event(cur_ev, ev) :: inter_event_invariant(this.state, ev, this.queue[1..], cur_ev.natTime))
            )
            // and the event must still be part of a valid sequence of events
            ensures  valid_event_queue([cur_ev] + this.queue)




    }

}