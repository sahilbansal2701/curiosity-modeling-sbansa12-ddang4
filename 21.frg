sig State {

}

pred ValidStates {

}

pred initState[s: State] {

}

pred finalState[s: State] {

}


pred move[pre: State, post: State] {

}

pred TransitionStates {
    // TODO: Fill me in!
    some init, final: State {
        -- constrains on init state
        initState[init]
        all s: State | (s != init) => s.next != init
        -- constraints on final state
        finalState[final]
        final.next = none
        -- link init to final state via gwnext
        reachable[final, init, next]
        -- valid transitions
        all s: State | {
            some s.next => move[s, s.next]
        }
    }
}

run {
    ValidStates
    TransitionStates
} for exactly ??? for {next is linear}