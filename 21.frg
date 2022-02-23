#lang forge/bsl "cm" "spx27018"

// Player
abstract sig Player {}
one sig P1, P2 extends Player {}

// Board
sig State {
    count: one Int,
    player: one Player
}

// Game
one sig Game {
    next: pfunc State -> State,
    initialState: one State
}

pred wellformed {
    all s: State | {
        s.count >= 0 and s.count <= 21
    }
}

pred starting[s: State] {
    s.count = 0
    s.player = P2 // Person To Say s.count
}

pred P1Turn[s: State] {
    s.player = P2
}

pred P2Turn[s: State] {
    s.player = P1
}

pred move[pre: State, numUp: Int, p: Player, post: State] {
    // GUARD
    p = P1 implies P1Turn[pre]
    p = P2 implies P2Turn[pre]
    numUp >= 1 and numUp <= 3
    // ACTION
    post.count = add[numUp, pre.count] // How Many Numbers They Count Up
    post.player != pre.player // Next State Must Have the Next Player
}

pred loser[s: State, p: Player] {
    s.count = 21
    s.player = p
}

pred traces {
    -- initial board is a starting board (rules of 21)
    starting[Game.initialState]
    -- initial board is initial in the sequence (trace)
    not (some sprev: State | Game.next[sprev] = Game.initialState)
    --"next” enforces move predicate (valid transitions!)
    all s: State | {
        some Game.next[s] implies {
            some num: Int, p: Player | move[s, num, p, Game.next[s]]
        }
    } 
}

run {
    wellformed
    traces
} for exactly 21 State, 6 Int for {next is linear}