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
    // not gameOver[pre]
    // ACTION
    post.count = add[numUp, pre.count] // How Many Numbers They Count Up
    post.player != pre.player // Next State Must Have the Next Player
}


// pred doNothing[pre: State, post: State] {
//     gameOver[pre] -- guard of the transition
//     pre.board = post.board -- effect of the transition
// }



pred loser[s: State, p: Player] {
    s.count = 21
    s.player = p
}

// gameOver[s: State] {
//   some p: Player | winner[s, p]
// }


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

// pred traces {
//     -- The trace starts with an initial state
//     starting[Game.initialState]
//     no sprev: State | sprev.next = Game.initialState
//     -- Every transition is a valid move
//     all s: State | some Game.next[s] implies {
//       some row, col: Int, p: Player | {
//         move[s, row, col, p, Game.next[s]] 
//       }
//       or
//       doNothing[s, Game.next[s]]      
//     } 
// }


run {
    wellformed
    traces
} for exactly 21 State, 6 Int for {next is linear}