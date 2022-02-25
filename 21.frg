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
    s.player = P2 // Person to say s.count
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
    add[numUp, pre.count] < 22
    not gameOver[pre]

    // ACTION
    post.count = add[numUp, pre.count] // How many numbers they count up
    post.player != pre.player // Next state must have the next player
}

// Strategic Move P2
pred strategicMove[pre: State, numUp: Int, p: Player, post: State] {
    // GUARD
    p = P1 implies P1Turn[pre]
    p = P2 implies P2Turn[pre]
    numUp >= 1 and numUp <= 3
    add[numUp, pre.count] < 22
    not gameOver[pre]

    // ACTION
    p = P2 => remainder[add[numUp, pre.count], 4] = 0
    post.count = add[numUp, pre.count] // How many numbers they count up
    post.player != pre.player // Next state must have the next player
}

pred loser[s: State, p: Player] {
    s.count = 21
    s.player = p
}

pred gameOver[s: State] {
  some p: Player | loser[s, p]
}

pred doNothing[pre: State, post: State] {
    gameOver[pre] -- guard of the transition
    pre.count = post.count -- effect of the transition
    pre.player = post.player
}

pred traces {
    -- initial board is a starting board (rules of 21)
    starting[Game.initialState]
    -- initial board is initial in the sequence (trace)
    not (some sprev: State | Game.next[sprev] = Game.initialState)
    --"next” enforces move predicate (valid transitions!)
    all s: State | {
        some Game.next[s] implies {
            (some num: Int, p: Player | move[s, num, p, Game.next[s]])
            or
            (doNothing[s, Game.next[s]])
        }
        
    }
}

pred tracesStrategic {
    -- initial board is a starting board (rules of 21)
    starting[Game.initialState]
    -- initial board is initial in the sequence (trace)
    not (some sprev: State | Game.next[sprev] = Game.initialState)
    --"next” enforces move predicate (valid transitions!)
    all s: State | {
        some Game.next[s] implies {
            (some num: Int, p: Player | strategicMove[s, num, p, Game.next[s]])
            or
            (doNothing[s, Game.next[s]])
        }
        
    }
}

// run {
//     wellformed
//     traces
// } for exactly 22 State, exactly 6 Int for {next is linear}

// Uncomment to make P2 use a strategy, where it only says numbers that are a multiple of 4, to always win
// run {
//     wellformed
//     tracesStrategic
// } for exactly 22 State, exactly 6 Int for {next is linear}

// Uncomment to make P2 always lose
// run {
//     wellformed
//     traces
//     some s: State | loser[s, P2]
// } for exactly 22 State, exactly 6 Int for {next is linear}

// Tests
test expect {
    strategyAlwaysWins: {
        wellformed
        tracesStrategic
        some s: State | loser[s, P2]
    } for exactly 22 State, exactly 6 Int for {next is linear} is unsat
}

example validWellformed is {wellformed} for {
    #Int = 6
    State = `State0
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 13
    player = `State0 -> `P20
}

example invalidWellformed is not {wellformed} for {
    #Int = 6
    State = `State0
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 22
    player = `State0 -> `P20
}

example validStarting is {some s: State | starting[s]} for {
    #Int = 6
    State = `State0
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 0
    player = `State0 -> `P20
}

example invalidStarting is not {some s: State | starting[s]} for {
    #Int = 6
    State = `State0
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 13
    player = `State0 -> `P20
}

example validP1Turn is {some s: State | P1Turn[s]} for {
    #Int = 6
    State = `State0
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 0
    player = `State0 -> `P20
}

example invalidP1Turn is not {some s: State | P1Turn[s]} for {
    #Int = 6
    State = `State0
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 22
    player = `State0 -> `P10
}

example validP2Turn is {some s: State | P2Turn[s]} for {
    #Int = 6
    State = `State0
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 4
    player = `State0 -> `P10
}

example invalidP2Turn is not {some s: State | P2Turn[s]} for {
    #Int = 6
    State = `State0
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 22
    player = `State0 -> `P20
}

example validLoser is {some s: State | loser[s, P2]} for {
    #Int = 6
    State = `State0
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 21
    player = `State0 -> `P20
}

example invalidLoser is not {some s: State | loser[s, P2]} for {
    #Int = 6
    State = `State0
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 13
    player = `State0 -> `P20
}

example validGameOver is {some s: State | gameOver[s]} for {
    #Int = 6
    State = `State0
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 21
    player = `State0 -> `P20
}

example invalidGameOver is not {some s: State | gameOver[s]} for {
    #Int = 6
    State = `State0
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 13
    player = `State0 -> `P20
}


example validMove is {some pre, post: State, numUp: Int, p: Player | move[pre, numUp, p, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 4 +
            `State1 -> 6
    player = `State0 -> `P10 +
             `State1 -> `P20
}

example invalidMoveNotTurn is not {some pre, post: State, numUp: Int, p: Player | move[pre, numUp, p, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 4 +
            `State1 -> 6
    player = `State0 -> `P10 +
             `State1 -> `P10
}

example invalidMoveNumUpWrong1 is not {some pre, post: State, numUp: Int, p: Player | move[pre, numUp, p, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 4 +
            `State1 -> 4
    player = `State0 -> `P10 +
             `State1 -> `P20
}

example invalidMoveNumUpWrong2 is not {some pre, post: State, numUp: Int, p: Player | move[pre, numUp, p, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 4 +
            `State1 -> 8
    player = `State0 -> `P10 +
             `State1 -> `P20
}

example invalidMoveBeyond21 is not {some pre, post: State, numUp: Int, p: Player | move[pre, numUp, p, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 20 +
            `State1 -> 22
    player = `State0 -> `P10 +
             `State1 -> `P20
}

example invalidMoveGameAlreadyOver is not {some pre, post: State, numUp: Int, p: Player | move[pre, numUp, p, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 21 +
            `State1 -> 22
    player = `State0 -> `P10 +
             `State1 -> `P20
}

example validStrategicMove1 is {some pre, post: State, numUp: Int, p: Player | strategicMove[pre, numUp, p, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 5 +
            `State1 -> 8
    player = `State0 -> `P10 +
             `State1 -> `P20
}

example validStrategicMove2 is {some pre, post: State, numUp: Int, p: Player | strategicMove[pre, numUp, p, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 8 +
            `State1 -> 11
    player = `State0 -> `P20 +
             `State1 -> `P10
}

example invalidStrategicMoveNotTurn is not {some pre, post: State, numUp: Int, p: Player | strategicMove[pre, numUp, p, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 4 +
            `State1 -> 6
    player = `State0 -> `P10 +
             `State1 -> `P10
}

example invalidStrategicMoveNumUpWrong1 is not {some pre, post: State, numUp: Int, p: Player | strategicMove[pre, numUp, p, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 4 +
            `State1 -> 4
    player = `State0 -> `P10 +
             `State1 -> `P20
}

example invalidStrategicMoveNumUpWrong2 is not {some pre, post: State, numUp: Int, p: Player | strategicMove[pre, numUp, p, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 4 +
            `State1 -> 8
    player = `State0 -> `P10 +
             `State1 -> `P20
}

example invalidStrategicMoveBeyond21 is not {some pre, post: State, numUp: Int, p: Player | strategicMove[pre, numUp, p, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 20 +
            `State1 -> 22
    player = `State0 -> `P10 +
             `State1 -> `P20
}

example invalidStrategicMoveGameAlreadyOver is not {some pre, post: State, numUp: Int, p: Player | strategicMove[pre, numUp, p, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 21 +
            `State1 -> 22
    player = `State0 -> `P10 +
             `State1 -> `P20
}

example invalidStrategicMoveP2NotMultiple4 is not {some pre, post: State, numUp: Int, p: Player | strategicMove[pre, numUp, p, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 13 +
            `State1 -> 15
    player = `State0 -> `P10 +
             `State1 -> `P20
}

example validDoNothing is {some pre, post: State | doNothing[pre, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 21 +
            `State1 -> 21
    player = `State0 -> `P20 +
             `State1 -> `P20
}

example invalidDoNothingGameNotOver is not {some pre, post: State | doNothing[pre, post]} for {
    #Int = 6
    State = `State0 + `State1
    P1 = `P10
    P2 = `P20
    Player = P1 + P2
    count = `State0 -> 4 +
            `State1 -> 6
    player = `State0 -> `P10 +
             `State1 -> `P20
}