# Curiosity Modeling

# Counting to 21
A game with n amount of people. We start at 0 and each person counts up saying only 1-3 numbers at a time. Whoever says 21 loses the game. If a two player version of this game is played, there is a known strategy for the person going second to always win. We would like to model the game and verify that the strategy indeed holds for all possible games between two players. In addtion, the model is flexible enough that it can be easily changed to find a strategy to always win when needing to count to a higher number.

# Assumptions
- We are playing a two player version of the game
- Player1 always goes first
- We are only counting upto 21

# Abstractions
- Rather than have the players count up we have them add 1, 2 or 3 to the previous number to simulate a faster-paced verion of the game
- In the initial state, the count is 0 and player 2 said that number. In reality, player 1 would be first and say 1, 2 or 3.
- The player assocaited with each state is the player who said that count.
- We limit the game to 22 states because there is one initial state and at maximum 21 other states if each player only increments by 1, in a game of counting to 21.

# Runs Meaning
We have three commented run statements in 21.frg. 
- The first one is a simple run where all the States are well formed and any Player can win. This just generates all possible traces of the game.
- The second run statemtent is a non-strategic way to make one of the two players lose in every instance (P2 in the run statement). 
- The third run makes use of a strategicMove predicate to implement a strategy which would allow the second player to always win.

# Tests Meaning
- vacuityTest tests if wellformed and traces are sat for exactly 22 states and 6 Ints. It makes sure that some traces exist.
- strategyAlwaysWins if wellformed, strategicTraces and P2 loser is unsat. We are verifying the strategy always works by saying that if player 2 uses the multiple of 4 strategy, losing is impossible for them.
- basicTestwithLessStates tests if wellformed and traces are sat for 10 states. A game with only 10 states is possible.
- noOneWinsTestwithLessThanSevenStates tests no one can win in less than 7 states. A game with only 7 states produces no loser because it would be impossible to reach 21 given the constraints of the game.
- onlyOnePlayerAlwaysLoses tests in a game with all wellformed state someone always wins and someone always loses.

# Examples Meaning
- For the predicates wellformed, starting, loser, P1Turn, P2Turn,gameOver and doNothing, checked validity through sat and unsat examples.
- Checked validity of move and strategicMove to give sat
- Checked 5 examples of invalid states for move to result in unsat. These include checking if the count goes beyond 21, game finishes before 21, and count between two consecutive state always differs by 1, 2 or 3 only.
- Checked 5 examples of invalid states for strategicMove to result in unsat. These include checking if the count goes beyond 21, game finishes before 21, count between two consecutive state always differs by 1, 2 or 3 only, and to make sure that P2 wins.

# How To Read Instance
The best way to read an instance would be to look at the tables in Sterling. The table 'count' contains the state and the count corresponding to that state. The table 'player' contains the state and the player who said the current count. These two tables together depict how the game progresses. In each run, we will have 22 States and once the count reaches 21, all the remaining states will be identical to this one as we just 'do nothing'.

# Sigs Representation (Purpose and Connection)
- Player: Abstract type used to represent a player of the game.
    - P1: A concrete one sig that represents player 1 of the game
    - P2: A concrete one sig that represents player 2 of the game
- State: Used to represent the current state of the game. It contains two fields: count and player.
    - count: represents the current number counted upto
    - player: represents the player who said count
- Game: A one sig used to refer to an entire game/trace. It has two fields: next and initalState
    - next: A pfunc of State to State that is used to find which state follows another state and by traversing this can figure out an entire trace of the game
    - initialState: the initial state of the game/trace

# Pred Representation (Purpose and Connection)
- wellformed: predicate that narrows down the space to only have valid states, which are states where the count is greater than or equal to 0 and less than or equal to 21.
- starting[s: State]: predicate that returns true when s is a starting state for the game else returns false. A starting state is when the count is 0 and the player is player2.
- P1Turn[s: State]: predicate that returns true when it is player1's turn else false. It is player1's turn if the person who said the current count was player2.
- P2Turn[s: State]: predicate that returns true when it is player2's turn else false. It is player2's turn if the person who said the current count was player1.
- move[pre: State, numUp: Int, p: Player, post: State]: predicate that returns true if going from State pre to State post is a valid move in the game else false. The game has a valid move only if it is that players turn and the number we count up to is 1 or 2 or 3 increments higher and the game is not over. In addition, we had to add a constraint that the player cannot go above 21 because since we are couting up they would always have to say 21 and cannot just skip it. A move would then just be adding how much we want to count up by to the count and changing the player to the next player.
- strategicMove[pre: State, numUp: Int, p: Player, post: State]: similar to the move predicate with the added constraint that player2 always counts upto and including a multiple of 4. This predicate was made so that we could have player2 use the known strategy.
- loser[s: State, p: Player]: predicate that returns true if the player p has lost in state s else false. We know a player has lost if the count for the state is 21 and they are the one who said that count.
- gameOver[s: State]: predicate that returns true if any of the players have lost, else false.
- doNothing[pre: State, post: State]: predicate that returns true if nothing is done going from state pre to state post. We need this so that we can model traces of the game that are less than 22 states. We can only do nothing if the game is over and in this case by do nothing we mean that the count and player for the state stay the same.
- traces: predicate that is used to generate normal, non-strategic traces of the game. We do this by saying the initial state of the game ahs to satisfy the starting predicate, that no state can reach back to the starting state, and that every state that follows another state must either satisfy the move predicate or the do nothing predicate. 
- tracesStrategic: predicate similar to the traces predicate with the only change that player2 will always employ their strategy.