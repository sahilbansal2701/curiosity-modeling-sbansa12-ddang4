# Curiosity Modeling

# Counting to 21
A game with n amount of people. We start counting up and each person can only say 1-3 numbers. Whoever says 21 loses the game. Between two people there is a known strategy to always win. So could be taken in two ways. Either only have two players and increase the number we count to or keep the number we count to the same and increase number of players. Interesting to see if we can find a strategy such that a player always wins.

# Assumptions
- We are playing a Two Player version of the counting to 21 game.
- Player 1 always goes first

# Abstractions
initial state is player 2, 0
the player in state is the player who said that number rather than the player to go next
game has a loser rather than a winner

# What are you trying to model? Include a brief description that would give someone unfamiliar with the topic a basic understanding of your goal.
# Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by Sterling. How should we look at and interpret an instance created by your spec?
# At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.
