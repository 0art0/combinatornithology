# Combinatornithology

The game in this repository is meant to introduce the player to the area of [Combinatory logic](https://en.wikipedia.org/wiki/Combinatory_logic) through a series of short logic puzzles. The puzzles used here are mainly inspired by the ones in Raymond Smullyan's excellent book "To Mock a Mockingbird".

This game is intended to be played using the [LEAN theorem prover](https://leanprover.github.io/about/), although the puzzles can be solved independently as well (it is a lot more fun to use LEAN!). If you do not have LEAN installed, you can play the online version of this game <here>.
  
If you are new to LEAN, you can find a list of resources for getting started on the [LEAN prover community website](https://leanprover-community.github.io/learn.html).
  
The main tactics you will need for this game are:
  - `rw` - used to rewrite equalities
  - `intro` - used to pick an arbitrary bird in the forest
  - `existi` - used to specify a particular bird required to complete a goal
  - `unfold` - to unfold the definitions
  
---
