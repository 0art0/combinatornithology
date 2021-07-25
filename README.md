# Combinatornithology

The game in this repository is meant to introduce the player to the area of [Combinatory logic](https://en.wikipedia.org/wiki/Combinatory_logic) through a series of short logic puzzles. The puzzles used here are mainly inspired by the ones in Raymond Smullyan's excellent book "To Mock a Mockingbird".

This game is intended to be played using the [LEAN theorem prover](https://leanprover.github.io/about/), although the puzzles can be solved independently as well (it is a lot more fun to use LEAN!). If you do not have LEAN installed, you can play the online version of this game [here](https://leanprover-community.github.io/lean-web-editor/#url=https%3A%2F%2Fraw.githubusercontent.com%2F0Art0%2Fcombinatornithology%2Fmaster%2Fsrc%2Fcombinatornithology.lean).
  
If you are new to LEAN, you can find a list of resources for getting started on the [LEAN prover community website](https://leanprover-community.github.io/learn.html).
  
The main tactics you will need for this game are:
  - `rw` - used to rewrite equalities
  - `intro` - used to pick an arbitrary bird in the forest
  - `existsi` - used to specify a particular bird required to complete a goal
  - `unfold` - to unfold the definitions

The objective of the game is to fill in the `sorry`s with LEAN proofs of the puzzles. If you are stuck, solutions are available [in this file](https://github.com/0Art0/combinatornithology/blob/solutions/src/combinatornithology_solved.lean).

A description of all the birds and their calls can be found in [the `birdcall.md` file](https://github.com/0Art0/combinatornithology/blob/master/src/birdcalls.md).

---
