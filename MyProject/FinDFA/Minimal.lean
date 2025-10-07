import MyProject.FinDFA.NerodeEquiv

/-!
# The (minimal) Nerode Automaton as an AccessableFinDFA

We construct the *Nerode Automaton* of a given `AccessableFinDFA` `M`, which is the DFA
defined on the state space given by the quotient of the Nerode equivalence relation on `M`'s states,
with the transition function induced by `M`'s transition function.

We then show that this automaton is minimal by the surjective-morphism based preorder, defined
in `Morphisms.lean`.

## Main Definitions

* `AccessableFinDFA.NerodeAutomaton M` : The Nerode automaton of the `AccessableFinDFA` `M`.

## Main Theorems

* `AccessableFinDFA.NerodeAutomaton_isMinimal` : Given an `AccessableFinDFA` `M`, the Nerode automaton of `M`
is minimal. That is, for any other `AccessableFinDFA` `O` accepting the same language as `M`, there exists
a surjective morphism from `O` to `M.NerodeAutomaton`.

## TODO

* Also prove that the nerode automaton has the minimal amount of states?
-/
