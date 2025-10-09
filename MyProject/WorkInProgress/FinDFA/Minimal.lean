import MyProject.WordInProgress.Nerode

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
* Correct minimality Definition?
-/

namespace AccessibleFinDFA

universe u v

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {σ : Type v} [Fintype σ] [DecidableEq σ]

/-- The Nerode automaton of the `AccessibleFinDFA` `M`. -/
def NerodeAutomaton (M : AccessibleFinDFA α σ) : AccessibleFinDFA α (Quotient (NerodeEquiv.setoid M)) where
  step := sorry
  start := Quotient.mk (NerodeEquiv.setoid M) M.start
  accept := {Quotient.mk (NerodeEquiv.setoid M) q | q ∈ M.accept }

theorem NerodeAutomaton_isMinimal (M : AccessibleFinDFA α σ) :
    isMinimal (M.NerodeAutomaton) := by
  intro N h
  haveI : Nonempty (N →ₗ M.NerodeAutomaton) := h
  sorry

end AccessibleFinDFA
#check isMinimal

def isMinimal' (M : AccessibleFinDFA α σ) : Prop :=
  ∀ (N : AccessibleFinDFA α σ) (h : N ≤ M),  Nonempty ((N : DFA α σ≃ₗ M)
