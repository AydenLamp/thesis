import MyProject.FinDFA.Defs

/-!
# Accessable Finite DFAs

This file defines a structure that extends `FinDFA` to require that every state is reachable
from the start state by some word.

## Main Definitions

* `AccessableFinDFA α σ` : A FinDFA with alphabet `α` and state space `σ`,
both finite and with decidable equality, such that every state is reachable from the start state.
* `AccessableFinDFA.evalFrom` : The state reached from reading the word `w : list α`
starting from state `s : σ` for an `AccessableFinDFA` `M
* `AccessableFinDFA.acceptsFrom s` : The language accepted by `M` starting from state `s : σ`.
* `AccessableFinDFA.toFinDFA` : The underlying `FinDFA` of an `AccessableFinDFA`.
* `FinDFA.toAccessable` : A function which constructs an `AccessableFinDFA` from any `FinDFA`
which accepts the same language.
* `AccessableFinDFA.getWordOfState s` : For `s : σ`, a word which reaches `s` from the start state.
* `AccessableFinDFA.getWordsLeqLength n` : The `Finset` of all words of length ≤ `n` in the alphabet of `M`.

## Main Theorems

* `AccessableFinDFA.accepts_toFinDFA` : The language accepted by an `AccessableFinDFA` is the same
as its underlying `FinDFA`.
* `FinDFA.toAccessable_accepts` : The language accepted by `M.toAccessable` is the same as that
accepted by `M`.
* `AccessableFinDFA.getWordOfState_correct` : Characterization of `M.getWordOfState s`.
* `AccessableFinDFA.getWordsLeqLength_correct` : Characterization of `M.getWordsLeqLength n`.

## Implementation Notes

Note that the `step_accessable` field of `AccessableFinDFA` is about `FinDFA.evalFrom`, not the new
`AccessableFinDFA.evalFrom` that is defined later. These are the same function, but in proofs lean
can get confused between them. For this reason, in proofs, you should usually talk about the
`AccessableFinDFA.evalFrom` function, and use the lemma `AccessableFinDFA.step_accessable'`
(note the `'`) to access the `step_accessable` property.
-/

universe u v

/-- A `FinDFA` where every state is accesssable -/
structure AccessableFinDFA (α : Type u) (σ : Type v) [Fintype α] [DecidableEq α]
    [Fintype σ] [DecidableEq σ] extends M : FinDFA α σ where
  /-- All states can be reached from `M.start` by some word `w` -/
  -- DONT USE THIS VERSION IN PROOFS, use `step_accessable'` below (different M.evalFrom function)
  step_accessable (s : σ) : ∃ w : List α, M.evalFrom M.start w = s



namespace AccessableFinDFA

variable {α : Type u} [instα : Fintype α]
variable [DecidableEq α]
variable {σ : Type v} [instσ : Fintype σ] [DecidableEq σ]

set_option linter.unusedSectionVars false

/-- Evaluate from a given state. Mirrors `DFA.evalFrom`. -/
def evalFrom (M : AccessableFinDFA α σ) (s : σ) : List α → σ :=
  List.foldl M.step s

@[simp] lemma evalFrom_nil (M : AccessableFinDFA α σ) (s : σ) : M.evalFrom s [] = s := rfl

@[simp] lemma evalFrom_singleton (M : AccessableFinDFA α σ) (s : σ) (a : α) :
    M.evalFrom s [a] = M.step s a := rfl

@[simp] lemma evalFrom_append_singleton (M : AccessableFinDFA α σ)
    (s : σ) (x : List α) (a : α) :
    M.evalFrom s (x ++ [a]) = M.step (M.evalFrom s x) a := by
  simp [evalFrom, List.foldl_append]

/-- Evaluate from the start state. Mirrors `DFA.eval`. -/
def eval (M : AccessableFinDFA α σ) : List α → σ := M.evalFrom M.start

@[simp] lemma eval_nil (M : AccessableFinDFA α σ) : M.eval [] = M.start := rfl

@[simp] lemma eval_singleton (M : AccessableFinDFA α σ) (a : α) :
    M.eval [a] = M.step M.start a := rfl

@[simp] lemma eval_append_singleton (M : AccessableFinDFA α σ) (x : List α) (a : α) :
    M.eval (x ++ [a]) = M.step (M.eval x) a := by
  simp [eval]

/-- `M.acceptsFrom s` as a language over `α`. -/
def acceptsFrom (M : AccessableFinDFA α σ) (s : σ) : Language α :=
  {x | M.evalFrom s x ∈ M.accept}

@[simp] lemma mem_acceptsFrom (M : AccessableFinDFA α σ) {s : σ} {x : List α} :
    x ∈ M.acceptsFrom s ↔ M.evalFrom s x ∈ M.accept := Iff.rfl

/-- `M.accepts` is the language accepted from the start state. -/
def accepts (M : AccessableFinDFA α σ) : Language α := M.acceptsFrom M.start

@[simp] lemma mem_accepts (M : AccessableFinDFA α σ) {x : List α} :
    x ∈ M.accepts ↔ M.eval x ∈ (M.accept) := Iff.rfl

/-! ### Conversions to and from `FinDFA` -/

def toFinDFA (M : AccessableFinDFA α σ) : FinDFA α σ where
  step   := M.step
  start  := M.start
  accept := M.accept

@[simp] lemma accepts_toFinDFA (M : AccessableFinDFA α σ) :
    (M.toFinDFA.accepts : Language α) = M.accepts := by
  ext x; rfl

@[simp] lemma evalFrom_eq (M : AccessableFinDFA α σ) :
    M.toFinDFA.evalFrom = M.evalFrom := by
  rfl

/- A version of `step_accessable` about `AccessableFinDFA.evalFrom` not `FinDFA.evalFrom` -/
lemma step_accessable' (M : AccessableFinDFA α σ) (s : σ) :
    ∃ w : List α, M.evalFrom M.start w = s := M.step_accessable s

end AccessableFinDFA

namespace FinDFA

variable {α : Type u} [instα : Fintype α] [DecidableEq α]
variable {σ : Type v} [instσ : Fintype σ] [DecidableEq σ]

def toAccessable (M : FinDFA α σ) : AccessableFinDFA α {s : σ // M.isAccessableState s} where
  step := fun s a => ⟨M.step s.val a, by
      simp_all [isAccessableState]
      obtain ⟨s, ⟨w, hs⟩⟩ := s
      use w ++ [a]
      simp_all⟩
  start := ⟨M.start, by simp_all only [isAccessableState]; use []; simp⟩
  accept := {s | s.val ∈ M.accept}
  step_accessable := by
    intros s
    simp_all [isAccessableState]
    obtain ⟨s, ⟨w, hx⟩⟩ := s
    use w
    apply Subtype.eq
    induction w using List.reverseRecOn generalizing s with
    | nil => simp_all; simp at hx; exact hx
    | append_singleton w a ih =>
      simp at hx
      simp_all

lemma toAccessable.eval (M : FinDFA α σ) (w : List α) : (M.toAccessable.eval w).val = M.eval w := by
  induction w using List.reverseRecOn with
  | nil => simp_all [toAccessable]
  | append_singleton w a ih =>
    simp_all [toAccessable]

/-- Our `toAccessable` function preserves the language recognized -/
theorem toAccessable.pres_lang (M : FinDFA α σ) (w : List α) : w ∈ M.accepts ↔ w ∈ (M.toAccessable).accepts := by
  simp_all [mem_accepts, AccessableFinDFA.mem_accepts]
  constructor
  · intro h
    have h₂ := toAccessable.eval M w
    simp_all [toAccessable]
  · intros h
    have h₂ := toAccessable.eval M w
    simp_all [toAccessable]

end FinDFA

/-!
### AccessableFinDFA definitions on finsets
-/

namespace AccessableFinDFA

variable {α : Type u} [instα : Fintype α] [DecidableEq α]
variable {σ : Type v} [instσ : Fintype σ] [DecidableEq σ]

/-- Returns a `Finset` of all words of length ≤ `n` -/
def getWordsLeqLength (M : AccessableFinDFA α σ) (n : ℕ) : Finset (List α) :=
  M.toFinDFA.getWordsLeqLength n

lemma getWordsLeqLength_correct (M : AccessableFinDFA α σ) {n : ℕ} {w : List α} :
    w ∈ M.getWordsLeqLength n ↔ w.length ≤ n := by
  unfold getWordsLeqLength
  simp [FinDFA.getWordsLeqLength_correct]
