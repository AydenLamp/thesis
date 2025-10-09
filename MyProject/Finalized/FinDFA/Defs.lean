import Mathlib

/-!
# FinDFA : Finite and computable DFAs

This file defines a structure `FinDFA` that is equivalent to `Mathlib.Computability.DFA`,
except that the accept states are given as a `Finset` instead of a `Set`, and
we require `Fintype` and `DecidableEq` instances on the alphabet and state space.

We define another structure `AccessibleFinDFA` that extends `FinDFA`
with a proof that every state is accessible.

We provide a coercion from `FinDFA` and `AccessibleFinDFA` to `DFA`, so that all
theorems and definitions about `DFA` can be used on `FinDFA` and `AccessibleFinDFA` transparently.

## Main Definitions

* `FinDFA α σ` : A DFA with alphabet `α` and state space `σ`
* `FinDFA.toDFA` : Converts a `FinDFA` to a `DFA`
* `FinDFA.getWordsLeqLength (n : ℕ) ` :  Returns a `Finset` of all words of length less than or
equal to `n` over the alphabet of the `FinDFA`.
* `FinDFA.isAccessibleState` : A *Decidable* predicate on states, true if the state is reachable
from the start state by some word.
* `AccessibleFinDFA` : A structure extending `FinDFA` with a proof that every state is
accessible.
* `FinDFA.toAccessible` : A function that converts a `FinDFA` to an `AccessibleFinDFA`

## Main Theorems

* `FinDFA.getWordsLeqLength_correct` : The `Finset` returned by `FinDFA.getWordsLeqLength n` contains
exactly the words of length less than or equal to `n`.
* `exists_short_access_word` : If a state is accessible, then it is accessed by a word of length
at most the number of states in the `FinDFA`. This theorem is used to obtain the decidability of
the `isAccessibleState` predicate.
* `FinDFA.toAccessible_pres_lang` : The `AccessibleFinDFA` obtained from a `FinDFA` accepts the same
language as the original `FinDFA`.
-/

universe u v

/-- A *finite and computable* DFA -/
structure FinDFA (α : Type u) (σ : Type v)
  [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ] where
  /-- Transition function. -/
  step  : σ → α → σ
  /-- Start state. -/
  start : σ
  /-- Accepting states as a `Finset`. -/
  accept : Finset σ

namespace FinDFA

variable {α : Type u} {σ : Type v} [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]

/-- Convert a `FinDFA` to a `DFA`. -/
def toDFA (M : FinDFA α σ) : DFA α σ where
  step   := M.step
  start  := M.start
  accept := (M.accept : Set σ)

/-- Coersion from `FinDFA` to `DFA`. -/
instance : Coe (FinDFA α σ) (DFA α σ) := ⟨toDFA⟩

@[simp] lemma coe_start (M : FinDFA α σ) : M.toDFA.start = M.start := rfl

@[simp] lemma coe_step (M : FinDFA α σ) : M.toDFA.step = M.step := rfl

@[simp] lemma coe_accept (M : FinDFA α σ) (s : σ) : s ∈ M.toDFA.accept ↔ s ∈ M.accept := by rfl

/-- Inputs a word `w` and returns an injection from letters `a` to `a :: w` -/
@[simp] def prependLetter (w : List α) : α ↪ List α where
  toFun (a : α) := a :: w
  inj' := by simp_all [Function.Injective]

/- Inputs a word `w` and returns the finset of `a :: w` for all `a : α` -/
@[simp] def getNextWords (w : List α) : Finset (List α) :=
  Finset.map (prependLetter w) (Finset.univ : Finset α)

/- Returns all the words of length `n` in the alphabet of `M` -/
@[simp] def getWordsOfLength (M : FinDFA α σ) (n : ℕ) : Finset (List α) :=
  match n with
  | 0 => {[]}
  | n + 1 => Finset.biUnion (M.getWordsOfLength n) getNextWords

@[simp] lemma getWordsOfLength_correct (M : FinDFA α σ) (n : ℕ) (w : List α) :
    w ∈ M.getWordsOfLength (n) ↔ w.length = n := by
  constructor
  · intros h
    induction n generalizing w with
    | zero => simp_all [getWordsOfLength]
    | succ n ih =>
      simp_all
      obtain ⟨v, ⟨hv₁, hv₂⟩⟩ := h
      have hvlen := ih v hv₁
      obtain ⟨v, hv⟩ := hv₂
      subst w
      subst n
      simp
  · intros h
    induction w generalizing n with
    | nil =>
      subst n
      simp
    | cons w ws ih =>
      subst n
      simp_all

/-- Returns a `Finset` of all words of length ≤ `n` -/
def getWordsLeqLength (M : FinDFA α σ) (n : ℕ) : Finset (List α) :=
  match n with
  | 0 => M.getWordsOfLength 0
  | n + 1 => (M.getWordsOfLength (n+1)) ∪ M.getWordsLeqLength n

@[simp] theorem getWordsLeqLength_correct (M : FinDFA α σ) {n : ℕ} {w : List α} :
    w ∈ M.getWordsLeqLength n ↔ w.length ≤ n := by
  constructor
  · intro hin
    induction n generalizing w with
    | zero => simp_all [getWordsLeqLength]
    | succ m ih =>
      simp_all [getWordsLeqLength]
      rcases hin with (hin | hin)
      · aesop
      · apply ih at hin
        exact Nat.le_add_right_of_le hin
  · intro hlen
    induction n generalizing w with
    | zero => simp_all [getWordsLeqLength]
    | succ n ih =>
      simp_all [getWordsLeqLength]
      have hn : w.length = n + 1 ∨ w.length ≤ n := by exact Nat.le_succ_iff_eq_or_le.mp hlen
      rcases hn with (hn | hn)
      · left
        have hw : w ≠ [] := by
          aesop
        have hw' := w.cons_head_tail hw
        use w.tail
        simp_all
        have hw' := w.cons_head_tail hw
        use w.head hw
      · right
        apply ih
        exact hn

/-!
### Accessible States

We define the predicate `isAccessibleState` on states, which is true if there is some word
that leads to that state from the start state. We show that if a state is accessible, then it is
accessible by some word of length at most the number of states in the `FinDFA`. This is used to
show that the `isAccessibleState` predicate is decidable, becuase we only must search through
finitely many words to determine if a state is accessible.
-/

/-- A State is accessible if there is some word that leads to it-/
abbrev isAccessibleState (M : FinDFA α σ) (s : σ) : Prop :=
  ∃ w, (M : DFA α σ).evalFrom M.start w = s

/-- If a state `s` is reachable, then it is reachable by some word of length ≤ |σ|. -/
theorem exists_short_access_word (M : FinDFA α σ) (s : σ) {w : List α}
    (hw : (M : DFA α σ).evalFrom M.start w = s) :
    ∃ v : List α, v.length ≤ Fintype.card σ ∧ s = (M : DFA α σ).evalFrom M.start v := by
  -- strong recursion on the length of `w`
  refine (Nat.strongRecOn
    (motive := fun n => ∀ w : List α, w.length = n →
      (M : DFA α σ).evalFrom M.start w = s →
        ∃ v : List α, v.length ≤ Fintype.card σ ∧
        s = (M : DFA α σ).evalFrom M.start v)
    w.length ?_ w rfl hw)
  simp_all
  intro n ih w hlen hw'
  by_cases hshort : n ≤ Fintype.card σ
  · subst hlen
    use w
    simp [hw', hshort]
  · have hle : Fintype.card σ ≤ n := by exact Nat.le_of_not_ge hshort
    -- Use Mathlib's `DFA.evalFrom_split` lemma to split `w` into `a ++ b ++ c`
    -- with a loop on `b`
    subst hlen
    have h := ((M : DFA α σ).evalFrom_split hle hw')
    rcases h with ⟨q, a, b, c, hsplit, hlen, hbne, hqa, hqb, hqc⟩
    simp_all
    have hlen₂ : (a ++ c).length < a.length + (b.length + c.length) := by
      simp_all
      exact List.length_pos_iff.mpr hbne
    have h := ih (a ++ c).length hlen₂ (a ++ c) rfl
    have h' : M.toDFA.evalFrom M.start (a ++ c) = s := by
      simp_all [DFA.evalFrom_of_append]
    obtain ⟨v, hv⟩ := h h'
    use v

/-- The set of all accessible states -/
def getAccessibleStates (M : FinDFA α σ) : Finset σ :=
  Finset.biUnion
    (M.getWordsLeqLength (Fintype.card σ))
    (fun s ↦ {(M : DFA α σ).evalFrom M.start s})

/-- Characterization of the `getAccessibleStates`. -/
lemma getAccessibleStates_correct (M : FinDFA α σ) (s : σ) :
   M.isAccessibleState s ↔ s ∈ M.getAccessibleStates := by
  simp [isAccessibleState, getAccessibleStates]
  constructor
  · rintro ⟨w, hw⟩
    apply M.exists_short_access_word s hw
  · rintro ⟨w, hw₁, hw₂⟩
    use w
    exact hw₂.symm

/-- Decidability of whether a state is accessible -/
instance isAccessibleStateDecidable (M : FinDFA α σ) (s : σ) :
    Decidable (M.isAccessibleState s) := by
  have h := M.getAccessibleStates_correct s
  rw [h]
  infer_instance

end FinDFA

/-!
### Accessible DFAs

An accessible DFA is one where every state is accessible.
We define a structure `AccessibleFinDFA` that extends `FinDFA`
with a proof that every state is accessible.

We also define coersions to both `FinDFA` and `DFA`.
-/

/-- An accessible DFA is one where every state is accessible. -/
structure AccessibleFinDFA (α : Type u) (σ : Type v)
    [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ] extends M : FinDFA α σ where
  is_accessible (s : σ) : M.isAccessibleState s

namespace AccessibleFinDFA

variable {α : Type u} [instα : Fintype α] [DecidableEq α]
variable {σ : Type v} [instσ : Fintype σ] [DecidableEq σ]

/-- A function that converts an `AccessibleFinDFA` to a `FinDFA`. -/
@[simp] def toFinDFA (M : AccessibleFinDFA α σ) : FinDFA α σ where
  step   := M.step
  start  := M.start
  accept := M.accept

/-- A function that converts an `AccessibleFinDFA` to a `DFA`. -/
@[simp] def toDFA (M : AccessibleFinDFA α σ) : DFA α σ := M.toFinDFA.toDFA

/-- Registering the coersion `AccessibleFinDFA` to `FinDFA`. -/
instance : Coe (AccessibleFinDFA α σ) (FinDFA α σ) := ⟨toFinDFA⟩

@[simp] lemma coe_start' (M : AccessibleFinDFA α σ) : M.toFinDFA.start = M.start := by rfl

@[simp] lemma coe_step' (M : AccessibleFinDFA α σ) : M.toFinDFA.step = M.step := by rfl

@[simp] lemma coe_accept' (M : AccessibleFinDFA α σ) (s : σ) :
    s ∈ M.toFinDFA.accept ↔ s ∈ M.accept := by rfl

/-- Registering the coersion `AccessibleFinDFA` to `DFA`. -/
instance : Coe (AccessibleFinDFA α σ) (DFA α σ) := ⟨toDFA⟩

@[simp] lemma coe_start (M : AccessibleFinDFA α σ) : M.toDFA.start = M.start := by rfl

@[simp] lemma coe_step (M : AccessibleFinDFA α σ) : M.toDFA.step = M.step := by rfl

@[simp] lemma coe_accept (M : AccessibleFinDFA α σ) (s : σ) :
    s ∈ M.toDFA.accept ↔ s ∈ M.accept := by rfl

end AccessibleFinDFA

/-! ### FinDFA → AccessibleFinDFA -/

namespace FinDFA

variable {α : Type u} [instα : Fintype α] [DecidableEq α]
variable {σ : Type v} [instσ : Fintype σ] [DecidableEq σ]

/-- Convert a `FinDFA` to an `AccessibleFinDFA`, by restricting to the accessible states. -/
def toAccessible (M : FinDFA α σ) : AccessibleFinDFA α {s : σ // M.isAccessibleState s} where
  step := fun s a => ⟨M.step s.val a, by
      simp_all [isAccessibleState]
      obtain ⟨s, ⟨w, hs⟩⟩ := s
      use w ++ [a]
      simp_all⟩
  start := ⟨M.start, by simp_all only [isAccessibleState]; use []; simp⟩
  accept := {s | s.val ∈ M.accept}
  is_accessible := by
    rintro ⟨s, ⟨w, hs⟩⟩
    simp_all [isAccessibleState]
    use w
    apply Subtype.eq
    simp_all [toDFA]
    induction w using List.reverseRecOn generalizing s with
    | nil => simp_all
    | append_singleton w a ih => simp_all [toDFA]

/-- For `toAccessible`, the carrier value of a single step is the original step. -/
@[simp] lemma toAccessible_step_val (M : FinDFA α σ)
    (s : {s : σ // M.isAccessibleState s}) (a : α) :
    ((M.toAccessible).step s a).val = M.step s.val a := rfl

/-- The underlying state reached by evaluating `toAccessible` from any accessible start `s` on
    a word `w` matches evaluating the original DFA from `s.val` on `w`. -/
lemma toAccessible_evalFrom_val (M : FinDFA α σ)
    (s : {s : σ // M.isAccessibleState s}) (w : List α) :
    ((M.toAccessible : DFA α {s : σ // M.isAccessibleState s}).evalFrom s w).val
      = ((M : DFA α σ).evalFrom s.val w) := by
  induction w using List.reverseRecOn with
  | nil =>
    simp [DFA.evalFrom]
  | append_singleton w a ih =>
    simp_all [DFA.evalFrom_append_singleton]

/-- The underlying state reached by evaluating `toAccessible` on `w` equals the state reached
    by evaluating the original DFA on `w`. -/
lemma toAccessible_eval_val (M : FinDFA α σ) (w : List α) :
    ((M.toAccessible : DFA α {s : σ // M.isAccessibleState s}).eval w).val
      = ((M : DFA α σ).eval w) := by
  have h := M.toAccessible_evalFrom_val ((M.toAccessible : AccessibleFinDFA α _).start) w
  simp_all [DFA.eval, toAccessible]

/-- The language of `M.toAccessible : AccessibleFinDFA α _` is
the same as the language of `M : FinDFA α σ`. -/
theorem toAccessible_pres_lang (M : FinDFA α σ) :
    ((M.toAccessible) : DFA α {s : σ // M.isAccessibleState s}).accepts = (M : DFA α σ).accepts := by
  ext w
  have h := M.toAccessible_eval_val w
  simp_all [DFA.mem_accepts]
  rw [← h]; clear h
  simp_all [toAccessible]


end FinDFA
