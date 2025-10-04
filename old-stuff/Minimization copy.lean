import Mathlib

/-!
### Nerode Equivalence
This section defines the Nerode equivalence relation on the states of a DFA.
We prove that it is an equivalence relation, and we define the quotient type of states
by this relation.
-/

section NerodeEquivalence

namespace DFA

universe v u

variable {α : Type u} {σ : Type v}

/-- The Nerode equivalence relation on the states of a DFA.
For states `s₁, s₂`, we say `NerodeEquiv s₁ s₂` when the set of accepting words
from that state are equal. -/
def NerodeEquiv (M : DFA α σ) (s₁ s₂ : σ) : Prop :=
  ∀ w : List α, M.evalFrom s₁ w ∈ M.accept ↔ M.evalFrom s₂ w ∈ M.accept


theorem NerodeEquiv.refl (M : DFA α σ) (s : σ) : M.NerodeEquiv s s := by
  intro w; rfl

theorem NerodeEquiv.symm (M : DFA α σ) {s₁ s₂ : σ} (h : M.NerodeEquiv s₁ s₂) : M.NerodeEquiv s₂ s₁ := by
  intro w; rw [h w]

theorem NerodeEquiv.trans (M : DFA α σ) {s₁ s₂ s₃ : σ}
    (h₁ : M.NerodeEquiv s₁ s₂) (h₂ : M.NerodeEquiv s₂ s₃) : M.NerodeEquiv s₁ s₃ := by
  intro w; rw [h₁ w, h₂ w]

instance NerodeEquiv.setoid (M : DFA α σ) : Setoid σ where
  r := M.NerodeEquiv
  iseqv := ⟨NerodeEquiv.refl M, NerodeEquiv.symm M, NerodeEquiv.trans M⟩

def NerodeStates (M : DFA α σ) := Quotient (NerodeEquiv.setoid M)

/-! 
### Distinguishing Words
-/

def indistinguishableTo (M : DFA α σ) (n : ℕ) (s₁ s₂ : σ) : Prop :=
  ∀ w : List α, w.length ≤ n → (M.evalFrom s₁ w ∈ M.accept ↔ M.evalFrom s₂ w ∈ M.accept)

lemma indistinguishableTo.refl (M : DFA α σ) (n : ℕ) (s : σ) : M.indistinguishableTo n s s := by
  intro w hw; rfl

lemma indistinguishableTo.symm (M : DFA α σ) (n : ℕ) {s₁ s₂ : σ}
    (h : M.indistinguishableTo n s₁ s₂) : M.indistinguishableTo n s₂ s₁ := by
  intro w
  specialize h w
  simp_all

lemma indistinguishableTo.trans (M : DFA α σ) (n : ℕ) {s₁ s₂ s₃ : σ}
    (h₁ : M.indistinguishableTo n s₁ s₂) (h₂ : M.indistinguishableTo n s₂ s₃) :
    M.indistinguishableTo n s₁ s₃ := by
  intro w hw
  specialize h₁ w hw
  specialize h₂ w hw
  rw [h₁, h₂]

instance indistinguishableTo.setoid (M : DFA α σ) (n : ℕ) : Setoid σ where
  r (s₁ s₂ : σ) := M.indistinguishableTo n s₁ s₂
  iseqv := 
    ⟨indistinguishableTo.refl M n, 
    indistinguishableTo.symm M n, 
    indistinguishableTo.trans M n⟩

lemma indistinguishable_suc (M : DFA α σ) (s₁ s₂ : σ) (n : ℕ): 
    M.indistinguishableTo (n + 1) s₁ s₂ ↔ M.indistinguishableTo n s₁ s₂ ∧ 
    ∀ a : α, M.indistinguishableTo n (M.evalFrom s₁ [a]) (M.evalFrom s₂ [a]) := by
  sorry

/-- The eq-relation on states defined by being indistinguishable by up to `m` elements
is FINER than the relation of being indistinguishable up to `n` elements if `n ≤ m`-/
lemma indistinguishableTo.mono (M : DFA α σ) (s₁ s₂ : σ) {n m : ℕ} (h : n ≤ m) :
    indistinguishableTo.setoid M m ≤ indistinguishableTo.setoid M n := by
  simp [Setoid.le_def]
  intros s₁ s₂ h
  sorry

lemma indistinguishableTo.eq_nerode_iff_fixed (M : DFA α σ) (n : ℕ) : 
    indistinguishableTo.setoid M n = indistinguishableTo.setoid M (n + 1) ↔ 
    indistinguishableTo.setoid M n = NerodeEquiv.setoid M := by 
  sorry

/- 
`indistinguishableTo n + 1` is either FINER or EQUAL to `indistinguishableTo n`
by the previous lemma. 
If it is EQUAL, then we have reached a fixed point, and the relation is equal to Nerode equivalence.
Each iteration can only refine the relation, and there is an upper bound on the finest relation (the one 
that gives each element its own class), so we must reach a fixed point in at most `Fintype.card σ` iterations.
-/

variable [Fintype σ] [Fintype α]

lemma indistinguistableTo.eq_nerode (M : DFA α σ) : 
    indistinguishableTo.setoid M (Fintype.card σ) = NerodeEquiv.setoid M := by 
  sorry

instance (M : DFA α σ) (s : σ) : Decidable (s ∈ M.accept) := by infer_instance

instance indistinguishableTo.DecidableRel (M : DFA α σ) (n : ℕ) : DecidableRel (M.indistinguishableTo n) := by
  intros s₁ s₂
  simp [indistinguishableTo]
  apply Classical.decEq


/-- We say `Distinguishes s₁ s₂ w` if the word `w` accepts from 
s₁ but not from s₂, or vice versa. -/
def Distinguishes (M : DFA α σ) (s₁ s₂ : σ) (w : List α) : Prop := 
  (M.evalFrom s₁ w ∈ M.accept) ∧ (M.evalFrom s₂ w ∉ M.accept) ∨ 
  (M.evalFrom s₂ w ∈ M.accept) ∧ (M.evalFrom s₁ w ∉ M.accept)

/-- Two states are either nerode equivalent or there exists a distinguishing word -/
lemma NerodeEquiv.iff_not_exists(M : DFA α σ) (s₁ s₂ : σ) :
    M.NerodeEquiv s₁ s₂ ↔ ¬ ∃ w : List α, M.Distinguishes s₁ s₂ w := by
  simp [NerodeEquiv, Distinguishes]
  grind


/-! 
### Decidable Nerode Equivalence
This section defines a `Fintype` instance on the quotient type of states by the Nerode equivalence relation.
We do this by defining a boolean function that decides whether two states are Nerode equivalent.
-/

variable [Fintype α] [Fintype σ] [DecidableEq α] [DecidableEq σ] -- we assume that the states and alphabet are finite

/-- For all words, there is a word that has the same behavior of that word on all 
states but has length ≤ Fintype.card σ -/
lemma exists_short_path (M : DFA α σ) (w : List α) : 
    ∃ v : List α, v.length ≤ Fintype.card σ ∧ ∀ (s : σ), M.evalFrom s v = M.evalFrom s w := by
  sorry

lemma Distinguishes.short (M : DFA α σ) (s₁ s₂ : σ) : 
    (∃ w : List α, M.Distinguishes s₁ s₂ w) ↔ ∃ w' : List α, w'.length ≤ Fintype.card σ ∧ 
    M.Distinguishes s₁ s₂ w' := by
  constructor
  · rintro ⟨w, hw⟩ 
    obtain ⟨v, ⟨hleq, hv⟩⟩ := exists_short_path M w
    use v
    simp_all
    have hs₁ := hv s₁
    have hs₂ := hv s₂
    simp [Distinguishes] at hw ⊢
    rcases hw with (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · simp_all
    · simp_all
  · rintro ⟨w, ⟨h₁, h₂⟩⟩ 
    use w

/-- In order to ensure Nerode equivalence, it is sufficient to check all words with length
less than the number of states. -/
lemma NerodeEquiv.short (M : DFA α σ) (s₁ s₂ : σ) : M.NerodeEquiv s₁ s₂ ↔ 
    ¬ ∃ w : List α, w.length ≤ Fintype.card σ ∧ M.Distinguishes s₁ s₂ w := by 
  rw [NerodeEquiv.iff_not_exists]
  have h := Distinguishes.short M s₁ s₂
  simp_all

def acceptsFinset (M : DFA α σ) : Finset σ := {s | s ∈ M.accept}

instance (M : DFA α σ) (s : σ) : Decidable (s ∈ M.accept) := by 
  

instance (M : DFA α σ) (s : σ) (w : List α) : Decidable (M.evalFrom s w ∈ M.accept) := by 
  simp_all [evalFrom]
  sorry



/-- Returns true if `w` distinguishes `s₁` and `s₂` -/
def isDistinguishing (M : DFA α σ) (s₁ s₂ : σ) (w : List α) : Bool := 
  if (M.evalFrom s₁ w ∈ M.accept) then 
    if (M.evalFrom s₂ w ∈ M.accept) then false else true
  else 
    if (M.evalFrom s₂ w ∉ M.accept) then false else true
  
lemma isDistinguishing_correct (M : DFA α σ) (s₁ s₂ : σ) (w : List α) :
    isDistinguishing M s₁ s₂ w ↔ M.Distinguishes s₁ s₂ w := by 
  simp [isDistinguishing, Distinguishes]
  grind

/-- Returns all the words of length `n` -/ 
def getWordsOfLength (M : DFA α σ) (n : ℕ) : List (List α) := sorry 

lemma getWordsOfLength_correct (M : DFA α σ) (n : ℕ) (w : List α) :
    w ∈ getWordsOfLength M n ↔ w.length = n := by sorry

/-- Returns all the words of length `≤ n` -/
def getWordsUpToLength (M : DFA α σ) (n : ℕ) : List (List α) := sorry

lemma getWordsUpToLength_correct (M : DFA α σ) (n : ℕ) (w : List α) :
    w ∈ getWordsUpToLength M n ↔ w.length ≤ n := by sorry

/-- Returns false if any word of length `≤ Fintype.card σ` distinguishes 
`s₁` from `s₂`. Otherwise, it returns true -/
def NerodeEquiv.bool (M : DFA α σ) (s₁ s₂ : σ) : Bool := sorry

lemma NerodeEquiv.bool_correct' (M : DFA α σ) (s₁ s₂ : σ) :
    NerodeEquiv.bool M s₁ s₂ ↔ ¬ ∃ w : List α, w.length ≤ Fintype.card σ ∧ M.Distinguishes s₁ s₂ w := by sorry

lemma NerodeEquiv.bool_correct (M : DFA α σ) (s₁ s₂ : σ) :
    NerodeEquiv.bool M s₁ s₂ ↔ M.NerodeEquiv s₁ s₂ := by 
  rw [NerodeEquiv.bool_correct']
  rw [← NerodeEquiv.short M s₁ s₂]

instance NerodeEquiv.DecidableRel (M : DFA α σ) [Fintype σ] [Fintype α] : DecidableRel (NerodeEquiv M) := by
  intros s₁ s₂
  rcases h : (NerodeEquiv.bool M s₁ s₂)
  · apply isFalse    
    rw [← NerodeEquiv.bool_correct]
    exact ne_true_of_eq_false h
  · apply isTrue
    rw [← NerodeEquiv.bool_correct]
    exact h

instance FintypeNerodeStates (M : DFA α σ) [Fintype α] [inst : Fintype σ] : Fintype (NerodeStates M) := by
  apply @Quotient.fintype σ inst (NerodeEquiv.setoid M) (NerodeEquiv.DecidableRel M)


end DFA

end NerodeEquivalence