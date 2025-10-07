import MyProject.FinDFA.Morphisms

/-!
# Nerode Equivalence on AccessableFinDFAs

This file defines the Nerode equivalence relation on the states of an `AccessableFinDFA`.
We say two states `s₁, s₂` are Nerode Equivalent iff for all words `w`, the states
`evalFrom s₁ w` and `evalFrom s₂ w` are either both accepting or both rejecting.

We prove that the Nerode relation is a Decidable Equivalence Relation. This is done
by defining a bounded version of the Nerode relation, `BoundedNerode n`, where we only
consider words of length ≤ `n`. Because the alphabet is finite, there are only finitely many
such words, and thus `BoundedNerode n` is decidable. We then prove that `BoundedNerode n`
stabilizes at or before `n = |σ|`, where `σ` is the state space of the DFA, and that
the stabilized version is equivalent to the unbounded Nerode relation. This allows us to
transfer the decidability instance from `BoundedNerode` to `Nerode`.

## Main Definitions

 * `M.Nerode s₁ s₂` : The Nerode equivalence relation on states `s₁, s₂` of a FinDFA `M`.
 * `FinDFA.Nerode.decidable` : The decidability instance for the Nerode relation.
 * `FinDFA.Nerode.fintype` : The fintype instance for the quotient type of the Nerode relation.
-/

namespace FinDFA

universe u v

variable {α : Type u} [αFin : Fintype α] [αDec : DecidableEq α]
variable {σ : Type v} [σFin : Fintype σ] [σDec : DecidableEq σ]

/-- **Nerode Equivalence**: states accept exactly the same set of words. -/
def Nerode (M : FinDFA α σ) (s₁ s₂ : σ) : Prop :=
  ∀ w : List α, (M.evalFrom s₁ w ∈ M.accept ↔ M.evalFrom s₂ w ∈ M.accept)

lemma NerodeEquiv.refl (M : FinDFA α σ) (s : σ) : M.Nerode s s := by intro; rfl

lemma NerodeEquiv.symm (M : FinDFA α σ) {s₁ s₂ : σ}
    (h : M.Nerode s₁ s₂) : M.Nerode s₂ s₁ := by
  intro w; simpa [Iff.comm] using h w

lemma NerodeEquiv.trans (M : FinDFA α σ) {s₁ s₂ s₃ : σ}
  (h₁ : M.Nerode s₁ s₂) (h₂ : M.Nerode s₂ s₃) :
    M.Nerode s₁ s₃ := by
  intro w
  simpa [Iff.trans] using (h₁ w).trans (h₂ w)

/-- The `Nerode` relation is an equivalence -/
def NerodeEquiv.setoid (M : FinDFA α σ) : Setoid σ where
  r := M.Nerode
  iseqv :=
    ⟨NerodeEquiv.refl M, NerodeEquiv.symm M, NerodeEquiv.trans M⟩

/-- **Bounded Nerode**: states `s₁, s₂` are indistinguishable by words of length ≤ `n`. -/
def BoundedNerode (M : FinDFA α σ) (n : ℕ) (s₁ s₂ : σ) : Prop :=
  ∀ w : List α, w.length ≤ n → (M.evalFrom s₁ w ∈ M.accept ↔ M.evalFrom s₂ w ∈ M.accept)

lemma BoundedNerode.refl (M : FinDFA α σ) (n : ℕ) (s : σ) :
    M.BoundedNerode n s s := by
  intro w _; rfl

lemma BoundedNerode.symm (M : FinDFA α σ) (n : ℕ)
    {s₁ s₂ : σ} (h : M.BoundedNerode n s₁ s₂) :
    M.BoundedNerode n s₂ s₁ := by
  intro w hw; simpa [Iff.comm] using h w hw

lemma BoundedNerode.trans (M : FinDFA α σ) (n : ℕ) {s₁ s₂ s₃ : σ}
  (h₁ : M.BoundedNerode n s₁ s₂)
  (h₂ : M.BoundedNerode n s₂ s₃) :
    M.BoundedNerode n s₁ s₃ := by
  intro w hw
  simpa [Iff.trans] using (h₁ w hw).trans (h₂ w hw)

/- The `BoundedNerode` relation is a an equivalence-/
def BoundedNerode.setoid (M : FinDFA α σ) (n : ℕ) : Setoid σ where
  r := M.BoundedNerode n
  iseqv :=
    ⟨BoundedNerode.refl M n, BoundedNerode.symm M n, BoundedNerode.trans M n⟩

/-!
### Decidability of BoundedNerode

We define a computable version of `BoundedNerode` that quantifies over our finset
`M.getWordsLeqLength n`. Becuase this is a finite set, this version is decidable.
We then prove that this computable version is equivalent to the original one, and
thus we can transfer the decidability instance to the `BoundedNerode`.
-/

/-- We define an equivalent version of `BoundedNerode` that is based on
our `getWordsLeqLength` function from `FinDFA.Defs.lean`. -/
def BoundedNerodeComputable (M : FinDFA α σ) (n : ℕ) (s₁ s₂ : σ) : Prop :=
  ∀ w ∈ M.getWordsLeqLength n, (M.evalFrom s₁ w ∈ M.accept ↔ M.evalFrom s₂ w ∈ M.accept)

/-- This version is Decidable 'for free' -/
instance BoundedNerodeComputable.decidable (M : FinDFA α σ) (n : ℕ) :
    DecidableRel (M.BoundedNerodeComputable n) := by
  unfold BoundedNerodeComputable
  infer_instance

/- We prove that the computable version is equivalent to the old one -/
lemma BoundedNerodeComputable.correct (M : FinDFA α σ) (n : ℕ) :
    M.BoundedNerode n = M.BoundedNerodeComputable n := by
  ext s₁ s₂
  constructor
  · intro h w hw
    apply h
    rw [getWordsLeqLength_correct] at hw
    exact hw
  · intro h w hw
    apply h
    rw [getWordsLeqLength_correct]
    exact hw

/- We can now translate the decidablity instance -/
instance BoundedNerode.decidable (M : FinDFA α σ) (n : ℕ) :
    DecidableRel (M.BoundedNerode n) := by
  rw [BoundedNerodeComputable.correct M n]
  infer_instance

/-- We can enumerate the elements of the quotient type of the equivalence
classes of the `BoundedNerode` relation -/
instance BoundedNerode.QuotientFintype (M : FinDFA α σ) (n : ℕ) :
    Fintype (Quotient (BoundedNerode.setoid M n)) := by
  apply @Quotient.fintype σ σFin
          (BoundedNerode.setoid M n)
          (BoundedNerode.decidable M n)

/-- We have decidable equality on the quotient
of the state space by the `BoundedNerode` relation -/
instance BoundedNerode.DecidableEq (M : FinDFA α σ) (n : ℕ) :
    DecidableEq (Quotient (BoundedNerode.setoid M n)) := by
  apply @Quotient.decidableEq σ
          (BoundedNerode.setoid M n)
          (BoundedNerode.decidable M n)

/-!
### Bounded Nerode Monotonicity and Stabilization

We prove that `BoundedNerode n+1` refines `BoundedNerode (n+1)`.

We prove that this refinement stabilitzes
`BoundedNerode n` = `BoundedNerode (n+1)` implies that
`BoundedNerode n` = `BoundedNerode m` for all `m ≥ n`.

We prove that `BoundedNerode` stabilizes at before `n = |σ|`
* at `n = 0`, the Quotient type has cardinality `2`
* at `n > 0`, the relation either refines, increasing the cardinality of
the quotient type by at least `1`, or it stabilizes.
* the cardinality of the quotient type is bounded above by `|σ|`
* Thus, the relation must stabilize at or before `n = |σ| - 2`
-/

/-!
### Stabilized Bounded Nerode = Nerode

We prove that `BoundedNerode |σ|` is equivalent to `Nerode`, which allows us to
transfer the decidability instance from `BoundedNerode` to `Nerode`.
-/

lemma BoundedNerode

/- ### Examples -/

inductive TestAlpha where
  | a
  | b
  | c
deriving Repr, Fintype, DecidableEq

inductive TestSigma where
  | s₁ -- start
  | s₂ -- accept
deriving Repr, Fintype, DecidableEq

def TestFinDFA : FinDFA TestAlpha TestSigma where
  step (s : TestSigma) (o : TestAlpha) :=
    match s with  -- Always transitions to s₂
    | TestSigma.s₁ =>
      match o with
      | TestAlpha.a => TestSigma.s₂
      | TestAlpha.b => TestSigma.s₂
      | TestAlpha.c => TestSigma.s₂
    | TestSigma.s₂ =>
      match o with
      | TestAlpha.a => TestSigma.s₂
      | TestAlpha.b => TestSigma.s₂
      | TestAlpha.c => TestSigma.s₂
  start := TestSigma.s₁
  accept := {TestSigma.s₂}

/-
#eval (TestFinDFA.getWordsOfLength 0)
#eval (TestFinDFA.getWordsOfLength 1)
#eval (TestFinDFA.getWordsOfLength 2)

#eval (TestFinDFA.getWordsLeqLength 2)
-/
