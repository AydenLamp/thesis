import Mathlib

/-!
# Computable DFAs

We package a DFA whose alphabet `α` and state space `σ` are `Fintype` with `DecidableEq`,
and the accept set is a `Finset` (not a `Set`).

We also define the `Nerode` Equivalence relation on states and provide
`Fintype` and `DecidableEq` instances for the quotient type of states by this relation.

The quotient type of the `Nerode` equivalence is the state space of the minimal DFA
accepting the same language, given that the original DFA is reachable.
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

/-! ### FinDFA implementation-/

namespace FinDFA

variable {α : Type u} [instα : Fintype α]
variable [DecidableEq α]
variable {σ : Type v} [instσ : Fintype σ] [DecidableEq σ]

set_option linter.unusedSectionVars false

/-- Evaluate from a given state. Mirrors `DFA.evalFrom`. -/
def evalFrom (M : FinDFA α σ) (s : σ) : List α → σ :=
  List.foldl M.step s

@[simp] lemma evalFrom_nil (M : FinDFA α σ) (s : σ) : M.evalFrom s [] = s := rfl

@[simp] lemma evalFrom_singleton (M : FinDFA α σ) (s : σ) (a : α) :
    M.evalFrom s [a] = M.step s a := rfl

@[simp] lemma evalFrom_append_singleton (M : FinDFA α σ)
    (s : σ) (x : List α) (a : α) :
    M.evalFrom s (x ++ [a]) = M.step (M.evalFrom s x) a := by
  simp [evalFrom, List.foldl_append]

/-- Evaluate from the start state. Mirrors `DFA.eval`. -/
def eval (M : FinDFA α σ) : List α → σ := M.evalFrom M.start

@[simp] lemma eval_nil (M : FinDFA α σ) : M.eval [] = M.start := rfl

@[simp] lemma eval_singleton (M : FinDFA α σ) (a : α) :
    M.eval [a] = M.step M.start a := rfl

@[simp] lemma eval_append_singleton (M : FinDFA α σ) (x : List α) (a : α) :
    M.eval (x ++ [a]) = M.step (M.eval x) a := by
  simp [eval]

/-- `M.acceptsFrom s` as a language over `α`. -/
def acceptsFrom (M : FinDFA α σ) (s : σ) : Language α :=
  {x | M.evalFrom s x ∈ M.accept}

@[simp] lemma mem_acceptsFrom (M : FinDFA α σ) {s : σ} {x : List α} :
    x ∈ M.acceptsFrom s ↔ M.evalFrom s x ∈ M.accept := Iff.rfl

/-- `M.accepts` is the language accepted from the start state. -/
def accepts (M : FinDFA α σ) : Language α := M.acceptsFrom M.start

@[simp] lemma mem_accepts (M : FinDFA α σ) {x : List α} :
    x ∈ M.accepts ↔ M.eval x ∈ (M.accept) := Iff.rfl

/-! #### Conversions to mathlib's `DFA` -/

-- If you want to reuse theorems from `Mathlib/Computability/DFA`,
-- it’s convenient to convert our `FinDFA` into a standard `DFA` by
-- coercing the `Finset` of accepts to a `Set` of accepts.
def toDFA (M : FinDFA α σ) : DFA α σ where
  step   := M.step
  start  := M.start
  accept := (M.accept : Set σ)

@[simp] lemma accepts_toDFA (M : FinDFA α σ) :
    (M.toDFA.accepts : Language α) = M.accepts := by
  ext x; rfl

/-! ### Equivalences on states  -/

/-- **Nerode Equivalence**: states accept exactly the
same set of words. This is the relation used in DFA minimization. -/
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

/- In Order to make the Nerode equivalence computable, we define a bounded version of it.
Later, we will prove that for a DFA with a finite number of states, the bounded version
is equivalent to the unbounded version when `n ≥ |σ|`. -/

/-- ***Bounded Nerode***: states `s₁, s₂` are indistinguishable by words of length ≤ `n`. -/
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
#### Bounded Nerode decidablity
We define a function `getWordsLeqLength` that returns all words of length ≤ `n`
as a `finset (List α)`, along with a correctness lemma. This allows us to define a
`DecidableRel` instance for `BoundedNerode`.
-/

set_option linter.unusedVariables false
/- Returns a Finset of all letters -/
@[simp] def getLetters (M : FinDFA α σ) : Finset (α) := Finset.univ

@[simp] lemma getLetters.correct (M : FinDFA α σ) (a : α) : a ∈ M.getLetters := by
  simp

def prependLetter (M : FinDFA α σ) (w : List α) : α ↪ List α where
  toFun (a : α) := a :: w
  inj' := by simp_all [Function.Injective]

/- Inputs a word `w` and returns the finset of `a :: w` for `a : α` -/
def getNextWords (M : FinDFA α σ) (w : List α) : Finset (List α) :=
  Finset.map (M.prependLetter w) (M.getLetters)

@[simp] lemma getNextWords.correct (M : FinDFA α σ) (w : List α) (a : α) :
    a :: w ∈ M.getNextWords w := by
  simp_all [getNextWords, prependLetter]

/- Returns all the words of length `n` -/
def getWordsOfLength (M : FinDFA α σ) (n : ℕ) : Finset (List α) :=
  match n with
  | 0 => {[]}
  | n + 1 => Finset.biUnion (M.getWordsOfLength n) M.getNextWords

lemma getWordsOfLength.correct (M : FinDFA α σ) (n : ℕ) (w : List α) :
    w ∈ M.getWordsOfLength (n) ↔ w.length = n := by
  constructor
  · intros h
    induction n generalizing w with
    | zero => simp_all [getWordsOfLength]
    | succ n ih =>
      simp_all [getWordsOfLength]
      obtain ⟨v, ⟨hv₁, hv₂⟩⟩ := h
      simp_all [getNextWords, prependLetter]
      have hvlen := ih v hv₁
      obtain ⟨v, hv⟩ := hv₂
      subst w
      subst n
      simp
  · intros h
    induction w generalizing n with
    | nil =>
      simp_all
      subst n
      unfold getWordsOfLength
      simp
    | cons w ws ih =>
      simp_all
      unfold getWordsOfLength
      subst n
      simp_all
      use ws
      simp_all

/-- Returns a `Finset` of all words of length ≤ `n` -/
def getWordsLeqLength (M : FinDFA α σ) (n : ℕ) : Finset (List α) :=
  match n with
  | 0 => M.getWordsOfLength 0
  | n + 1 => (M.getWordsOfLength (n+1)) ∪ M.getWordsLeqLength n

lemma getWordsLeqLength.correct (M : FinDFA α σ) {n : ℕ} {w : List α} :
    w ∈ M.getWordsLeqLength n ↔ w.length ≤ n := by
  constructor
  · intro hin
    induction n generalizing w with
    |zero =>
      unfold getWordsLeqLength at hin
      unfold getWordsOfLength at hin
      simp_all
    | succ m ih =>
      unfold getWordsLeqLength at hin
      simp_all
      rcases hin with (hin | hin)
      · rw [getWordsOfLength.correct] at hin
        simp_all
      · apply ih at hin
        exact Nat.le_add_right_of_le hin
  · intro hlen
    induction n generalizing w with
    | zero =>
      simp_all [getWordsLeqLength, getWordsOfLength]
    | succ n ih =>
      simp_all [getWordsLeqLength]
      have hn : w.length = n + 1 ∨ w.length ≤ n := by exact Nat.le_succ_iff_eq_or_le.mp hlen
      rcases hn with (hn | hn)
      · left
        rw [getWordsOfLength.correct M (n + 1) w]
        exact hn
      · right
        apply ih
        exact hn

/-- We define an equivalent version of `BoundedNerode` that is based on
our `getWordsLeqLength` function. -/
def BoundedNerodeComputable (M : FinDFA α σ) (n : ℕ) (s₁ s₂ : σ) : Prop :=
  ∀ w ∈ M.getWordsLeqLength n, (M.evalFrom s₁ w ∈ M.accept ↔ M.evalFrom s₂ w ∈ M.accept)

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
    rw [getWordsLeqLength.correct] at hw
    exact hw
  · intro h w hw
    apply h
    rw [getWordsLeqLength.correct]
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
  apply @Quotient.fintype σ instσ
          (BoundedNerode.setoid M n)
          (BoundedNerode.decidable M n)

/-- We have decidable equality on the quotient
of the state space by the `BoundedNerode` relation
instance BoundedNerode.DecidableEq (M : FinDFA α σ) (n : ℕ) :
    DecidableEq (Quotient (BoundedNerode.setoid M n)) := by
  apply @Quotient.decidableEq σ
          (BoundedNerode.setoid M n)
          (BoundedNerode.decidable M n) -/

/- ### Bounded Nerode Monotonicity
We prove that `BoundedNerode n+1` refines `BoundedNerode (n+1)`.

We prove that this refinement can stabilitze
`BoundedNerode n` = `BoundedNerode (n+1)` implies that
`BoundedNerode n` = `BoundedNerode m` for all `m ≥ n`.

We prove that `BoundedNerode` stablizes at before `n = |σ|`
* at `n = 0`, the Quotient type has cardinality `2`
* at `n > 0`, the relation either refines, increasing the cardinality of
the quotient type by at least `1`, or it stabilizes.
* the cardinality of the quotient type is bounded above by `|σ|`
* Thus, the relation must stabilize at or before `n = |σ| - 2`

We prove that `BoundedNerode |σ|` is equal to `Nerode`
-/

lemma BoundedNerode.stabilize (M : FinDFA α σ) (n : ℕ) :
    M.BoundedNerode n = M.BoundedNerode (n + 1) →


lemma BoundedNerode.stabilize (M : FinDFA α σ) :
    M.BoundedNerode (Fintype.card σ) = M.Nerode := by
  ext s₁ s₂








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


/-! ### Decidability instances -/


end FinDFA

-/
