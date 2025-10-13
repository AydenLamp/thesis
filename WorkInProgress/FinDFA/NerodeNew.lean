import MyProject.FinDFA.Morphisms
import Mathlib

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
transfer the decidability instance from `BoundedNerode` to `NerodeEquiv`.

## Main Definitions

 * `M.NerodeEquiv s₁ s₂` : The Nerode equivalence relation on states `s₁, s₂` of a FinDFA `M`.
 * `FinDFA.NerodeEquiv_decidable` : The decidability instance for the Nerode relation.
 * `FinDFA.NerodeEquiv_fintype` : The fintype instance for the quotient type of the Nerode relation.
-/

namespace AccessibleFinDFA

universe u v

variable {α : Type u} [Fintype α] [DecidableEq α ]
variable {σ : Type v} [σFin : Fintype σ] [DecidableEq σ]

variable (M : AccessibleFinDFA α σ)

/-- We say `Distinguishes w s₁ s₂` if evaluating the word `w` from state `s₁` is
accepting, but evaluating `w` from `s₂` is rejecting, or vice versa. -/
def Distinguishes (w : List α) (s₁ s₂ : σ) : Prop :=
  ((M : DFA α σ).evalFrom s₁ w ∈ M.accept) ≠ ((M : DFA α σ).evalFrom s₂ w ∈ M.accept)

lemma Distinguishes.iff_step (w : List α) (a : α) (s₁ s₂ : σ) :
    M.Distinguishes (a :: w) s₁ s₂ ↔ M.Distinguishes w (M.step s₁ a) (M.step s₂ a) := by
  simp_all [Distinguishes, DFA.evalFrom]

/-- **Nerode Equivalence**: states accept exactly the same set of words.
i.e. the states are not distinguishable by words of any length -/
def NerodeEquiv (M : AccessibleFinDFA α σ) (s₁ s₂ : σ) : Prop :=
  ∀ w : List α, ¬ (M.Distinguishes w s₁ s₂)

lemma NerodeEquiv.refl (M : AccessibleFinDFA α σ) (s : σ) : M.NerodeEquiv s s := by
  intro w
  simp [Distinguishes]

lemma NerodeEquiv.symm (M : AccessibleFinDFA α σ) {s₁ s₂ : σ}
    (h : M.NerodeEquiv s₁ s₂) : M.NerodeEquiv s₂ s₁ := by
  simp_all [NerodeEquiv, Distinguishes]

lemma NerodeEquiv.trans (M : AccessibleFinDFA α σ) {s₁ s₂ s₃ : σ}
  (h₁ : M.NerodeEquiv s₁ s₂) (h₂ : M.NerodeEquiv s₂ s₃) :
    M.NerodeEquiv s₁ s₃ := by
  intro w
  simp_all [NerodeEquiv, Distinguishes]

/-- The `Nerode` relation is an equivalence -/
def NerodeEquiv.setoid (M : AccessibleFinDFA α σ) : Setoid σ where
  r := M.NerodeEquiv
  iseqv :=
    ⟨NerodeEquiv.refl M, NerodeEquiv.symm M, NerodeEquiv.trans M⟩

/-- **Bounded Nerode**: states `s₁, s₂` are indistinguishable by words of length ≤ `n`. -/
def BoundedNerode (M : AccessibleFinDFA α σ) (n : ℕ) (s₁ s₂ : σ) : Prop :=
  ∀ w : List α, w.length ≤ n → ¬ (M.Distinguishes w s₁ s₂)

lemma BoundedNerode.refl (M : AccessibleFinDFA α σ) (n : ℕ) (s : σ) :
    M.BoundedNerode n s s := by
  intro w _; simp [Distinguishes]

lemma BoundedNerode.symm (M : AccessibleFinDFA α σ) (n : ℕ)
    {s₁ s₂ : σ} (h : M.BoundedNerode n s₁ s₂) :
    M.BoundedNerode n s₂ s₁ := by
  simp_all [BoundedNerode, Distinguishes]

lemma BoundedNerode.trans (M : AccessibleFinDFA α σ) (n : ℕ) {s₁ s₂ s₃ : σ}
  (h₁ : M.BoundedNerode n s₁ s₂) (h₂ : M.BoundedNerode n s₂ s₃) :
    M.BoundedNerode n s₁ s₃ := by
  simp_all [BoundedNerode, Distinguishes]

/- The `BoundedNerode` relation is a an equivalence-/
def BoundedNerode.setoid (n : ℕ) : Setoid σ where
  r := M.BoundedNerode n
  iseqv :=
    ⟨BoundedNerode.refl M n, BoundedNerode.symm M n, BoundedNerode.trans M n⟩

@[simp] lemma BoundedNerode.setoid_def  (n : ℕ) :
    (BoundedNerode.setoid M n).r = M.BoundedNerode n := by rfl

@[simp] lemma BoundedNerode.setoid_def' (n : ℕ) (s₁ s₂ : σ) :
    (BoundedNerode.setoid M n) s₁ s₂ ↔  M.BoundedNerode n s₁ s₂:= by rfl

/-- If `BoundedNerode n` does not relate `s₁ s₂`, then there
exists a word of length `≤n` that distinguishes s₁ and s₂-/
lemma BoundedNerode.exists_distinguishes {n : ℕ} {s₁ s₂ : σ} (h : ¬ M.BoundedNerode n s₁ s₂) :
    ∃ w : List α, (w.length ≤ n) ∧ M.Distinguishes w s₁ s₂ := by
  simp_all [BoundedNerode, Distinguishes]


lemma BoundedNerode.mono {n : ℕ} {s₁ s₂ : σ} : M.BoundedNerode (n + 1) s₁ s₂ → M.BoundedNerode n s₁ s₂ := by
  simp_all [BoundedNerode, Distinguishes]
  intros h w hw
  apply h
  linarith

/-- `BoundedNerode (n + 1)` (not-strictly) refines `BoundedNerode n` -/
lemma BoundedNerode.setoid_mono (M : AccessibleFinDFA α σ) (n : ℕ) :
    BoundedNerode.setoid M (n + 1) ≤ BoundedNerode.setoid M n:= by
  simp_all [Setoid.le_def, BoundedNerode]
  intros s₁ s₂ h w hw
  refine h w ?_
  linarith

-- TODO: Remove this lemma? it is unused in the proceding
lemma BoundedNerode.setoid_eq_iff (M : AccessibleFinDFA α σ) (n m : ℕ) :
    BoundedNerode.setoid M n = BoundedNerode.setoid M m ↔
    M.BoundedNerode n = M.BoundedNerode m := by
  constructor
  · intro h
    simp_all [BoundedNerode.setoid]
    apply congrArg (fun s ↦ s.r) at h
    simp_all
  · intro h
    apply Setoid.ext
    simp_all [BoundedNerode.setoid]

/-- `BoundedNerode (n + 1)` strictly refines `BoundedNerode n` if they are not equal-/
lemma BoundedNerode.setoid_mono' (M : AccessibleFinDFA α σ) (n : ℕ)
  (hneq : M.BoundedNerode n ≠ M.BoundedNerode (n + 1)) :
    BoundedNerode.setoid M (n + 1) < BoundedNerode.setoid M n := by
  simp_all [lt_iff_le_and_ne]
  constructor
  · apply BoundedNerode.setoid_mono M n
  · by_contra h
    apply hneq
    simp_all [BoundedNerode.setoid]
    apply congrArg (fun s ↦ s.r) at h
    simp_all



/-- If `BoundedNerode n` is not equal to `BoundedNerode n+1`, then there exists
some states `s₁ s₂` which are indistinguishable by words of length up to `n`
but are distinguished by some word of length `n + 1`-/
lemma BoundedNerode.neq_implies_distinguishes {n : ℕ}
  (hneq : M.BoundedNerode n ≠ M.BoundedNerode (n + 1)) :
    ∃ (s₁ s₂ : σ), M.BoundedNerode n s₁ s₂ ∧
      ∃ (w : List α), (w.length = n + 1) ∧ M.Distinguishes w s₁ s₂ := by
  by_contra hexists
  apply hneq
  ext s₁ s₂
  constructor
  · intros h
    simp_all
    have h₂ := hexists s₁ s₂ h
    simp_all only [BoundedNerode]
    intros w hw
    have hw : w.length = n + 1 ∨ w.length ≤ n := by omega
    rcases hw with (hw | hw)
    · apply h₂
      exact hw
    · apply h
      exact hw
  · intros h
    apply BoundedNerode.mono
    exact h

/-- If `BoundedNerode n = BoundedNerode n+1`,
then `BoundedNerode n=1 = BoundedNerode n+2`-/
lemma BoundedNerode_stable_succ (M : AccessibleFinDFA α σ) (n : ℕ)
  (heq : M.BoundedNerode n = M.BoundedNerode (n + 1)) :
    M.BoundedNerode (n + 1) = M.BoundedNerode (n + 2) := by
  by_contra hneq
  -- There exists some states `s₁, s₂`, and some word `w` of length `n+2`
  -- Such that `BoundedNerode n+1 s₁ s₂`, but `Distinguishes w s₁ s₂`
  obtain ⟨s₁, s₂, hind, w, wlen, hdist⟩ := BoundedNerode.neq_implies_distinguishes M hneq
  have hwPos : w ≠ [] := by aesop
  have hw : w = w.head hwPos :: w.tail := by
    rw [List.cons_head_tail hwPos]
  rw [hw] at hdist
  have hw₁ : w.tail.length = n + 1 := by simp; omega
  -- Thus, `w.tail` distinguishes `M.step s₁ a` and `M.step s₂ a`
  rw [Distinguishes.iff_step] at hdist
  -- Thus, `M.step s₁ a` and `M.step s₂ a` are distinguishable by a word of length `≤ n + 1`
  have hdist' : ¬ M.BoundedNerode (n + 1) (M.step s₁ (w.head hwPos)) (M.step s₂ (w.head hwPos)) := by
    simp [BoundedNerode]
    use w.tail
    constructor
    · omega
    · exact hdist
  -- Thus, `M.step s₁ a` and `M.step s₂ a` are distinguishable by a word of length `≤ n`
  have hdist'' : ¬ M.BoundedNerode n (M.step s₁ (w.head hwPos)) (M.step s₂ (w.head hwPos)) := by
    rw [heq]
    exact hdist'
  apply BoundedNerode.exists_distinguishes at hdist''
  -- `t` (length n) distinguishes `M.step s₁ a` and `M.step s₂ a`
  obtain ⟨t, htlen, htdist⟩ := hdist''
  -- Thus, `a :: t` (length n + 1) distinguishes `s₁` and `s₂`
  rw [← Distinguishes.iff_step] at htdist
  -- Thus, `s₁ ` and `s₂` are distinguishable by a word of length `≤ n + 1`
  have hdist''' : ¬ M.BoundedNerode (n + 1) s₁ s₂ := by
    simp [BoundedNerode]
    use (w.head hwPos :: t)
    constructor
    · simp [htlen]
    · exact htdist
  contradiction

/-- if `BoundedNerode n = BoundedNerode n+1`,
then `BoundedNerode m = BoundedNerode n` for all m ≥ n -/
lemma BoundedNerode_stable (M : AccessibleFinDFA α σ) {n : ℕ}
  (heq : M.BoundedNerode n = M.BoundedNerode (n + 1)) {m : ℕ} (hle : n ≤ m) :
    M.BoundedNerode n = M.BoundedNerode m := by
  induction hd : (m - n) generalizing m n heq with
  | zero =>
    have heq : m = n := by grind
    simp_all
  | succ o ih =>
    have heq' := BoundedNerode_stable_succ M n heq
    have hm : m - (n + 1) = o := by omega
    have ih := @ih (n + 1) heq' m (by omega) hm
    rwa [← ih]













/-!
### Decidability of BoundedNerode

We define a computable version of `BoundedNerode` that quantifies over our finset
`M.getWordsLeqLength n`. Becuase this is a finite set, this version is decidable.
We then prove that this computable version is equivalent to the original one, and
thus we can transfer the decidability instance to the `BoundedNerode`.
-/

/-- We define an equivalent version of `BoundedNerode` that is based on
our `getWordsLeqLength` function from `FinDFA.Defs.lean`. -/
def BoundedNerodeComputable (M : AccessibleFinDFA α σ) (n : ℕ) (s₁ s₂ : σ) : Prop :=
  ∀ w ∈ M.getWordsLeqLength n, ((M : DFA α σ).evalFrom s₁ w ∈ M.accept ↔ (M : DFA α σ).evalFrom s₂ w ∈ M.accept)

/-- This version is Decidable 'for free' -/
instance BoundedNerodeComputable.decidable (M : AccessibleFinDFA α σ) (n : ℕ) :
    DecidableRel (M.BoundedNerodeComputable n) := by
  unfold BoundedNerodeComputable
  infer_instance

/- We prove that the computable version is equivalent to the old one -/
lemma BoundedNerodeComputable.correct (M : AccessibleFinDFA α σ) (n : ℕ) :
    M.BoundedNerode n = M.BoundedNerodeComputable n := by
  ext s₁ s₂
  constructor
  · intro h w hw
    apply h
    rw [FinDFA.getWordsLeqLength_correct] at hw
    exact hw
  · intro h w hw
    apply h
    rw [FinDFA.getWordsLeqLength_correct]
    exact hw

/- We can now translate the decidablity instance -/
instance BoundedNerode.decidable (M : AccessibleFinDFA α σ) (n : ℕ) :
    DecidableRel (M.BoundedNerode n) := by
  rw [BoundedNerodeComputable.correct M n]
  infer_instance

/- We can now translate the decidablity instance -/
instance BoundedNerode.decidableRel (M : AccessibleFinDFA α σ) (n : ℕ) :
    DecidableRel (BoundedNerode.setoid M n) := by
  simp [BoundedNerode.setoid]
  rw [BoundedNerodeComputable.correct M n]
  infer_instance

/-- We can enumerate the elements of the quotient type of the equivalence
classes of the `BoundedNerode` relation -/
instance BoundedNerode.QuotientFintype (M : AccessibleFinDFA α σ) (n : ℕ) :
    Fintype (Quotient (BoundedNerode.setoid M n)) := by
  apply @Quotient.fintype σ σFin
          (BoundedNerode.setoid M n)
          (BoundedNerode.decidable M n)

/-- We have decidable equality on the quotient
of the state space by the `BoundedNerode` relation -/
instance BoundedNerode.DecidableEq (M : AccessibleFinDFA α σ) (n : ℕ) :
    DecidableEq (Quotient (BoundedNerode.setoid M n)) := by
  apply @Quotient.decidableEq σ
          (BoundedNerode.setoid M n)
          (BoundedNerode.decidable M n)

end AccessibleFinDFA

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




/-- The `Finpartition` of `σ` invoded by `BoundedNerode n` -/
def BoundedNerode.finpartition (M : AccessibleFinDFA α σ) (n : ℕ) :
    Finpartition (@Finset.univ σ σFin) :=
  Finpartition.ofSetoid (BoundedNerode.setoid M n)

/-- `s₂` is in the partition of `s₁` iff they are Bounded-Nerode-Related -/
lemma BoundedNerode.mem_part_finpartition_iff (M : AccessibleFinDFA α σ) (n : ℕ) (s₁ s₂ : σ) :
    s₂ ∈ (BoundedNerode.finpartition M n).part s₁ ↔ M.BoundedNerode n s₁ s₂ := by
  simp [BoundedNerode.finpartition, Finpartition.mem_part_ofSetoid_iff_rel]

/-! The finpartition induced by `BoundedNerode (n + 1)` refines `BoundedNerode n`-/
lemma BoundedNerode.finpartition_mono (M : AccessibleFinDFA α σ) (n : ℕ) :
    BoundedNerode.finpartition M (n + 1) ≤ BoundedNerode.finpartition M n := by
  intros t ht
  have hnonempty := @Finpartition.nonempty_of_mem_parts σ σDec
    (@Finset.univ σ σFin) (BoundedNerode.finpartition M (n + 1)) t ht
  rcases hnonempty with ⟨s, hs⟩
  have ht' : t = ((BoundedNerode.finpartition M (n + 1)).part s) := by
    symm
    apply Finpartition.part_eq_of_mem
    exact ht
    exact hs
  use (BoundedNerode.finpartition M n).part s
  simp_all
  intros s₂ hs₂
  rw [BoundedNerode.mem_part_finpartition_iff] at hs₂ ⊢
  apply BoundedNerode.mono M n hs₂

lemma BoundedNerode.finpartition_card_mono (M : AccessibleFinDFA α σ) (n : ℕ) :
    (BoundedNerode.finpartition M n).parts.card ≤
    (BoundedNerode.finpartition M (n + 1)).parts.card := by
  apply Finpartition.card_mono
  apply BoundedNerode.finpartition_mono M n

lemma BoundedNerode.finpartition_card_le (M : AccessibleFinDFA α σ) (n : ℕ) :
    (BoundedNerode.finpartition M n).parts.card ≤ Fintype.card σ := by
  apply Finpartition.card_parts_le_card

lemma BoundedNerode.finpartition_card_pos (M : AccessibleFinDFA α σ) (n : ℕ):
    0 ≤ (BoundedNerode.finpartition M n).parts.card := by
  simp




lemma BoundedNerode_start (M : AccessibleFinDFA α σ) :
    Fintype.card (Quotient (BoundedNerode.setoid M 0)) = 2 := by
  sorry

lemma BoundedNerode_max (M : AccessibleFinDFA α σ) (n : ℕ) :
    Fintype.card (Quotient (BoundedNerode.setoid M n)) ≤ Fintype.card σ := by
  sorry

lemma BoundedNerode_eq (M : AccessibleFinDFA α σ) (n : ℕ) :
    M.BoundedNerode n = M.BoundedNerode (n + 1) → M.BoundedNerode n = M.NerodeEquiv := by
  sorry

theorem BoundedNerode_eq_nerode (M : AccessibleFinDFA α σ) :
    M.BoundedNerode (Fintype.card σ) = M.NerodeEquiv := by
  sorry

/-! ### Decidability of NerodeEquiv -/

/-- We have a decidable procedure for testing if two
states of an `AccessibleFinDFA` are Nerode Equivalent.-/
instance NerodeEquiv_decidable (M : AccessibleFinDFA α σ) :
    DecidableRel (M.NerodeEquiv) := by
  rw [← BoundedNerode_eq_nerode M]
  apply BoundedNerode.decidable

/-- A `Fintype` instance on the quotient of the state type of a `AccessibleFinDFA`
by the Nerode equivalence relation -/
instance NerodeEquiv_quotient_fintype (M : AccessibleFinDFA α σ) :
        Fintype (Quotient (NerodeEquiv.setoid M)) := by
      apply @Quotient.fintype σ σFin
              (NerodeEquiv.setoid M)
              (NerodeEquiv_decidable M)

/-- A `DecidableEq` instance on the quotient of the state type of a `AccessibleFinDFA`
by the Nerode equivalence relation -/
instance NerodeEquiv_quotient_decidableEq (M : AccessibleFinDFA α σ) :
        DecidableEq (Quotient (NerodeEquiv.setoid M)) := by
      apply @Quotient.decidableEq σ
              (NerodeEquiv.setoid M)
              (NerodeEquiv_decidable M)
