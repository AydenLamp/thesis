
/-!
### Bounded Nerode Monotonicity and Stabilization

We prove that `BoundedNerode (n+1)` refines `BoundedNerode n` and deduce that the number of
equivalence classes is monotone nondecreasing in `n`. We also provide a local-step characterization
of `BoundedNerode (n+1)` in terms of acceptance at the current states and `BoundedNerode n` on
all single-letter successors. Finally, we sketch stabilization lemmas showing that once the
relation stabilizes at some `n`, it remains stable thereafter, and that at or before `|σ|` it
stabilizes to the full Nerode equivalence.
-/

/-- `BoundedNerode (n+1)` refines `BoundedNerode n`. -/
lemma BoundedNerode_mono (M : AccessibleFinDFA α σ) (n : ℕ) :
    BoundedNerode.setoid M (n + 1) ≤ BoundedNerode.setoid M n := by
  simp [Setoid.le_def]
  intro s₁ s₂ h
  intro w hw
  have : w.length ≤ n + 1 := Nat.le_trans hw (Nat.le_succ n)
  exact h w this

/-- Monotonicity of the number of equivalence classes: the quotient by `n` injects into
    the quotient by `n+1` via the surjective map in the opposite direction. -/
lemma BoundedNerode_card_mono (M : AccessibleFinDFA α σ) (n : ℕ) :
    Fintype.card (Quotient (BoundedNerode.setoid M n)) ≤
    Fintype.card (Quotient (BoundedNerode.setoid M (n + 1))) := by
  -- Use the natural surjection Quot (n+1) → Quot n induced by refinement
  let f : Quotient (BoundedNerode.setoid M (n + 1)) → Quotient (BoundedNerode.setoid M n) :=
    Quot.map (id)
      (by
        intro a b h
        exact (fun w hw => h w (Nat.le_trans hw (Nat.le_succ n))))
  -- Surjectivity: every class at level n is the image of the same representative's class at n+1
  have hsurj : Function.Surjective f := by
    intro q
    refine Quot.inductionOn q (fun s => ?_)
    refine ⟨Quot.mk _ s, ?_⟩
    rfl
  -- Cardinality inequality from surjection between finite types
  simpa using (Fintype.card_le_of_surjective f hsurj)

/-- Local characterization of `BoundedNerode (n+1)`.
It holds iff (1) the current states agree on acceptance and (2) for all letters `a`,
`BoundedNerode n` holds on the successors. -/
lemma BoundedNerode_succ_iff (M : AccessibleFinDFA α σ) (n : ℕ) (s₁ s₂ : σ) :
    M.BoundedNerode (n + 1) s₁ s₂ ↔
      ((s₁ ∈ M.accept) ↔ (s₂ ∈ M.accept)) ∧
      (∀ a : α, M.BoundedNerode n (M.step s₁ a) (M.step s₂ a)) := by
  sorry

/-- If the chain strictly refines at step `n → n+1`, there is a distinguishing witness of
length `n+1`. -/
lemma BoundedNerode_neq_implies_exists (M : AccessibleFinDFA α σ) {n : ℕ}
  (hneq : M.BoundedNerode n ≠ M.BoundedNerode (n + 1)) :
    ∃ (s₁ s₂ : σ) (w : List α), w.length = n + 1 ∧
    M.BoundedNerode n s₁ s₂ ∧ ¬ M.BoundedNerode (n + 1) s₁ s₂ := by
  sorry

/-- Stability step: if it stabilizes at `n`, it also stabilizes at `n+1`. -/
lemma BoundedNerode_stable_succ (M : AccessibleFinDFA α σ) (n : ℕ)
  (heq : M.BoundedNerode n = M.BoundedNerode (n + 1)) :
    M.BoundedNerode (n + 1) = M.BoundedNerode (n + 2) := by
  sorry

/-- Once stabilized, always stabilized. -/
lemma BoundedNerode_stable (M : AccessibleFinDFA α σ) (n : ℕ) :
    (M.BoundedNerode n = M.BoundedNerode (n + 1)) →
    ∀ m, m ≥ n → M.BoundedNerode n = M.BoundedNerode m := by
  intro h m hm
  induction' (m - n) with k hk generalizing m
  · have heq : m = n := by
      sorry
    simp [heq]
  · sorry

/-- General upper bound on the number of equivalence classes. -/
lemma BoundedNerode_max (M : AccessibleFinDFA α σ) (n : ℕ) :
    Fintype.card (Quotient (BoundedNerode.setoid M n)) ≤ Fintype.card σ := by
  classical
  let f : σ → Quotient (BoundedNerode.setoid M n) := fun s => Quot.mk _ s
  have hsurj : Function.Surjective f := by
    intro q
    refine Quot.inductionOn q (fun s => ?_)
    exact ⟨s, rfl⟩
  simpa using (Fintype.card_le_of_surjective f hsurj)

/-- If stability holds at step `n`, the bounded relation equals the full Nerode equivalence. -/
lemma BoundedNerode_eq (M : AccessibleFinDFA α σ) (n : ℕ) :
    M.BoundedNerode n = M.BoundedNerode (n + 1) → M.BoundedNerode n = M.NerodeEquiv := by
  sorry

/-- The bounded relation stabilizes to Nerode at or before `|σ|`. -/
theorem BoundedNerode_eq_nerode (M : AccessibleFinDFA α σ) :
    M.BoundedNerode (Fintype.card σ) = M.NerodeEquiv := by
  sorry

instance NerodeEquiv_decidable (M : AccessibleFinDFA α σ) :
    DecidableRel (M.NerodeEquiv) := by
  rw [← BoundedNerode_eq_nerode M]
  apply BoundedNerode.decidable

instance NerodeEquiv_quotient_fintype (M : AccessibleFinDFA α σ) :
        Fintype (Quotient (NerodeEquiv.setoid M)) := by
      apply @Quotient.fintype σ σFin
              (NerodeEquiv.setoid M)
              (NerodeEquiv_decidable M)

instance NerodeEquiv_quotient_decidableEq (M : AccessibleFinDFA α σ) :
        DecidableEq (Quotient (NerodeEquiv.setoid M)) := by
      apply @Quotient.decidableEq σ
              (NerodeEquiv.setoid M)
              (NerodeEquiv_decidable M)
