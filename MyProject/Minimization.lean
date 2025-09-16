import Mathlib

/- # Accessable DFAs -/
section Accessable

namespace DFA

variable {α σ : Type*}

def isAccessableState (M : DFA α σ) (s : σ) : Prop := s = M.start ∨ ∃ s₂ : σ, ∃ a : α, M.step s₂ a = s

def isAccessable (M : DFA α σ) : Prop := ∀ s : σ, M.isAccessableState s

def toAccessable (M : DFA α σ) : DFA α { s // M.isAccessableState s } where
  step := fun s a => ⟨M.step s.val a, by simp_all [isAccessableState]⟩
  start := ⟨M.start, by simp_all only [isAccessableState]; left; trivial⟩
  accept := { s | s.val ∈ M.accept}

end DFA

end Accessable

/-! # DFA Morphisms -/

section Morphisms

open DFA

variable {α σ σ₁ σ₂: Type* }

structure DFAHom (M : DFA α σ₁) (N : DFA α σ₂) where
  /-- The underlying function map from States of `M` to States of `N` -/
  toFun : σ₁ → σ₂
  /-- The proposition that the function preserves the start state-/
  map_start : toFun M.start = N.start
  /-- The proposition that the function preserves the set of accepting states -/
  map_accept (q : σ₁) (h : q ∈ M.accept) : toFun q ∈ N.accept
  /-- The proposition that the function preserves state transitions -/
  map_step (q : σ₁) (w : List α) : toFun (M.evalFrom q w) = N.evalFrom (toFun q) w

/-- `M →ₗ N` denotes the type of `DFAHom M N` -/
infixr:25 " →ₗ " => DFAHom

variable {M : DFA α σ₁} {N : DFA α σ₂}

/-- The existance of `f : M →ₗ N` implies that the language of `M` is contained in the language of `N`-/
theorem DFAHom.language_contained (f : M →ₗ N) (w : List α) : w ∈ M.accepts → w ∈ N.accepts := by
  intros h
  have h₂ : (M.evalFrom M.start w) ∈ M.accept := by
    simp_all [mem_accepts, eval]
  suffices : (N.evalFrom N.start w) ∈ N.accept
  · simp_all [mem_accepts, eval]
  have h₃ := f.map_step M.start w
  rw [f.map_start] at h₃
  rw [← h₃]
  apply f.map_accept (M.evalFrom M.start w) h₂

structure DFAEquiv (M : DFA α σ₁) (N : DFA α σ₂) where
  toDFAHom : M →ₗ N
  toInvDFAHom : N →ₗ M
  left_inv : Function.LeftInverse toInvDFAHom.toFun toDFAHom.toFun
  right_inv : Function.RightInverse toInvDFAHom.toFun toDFAHom.toFun

/-- `M ≃ₗ N` denotes the type of `DFAEquiv M N` -/
infixr:25 " ≃ₗ " => DFAEquiv

theorem DFAEquiv.language_eq (f : M ≃ₗ N) : M.accepts = N.accepts := by
  ext w
  constructor
  · apply DFAHom.language_contained f.toDFAHom w
  · apply DFAHom.language_contained f.toInvDFAHom w

end Morphisms

/-! # Partial Order on DFAs
Questions: Should this partial order be defined only on DFAs with the same language?
Only on DFAs where all states are accessable (is this necessesary for antisymm?)?
For anitsymmetry, we do not use the mathlib instance because `M ≤ N` and `N ≤ M`
should only imply `M ≃ₗ N` and not `M = N`.
Must the partial order require the morphisms to be injective on states?
-/

section PartialOrder

variable {α σ₁ σ₂ σ₃: Type*}

namespace DFA

def le (M : DFA α σ₁) (N : DFA α σ₂) : Prop := Nonempty (M →ₗ N)

infix:50 " ≤ " => le

lemma le_def (M : DFA α σ₁) (N : DFA α σ₂) : M ≤ N ↔ Nonempty (M →ₗ N) := by rfl

lemma le_refl (M : DFA α σ₁): M ≤ M := by
  exact ⟨{ toFun := id, map_start := rfl, map_accept := by simp, map_step := by simp }⟩

lemma le_trans (M : DFA α σ₁) (N : DFA α σ₂) (O : DFA α σ₃) (h₁ : M ≤ N) (h₂ : N ≤ O) : M ≤ O := by
  obtain f := h₁.some
  obtain g := h₂.some
  exact ⟨{
    toFun := g.toFun ∘ f.toFun,
    map_start := by simp_all; rw [f.map_start, g.map_start]
    map_accept := by
      intros q h
      simp_all
      apply g.map_accept
      apply f.map_accept
      exact h
    map_step := by
      intros q w
      simp_all
      rw [f.map_step, g.map_step] } ⟩

/- Question: Does this only hold if all the states are accessable?
Should this order be defined on only accessable Dfas? only dfas defining the same language? -/
lemma le_antisymm (M : DFA α σ₁) (N : DFA α σ₂) (h₁ : M ≤ N) (h₂ : N ≤ M) : Nonempty (M ≃ₗ N) := by
  exact ⟨{
    toDFAHom := h₁.some,
    toInvDFAHom := h₂.some,
    left_inv := by
      intros s
      sorry
    right_inv := sorry }⟩

def isMinimal (M : DFA α σ₁) : Prop := ∀ {σ : Type*} (N : DFA α σ), (M.accepts = N.accepts) → M ≤ N

end DFA

end PartialOrder

/-! # Minimization
We first require that the DFA is accessable, then we combine states that are myhill-equivalent.
-/

section Minimization

namespace DFA

universe u v
variable {α : Type u} {σ : Type v}

def MinimizeStates (M : DFA α σ) (h : M.isAccessable) := { s : σ // 1 = 1}

def Minimize (M : DFA α σ) (h : M.isAccessable) : DFA α (M.MinimizeStates h) where
  step := sorry
  start := ⟨M.start, by sorry⟩
  accept := sorry

theorem minimize_correct (M : DFA α σ) (h : M.isAccessable) : (M.Minimize h).isMinimal := by
  sorry

end DFA

end Minimization
