import MyProject.FinDFA.Defs

/-!
# Morphisms between DFAs

This file defines morphisms between DFAs, which are bundled functions between the state spaces
which respect the transition function, start state, and accept states of the DFAs.

We then define a partial order on `AccessibleFinDFA`s where `M ≤ N` iff there exists a surjective
morphism from `N.toDFA` to `M.toDFA`.

## Main Definitions

* `DFA.Hom` - A morphism from the `DFA` `M` to the `DFA` `N`, notated `M →ₗ N`.

* `DFA.Equiv` - An equivalence of `DFA`s, which is a bijective morphism, notated `M ≃ₗ N`.

* `AccessibleFinDFA.HomSurj` - A morphism on the underlying `DFA`s of the `AccessibleFinDFA`s
  which is surjective on states. Notated `M ↠ N`.

* `AccessibleFinDFA.le` - Notated `≤`, the partial order on `AccessibleFinDFA`s.

* `AccessibleFinDFA.isMinimal` - A predicate that `M` is minimal by the partial order, up to
  equivalence of the underlying `DFA`s.

## Main Theorems

* `DFA.hom_pres_lang` - The existence of `f : M →ₗ N` implies that the language of `M` equals
  the language of `N`.

We prove that the relation `≤` is a partial order (up to equivalence of underlying DFAs):
* `AccessibleFinDFA.le_refl` - Reflexivity.
* `AccessibleFinDFA.le_trans` - Transitivity.
* `AccessibleFinDFA.le_antisymm` - Antisymmetry up to equivalence of the underlying DFAs.

## Notation

* `M →ₗ N` - Notation for `DFA.Hom M N`.
* `M ≃ₗ N` - Notation for `DFA.Equiv M N`.
* `M ↠ N` - Notation for `AccessibleFinDFA.HomSurj M N`.
* `M ≤ N` - Notation for the partial order on `AccessibleFinDFA`s.
-/

namespace DFA

universe u v w

set_option linter.unusedSectionVars false

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {σ₁ : Type v} [Fintype σ₁] [DecidableEq σ₁]
variable {σ₂ : Type w} [Fintype σ₂] [DecidableEq σ₂]

/-- A morphism of DFAs from `M` to `N`. -/
structure Hom (M : DFA α σ₁) (N : DFA α σ₂) where
  /-- Underlying function map from states of `M` to states of `N`. -/
  toFun : σ₁ → σ₂
  /-- The function preserves the start state. -/
  map_start : toFun M.start = N.start
  /-- The function preserves the set of accepting states. -/
  map_accept (q : σ₁) : q ∈ M.accept ↔ toFun q ∈ N.accept
  /-- The function preserves state transitions. -/
  map_step (q : σ₁) (w : List α) : toFun (M.evalFrom q w) = N.evalFrom (toFun q) w

/-- `M →ₗ N` denotes the type of `DFA.Hom M N`. -/
infixr:25 " →ₗ " => Hom

variable {M : DFA α σ₁} {N : DFA α σ₂}

/-- A morphism preserves the accepted language. -/
theorem hom_pres_lang (f : M →ₗ N) : M.accepts = N.accepts := by
  ext w
  simp_all [mem_accepts, eval]
  constructor
  · intro h
    rw [f.map_accept] at h
    rw [f.map_step M.start w] at h
    rw [f.map_start] at h
    exact h
  · intro h
    rw [f.map_accept]
    rw [f.map_step M.start w]
    rw [f.map_start]
    exact h

/-- The identity morphism on a DFA. -/
def homRefl (M : DFA α σ₁) : M →ₗ M where
  toFun := id
  map_start := by rfl
  map_accept := by intro q; simp
  map_step := by intro q w; simp

/-- An equivalence of DFAs is a bijective morphism. -/
structure Equiv (M : DFA α σ₁) (N : DFA α σ₂) where
  toDFAHom : M →ₗ N
  toInvDFAHom : N →ₗ M
  left_inv : Function.LeftInverse toInvDFAHom.toFun toDFAHom.toFun
  right_inv : Function.RightInverse toInvDFAHom.toFun toDFAHom.toFun

/-- `M ≃ₗ N` denotes the type of `DFA.Equiv M N`. -/
infixr:25 " ≃ₗ " => Equiv

/-- The identity equivalence on a DFA. -/
def equivRefl (M : DFA α σ₁) : M ≃ₗ M where
  toDFAHom := homRefl M
  toInvDFAHom := homRefl M
  left_inv := by tauto
  right_inv := by tauto

end DFA

/-! ### Surjective Morphisms of AccessibleFinDFAs -/

namespace AccessibleFinDFA

universe u v w x

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {σ₁ : Type v} [Fintype σ₁] [DecidableEq σ₁]
variable {σ₂ : Type w} [Fintype σ₂] [DecidableEq σ₂]
variable {σ₃ : Type x} [Fintype σ₃] [DecidableEq σ₃]

/-- A surjective morphism between the underlying DFAs of `AccessibleFinDFA`s. -/
structure HomSurj (M : AccessibleFinDFA α σ₁) (N : AccessibleFinDFA α σ₂)
    extends f : (M : DFA α σ₁) →ₗ (N : DFA α σ₂) where
  /-- The function is surjective. -/
  surjective : Function.Surjective f.toFun

/-- `M ↠ N` denotes the type of `AccessibleFinDFA.HomSurj M N`. -/
infixr:25 " ↠ " => HomSurj

/-- Forget the surjectivity proof and view `HomSurj` as a DFA morphism. -/
@[simp] def HomSurj.toDFAHom {M : AccessibleFinDFA α σ₁} {N : AccessibleFinDFA α σ₂}
  (f : M ↠ N) : (M : DFA α σ₁) →ₗ (N : DFA α σ₂) where
  toFun := f.toFun
  map_start := f.map_start
  map_accept := f.map_accept
  map_step := f.map_step

/-! ### Partial Order on AccessibleFinDFAs -/

/-- The preorder on `AccessibleFinDFA`s: `M ≤ N` iff there is a surjective morphism `N ↠ M`. -/
def le (M : AccessibleFinDFA α σ₁) (N : AccessibleFinDFA α σ₂) : Prop :=
  Nonempty (N ↠ M)

/-- `M ≤ N` denotes the proposition `le M N`. -/
infix:25 " ≤ " => le

/-- Reflexivity of `≤`. -/
lemma le_refl (M : AccessibleFinDFA α σ₁) : M ≤ M := by
  simp [le]
  refine ⟨?f⟩
  refine AccessibleFinDFA.HomSurj.mk (DFA.homRefl M.toDFA) ?_
  intro s
  exact ⟨s, rfl⟩

/-- Transitivity of `≤`. -/
lemma le_trans {M : AccessibleFinDFA α σ₁} {N : AccessibleFinDFA α σ₂}
  {O : AccessibleFinDFA α σ₃} (h₁ : M ≤ N) (h₂ : N ≤ O) : M ≤ O := by
  obtain f := h₁.some
  obtain g := h₂.some
  refine ⟨?_⟩
  -- Compose the underlying DFA morphisms and show surjectivity.
  let I : O.toDFA →ₗ M.toDFA := by
    refine DFA.Hom.mk
      (toFun := f.toFun ∘ g.toFun)
      (map_start := by
        simp
        have hg := g.map_start
        have hf := f.map_start
        simp_all)
      (map_accept := by
        intro q
        simp_all
        have hg := g.map_accept q
        have hf := f.map_accept (g.toFun q)
        simp_all)
      (map_step := by
        intro q w
        simp_all
        have hg := g.map_step q w
        have hf := f.map_step (g.toFun q) w
        simp_all)
  refine AccessibleFinDFA.HomSurj.mk I ?_
  -- Surjectivity of the composition.
  have hI : I.toFun = f.toFun ∘ g.toFun := rfl
  simpa [hI] using Function.Surjective.comp f.surjective g.surjective

/-- Antisymmetry of `≤` up to equivalence of the underlying DFAs. -/
lemma le_antisymm (M : AccessibleFinDFA α σ₁) (N : AccessibleFinDFA α σ₂)
    (h₁ : M ≤ N) (h₂ : N ≤ M) :
    Nonempty ((M : DFA α σ₁) ≃ₗ (N : DFA α σ₂)) := by
  obtain f := h₁.some
  obtain g := h₂.some
  refine ⟨?_⟩
  refine DFA.Equiv.mk
    (toDFAHom := g.toDFAHom)
    (toInvDFAHom := f.toDFAHom)
    (left_inv := by
      -- Use accessibility to move back to the start state, then cancel via maps.
      simp_all [Function.LeftInverse]
      intro s
      obtain ⟨w, hs⟩ := M.is_accessible s
      rw [← hs]
      have hg₁ := g.map_step M.start w
      have hf₁ := f.map_step (g.toFun M.start) w
      have hg₂ := g.map_start
      have hf₂ := f.map_start
      rw [← hg₁] at hf₁
      simp_all)
    (right_inv := by
      simp_all [Function.RightInverse]
      intro s
      obtain ⟨w, hs⟩ := N.is_accessible s
      rw [← hs]
      have hg₁ := g.map_step M.start w
      have hf₁ := f.map_step (g.toFun M.start) w
      have hg₂ := g.map_start
      have hf₂ := f.map_start
      rw [← hg₁] at hf₁
      simp_all)

set_option linter.unusedVariables false in

/-- `M` is minimal for this preorder if every `N ≤ M` is equivalent to `M` as a DFA. -/
def isMinimal (M : AccessibleFinDFA α σ₁) (N : AccessibleFinDFA α σ₂) (hle : N ≤ M) : Prop :=
  Nonempty ((M : DFA α σ₁) ≃ₗ (N : DFA α σ₂))

end AccessibleFinDFA
