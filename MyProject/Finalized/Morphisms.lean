import MyProject.Finalized.FinDFA

/-!
# Morphisms between DFAs

This file defines morphisms between DFAs, which are bundled functions between the state spaces
which respect the transition function, start state, and accept states of the DFAs.

We then define a partial order on `AccessibleFinDFA`s where `M ≤ N` iff there exists a
surjective morphism from `N.toDFA` to `M.toDFA`.

## Main Definitions

* `DFA.Hom` : A morphism from the `DFA` `M` to the `DFA` `N`, notated `M →ₗ N`.
* `DFA.Equiv` : An equivalence of `DFA`s, which is a bijective morphism, notated `M ≃ₗ N`.
* `AccessibleFinDFA.HomSurj` : A morphism on the underlying `DFA`s of the `AccessibleFinDFA`s
which is surjective on states. Notated `M ↠ N`.
* `AccessibleFinDFA.le` : The partial order on `AccessibleFinDFA`s.
* `AccessibleFinDFA.isMinimal` : A predicate that `M` is minimal by the partial order, up to
equivalence of the underlying `DFA`s.

## Main Theorems

* `DFA.Hom_pres_language` : The existence of `f : M →ₗ N` implies that the language of `N`
equals the language of `M`.
* `AccessibleFinDFA.le_refl` : The relation `le` is reflexive.
* `AccessibleFinDFA.le_trans` : The relation `le` is transitive.
* `AccessibleFinDFA.le_antisymm` : The relation `le` is antisymmetric up
to equivalence of the underlying DFAs.

## Notation

* `M →ₗ N` : Notation for `DFA.Hom M N`.
* `M ≃ₗ N` : Notation for `DFA.Equiv M N`.
* `M ↠ N` : Notation for `AccessibleFinDFA.HomSurj M N`.
* `M ≤ N` : Notation for the partial order on `AccessibleFinDFA`s.
-/

namespace DFA

universe u v w

set_option linter.unusedSectionVars false

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {σ₁ : Type v} [Fintype σ₁] [DecidableEq σ₁]
variable {σ₂ : Type w} [Fintype σ₂] [DecidableEq σ₂]

structure Hom (M : DFA α σ₁) (N : DFA α σ₂) where
  /-- The underlying function map from States of `M` to States of `N` -/
  toFun : σ₁ → σ₂
  /-- The proposition that the function preserves the start state-/
  map_start : toFun M.start = N.start
  /-- The proposition that the function preserves the set of accepting states -/
  map_accept (q : σ₁) : q ∈ M.accept ↔ toFun q ∈ N.accept
  /-- The proposition that the function preserves state transitions -/
  map_step (q : σ₁) (w : List α) : toFun (M.evalFrom q w) = N.evalFrom (toFun q) w

/-- `M →ₗ N` denotes the type of `DFAHom M N` -/
infixr:25 " →ₗ " => Hom

variable {M : DFA α σ₁} {N : DFA α σ₂}

/-- The existance of `f : M →ₗ N` implies that the language of `M` equal to the language of `N`-/
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

/-- The morphism from a DFA to itself -/
def homRefl (M : DFA α σ₁) : M →ₗ M where
  toFun := id
  map_start := by rfl
  map_accept := by intros q; simp
  map_step := by intros q w; simp

/-- An equivalence of DFAs is a bijective morphism -/
structure Equiv (M : DFA α σ₁) (N : DFA α σ₂) where
  toDFAHom : M →ₗ N
  toInvDFAHom : N →ₗ M
  left_inv : Function.LeftInverse toInvDFAHom.toFun toDFAHom.toFun
  right_inv : Function.RightInverse toInvDFAHom.toFun toDFAHom.toFun

/-- `M ≃ₗ N` denotes the type of `DFA.equiv M N` -/
infixr:25 " ≃ₗ " => Equiv

def equivRefl (M : DFA α σ₁) : M ≃ₗ M where
  toDFAHom := homRefl M
  toInvDFAHom := homRefl M
  left_inv := by tauto
  right_inv := by tauto

end DFA

/-! ### Surjective Morphisms of AccessibleFinDFAs-/

namespace AccessibleFinDFA

universe u v w x

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {σ₁ : Type v} [Fintype σ₁] [DecidableEq σ₁]
variable {σ₂ : Type w} [Fintype σ₂] [DecidableEq σ₂]
variable {σ₃ : Type x} [Fintype σ₃] [DecidableEq σ₃]

structure HomSurj (M : AccessibleFinDFA α σ₁) (N : AccessibleFinDFA α σ₂)
    extends f : (M : DFA α σ₁) →ₗ (N : DFA α σ₂) where
  /-- The proposition that the function is surjective -/
  surjective : Function.Surjective f.toFun

infixr:25 " ↠ " => HomSurj

@[simp] def HomSurj.toDFAHom {M : AccessibleFinDFA α σ₁} {N : AccessibleFinDFA α σ₂} (f : M ↠ N) :
    (M : DFA α σ₁) →ₗ (N : DFA α σ₂) where
  toFun := f.toFun
  map_start := f.map_start
  map_accept := f.map_accept
  map_step := f.map_step

/-! ### Partial Order on AccessibleFinDFAs-/

/-- The partial order on `AccessibleFinDFA`s -/
def le (M : AccessibleFinDFA α σ₁) (N : AccessibleFinDFA α σ₂) : Prop := Nonempty (N ↠ M)

/-- `M ≤ N` denotes the proposition `le M N` -/
infix:25 " ≤ " => le

/-- The relation `le` is reflexive -/
lemma le_refl (M : AccessibleFinDFA α σ₁) : M ≤ M := by
  simp [le]
  apply Nonempty.intro
  apply AccessibleFinDFA.HomSurj.mk (DFA.homRefl M.toDFA)
  simp_all [Function.Surjective]
  intros s
  use s
  rfl

/-- The relation `le` is transitive-/
lemma le_trans {M : AccessibleFinDFA α σ₁} {N : AccessibleFinDFA α σ₂} {O : AccessibleFinDFA α σ₃}
    (h₁ : M ≤ N) (h₂ : N ≤ O) : M ≤ O := by
  obtain f := h₁.some
  obtain g := h₂.some
  apply Nonempty.intro
  let I : O.toDFA →ₗ M.toDFA := by
    apply DFA.Hom.mk
      (toFun := f.toFun ∘ g.toFun)
      (map_start := by
        simp
        have hg := g.map_start
        have hf := f.map_start
        simp_all)
      (map_accept := by
        intros q
        simp_all
        have hg := g.map_accept q
        have hf := f.map_accept (g.toFun q)
        simp_all)
      (map_step := by
        intros q w
        simp_all
        have hg := g.map_step q w
        have hf := f.map_step (g.toFun q) w
        simp_all)
  apply AccessibleFinDFA.HomSurj.mk I
  have hI : I.toFun = f.toFun ∘ g.toFun := rfl
  rw [hI]
  apply Function.Surjective.comp
  · exact f.surjective
  · exact g.surjective

/-- The `le` relation is Antisymmetric up to Equivalence of the underlying DFAs -/
lemma le_antisymm (M : AccessibleFinDFA α σ₁) (N : AccessibleFinDFA α σ₂) (h₁ : M ≤ N) (h₂ : N ≤ M) :
    Nonempty ((M : DFA α σ₁) ≃ₗ (N : DFA α σ₂)) := by
  obtain f := h₁.some
  obtain g := h₂.some
  apply Nonempty.intro
  apply DFA.Equiv.mk
    (toDFAHom := g.toDFAHom)
    (toInvDFAHom := f.toDFAHom)
    (left_inv := by
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
      intros s
      obtain ⟨w, hs⟩ := N.is_accessible s
      rw [← hs]
      have hg₁ := g.map_step M.start w
      have hf₁ := f.map_step (g.toFun M.start) w
      have hg₂ := g.map_start
      have hf₂ := f.map_start
      rw [← hg₁] at hf₁
      simp_all)

set_option linter.unusedVariables false in
/-- The proposition saying that `M` is minimal for this preorder-/
def isMinimal (M : AccessibleFinDFA α σ₁) (N : AccessibleFinDFA α σ₂) (hle : N ≤ M) : Prop :=
  Nonempty ((M : DFA α σ₁) ≃ₗ (N : DFA α σ₂))

end AccessibleFinDFA
