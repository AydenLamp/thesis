import MyProject.FinDFA.Accessable

/-!
# Partial order on Accessable Finite DFAs

This file defines morphisms between `AccessableFinDFA`s, which are bundled functions
between the state spaces which respect the transition functions, start state,
and accept states of the DFAs.

We define a partial order on `AccessableFinDFA`s where `M ≤ N`
if there exists a surjective `AccessableFinDFA` morphism from `N` to `M`.

## Main Definitions

 * `AccessableFinDFA.Morphism M N` : A morphism from the `AccessableFinDFA` `M`
 to the `AccessableFinDFA` `N`, notated `M →ₗ N`.
 * `AccessableFinDFA.Equiv M N` : An equivalence of `AccessableFinDFA`s,
  which is a bijective morphism, notated `M ≃ₗ N`.
 * `AccessableFinDFA.le` : The partial order on accessable `AccessableFinDFA`s.

## Main Theorems

* `AccessableFinDFA.morphism_pres_language` : The existance of a morphism
from `M` to `N` implies that `M` accepts the same language as `N`.
* `AccessableFinDFA.le_refl` : The relation `le` is reflexive.
* `AccessableFinDFA.le_trans` : The relation `le` is transitive.
* `AccessableFinDFA.le_antisymm` : The relation `le` is antisymmetric up to `AccessableFinDFA` equivalence.

## Noations

 * `M →ₗ N` : Notation for `AccessableFinDFA.Morphism M N`.
 * `M ≃ₗ N` : Notation for `AccessableFinDFA.Equiv M N`.
 * `M ≤ N` : Notation for `AccessableFinDFA.le M N`.
-/

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {σ₁ : Type*} [Fintype σ₁] [DecidableEq σ₁]
variable {σ₂ : Type*} [Fintype σ₂] [DecidableEq σ₂]
variable {σ₃ : Type*} [Fintype σ₃] [DecidableEq σ₃]


structure AccessableFinDFA.Hom (M : AccessableFinDFA α σ₁) (N : AccessableFinDFA α σ₂) where
  /-- The underlying function map from States of `M` to States of `N` -/
  toFun : σ₁ → σ₂
  /-- The proposition that the function preserves the start state-/
  map_start : toFun M.start = N.start
  /-- The proposition that the function preserves the set of accepting states -/
  map_accept (q : σ₁) : q ∈ M.accept ↔ toFun q ∈ N.accept
  /-- The proposition that the function preserves state transitions -/
  map_step (q : σ₁) (w : List α) : toFun (M.evalFrom q w) = N.evalFrom (toFun q) w

/-- `M →ₗ N` denotes the type of `AccessableFinDFA M N` -/
infixr:25 " →ₗ " => AccessableFinDFA.Hom

namespace AccessableFinDFA.Hom

variable {M : AccessableFinDFA α σ₁} {N : AccessableFinDFA α σ₂}

/-- The existance of `f : M →ₗ N` implies that the language of `M` equal to the language of `N`-/
theorem language_contained (f : M →ₗ N) : M.accepts = N.accepts := by
  ext w
  simp_all [M.mem_accepts, N.mem_accepts]
  have h : N.eval w ∈ N.accept ↔ N.evalFrom N.start w ∈ N.accept := by rfl
  rw [h]
  have h : M.eval w ∈ M.accept ↔ M.evalFrom M.start w ∈ M.accept := by rfl
  rw [h]; clear h
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


end AccessableFinDFA.Hom

structure AccessableFinDFA.Equiv (M : AccessableFinDFA α σ₁) (N : AccessableFinDFA α σ₂) where
  toHom : M →ₗ N
  toInvHom : N →ₗ M
  left_inv : Function.LeftInverse toInvHom.toFun toHom.toFun
  right_inv : Function.RightInverse toInvHom.toFun toHom.toFun

variable {M : DFA α σ₁} {N : DFA α σ₂}

/-- `M ≃ₗ N` denotes the type of `AccessableFinDFA.Equiv M N` -/
infixr:25 " ≃ₗ " => AccessableFinDFA.Equiv

/-- A structure for surjective Morphisms of Accessable DFAs -/
structure AccessableFinDFA.HomSurj (M : AccessableFinDFA α σ₁) (N : AccessableFinDFA α σ₂)
    extends M →ₗ N where
  /-- The proposition that the function is surjective -/
  surjective : Function.Surjective toFun

/-- `M ↠ N` denotes the type of `AccessableFinDFA.HomSurj M N` -/
infixr:25 " ↠ " => AccessableFinDFA.HomSurj

def AccessableFinDFA.HomSurj.rfl (M : AccessableFinDFA α σ) : M ↠ M where
  toFun := id
  map_start := by rfl
  map_accept := by intros q; simp
  map_step := by intros q w; simp
  surjective := by simp [Function.Surjective]

/-!
### Partial Order

We define a partial order on Accessable DFAs.
Let `M : AccessableDFA α σ₁` and `N : AccessableDFA α σ₂`
We say `M ≤ N` if there is a surjective morphism from `N` to `M`.

This is not technically a partial order becuase it is not antisymmetric,
`M ≤ N ∧ N ≤ M` implies `M ≃ₗ N` but not `M = N`
-/

namespace AccessableFinDFA

def le (M : AccessableFinDFA α σ₁) (N : AccessableFinDFA α σ₂) : Prop := Nonempty (N ↠ M)

infix:50 " ≤ " => le

lemma le_refl (M : AccessableFinDFA α σ₁) : M ≤ M := by
  simp [le]
  apply Nonempty.intro
  exact AccessableFinDFA.HomSurj.rfl M

lemma le_trans {M : AccessableFinDFA α σ₁} {N : AccessableFinDFA α σ₂} {O : AccessableFinDFA α σ₃}
    (h₁ : M ≤ N) (h₂ : N ≤ O) : M ≤ O := by
  obtain f := h₁.some
  obtain g := h₂.some
  apply Nonempty.intro
  let h : O →ₗ M := by
    apply AccessableFinDFA.Hom.mk
      (toFun := f.toFun ∘ g.toFun)
      (map_start := by
        simp [Function.comp, f.map_start, g.map_start])
      (map_accept := by
        intros q
        simp [Function.comp]
        rw [g.map_accept, f.map_accept])
      (map_step := by
        intros q w
        simp [Function.comp]
        rw [g.map_step, f.map_step])
  apply AccessableFinDFA.HomSurj.mk h
  have h₁ : h.toFun = f.toFun ∘ g.toFun := by rfl
  rw [h₁]
  apply Function.Surjective.comp
  · exact f.surjective
  · exact g.surjective

lemma le_antisymm (M : AccessableFinDFA α σ₁) (N : AccessableFinDFA α σ₂) (h₁ : M ≤ N) (h₂ : N ≤ M) :
    Nonempty (M ≃ₗ N) := by
  let f' := h₁.some.toHom
  let g' := h₂.some.toHom
  apply Nonempty.intro
  apply AccessableFinDFA.Equiv.mk
    (toHom := g')
    (toInvHom := f')
    (left_inv := by
      simp_all [Function.LeftInverse]
      intro s
      obtain ⟨w, hs⟩ := M.step_accessable' s
      rw [← hs]
      rw [g'.map_step, f'.map_step]
      rw [g'.map_start, f'.map_start] )
    (right_inv := by
      simp_all [Function.RightInverse]
      intros s
      obtain ⟨w, hs⟩ := N.step_accessable' s
      rw [← hs]
      rw [f'.map_step, g'.map_step, f'.map_start, g'.map_start] )

/-- The proposition saying that `M` is minimal for this preorder-/
def isMinimal (M : AccessableFinDFA α σ₁) : Prop :=
  ∀ {σ : Type*} [Fintype σ] [DecidableEq σ] (N : AccessableFinDFA α σ),
  (M.accepts = N.accepts) → M ≤ N

end AccessableFinDFA
