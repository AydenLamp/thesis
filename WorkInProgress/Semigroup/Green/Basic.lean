import MyProject.Green.Defs
import Mathlib

/-! # Basic Properties of Green's Relations

This file proves basic properties about Green's relations and idempotent elements.

We also prove that Green's relations are preserved under morphisms.

## Main Theorems

Characterizations of elements that are 𝓡-below, 𝓛-below, or 𝓗-below an idempotent.
* `RPreorder.le_idempotent` - `x` is 𝓡-below an idempotent `e` if and only if `x = e * x`.
* `LPreorder.le_idempotent` - `x` is 𝓛-below an idempotent `e` if and only if `x = x * e`.
* `HPreorder.le_idempotent` - `x` is 𝓗-below an idempotent `e`
if and only if `x = e * x` and `x = x * e`.

We prove that Green's relations are preserved under morphisms `f`.
* `RPreorder.hom_pres` - If `x ≤𝓡 y`, then `f x ≤𝓡 f y`.
* `LPreorder.hom_pres` - If `x ≤𝓛 y`, then `f x ≤𝓛 f y`.
* `JPreorder.hom_pres` - If `x ≤𝓙 y`, then `f x ≤𝓙 f y`.
* `HPreorder.hom_pres` - If `x ≤𝓗 y`, then `f x ≤𝓗 f y`.
* `REquiv.hom_pres` - If `x 𝓡 y`, then `f x 𝓡 f y`.
* `LEquiv.hom_pres` - If `x 𝓛 y`, then `f x 𝓛 f y`.
* `JEquiv.hom_pres` - If `x 𝓙 y`, then `f x 𝓙 f y`.
* `HEquiv.hom_pres` - If `x 𝓗 y`, then `f x 𝓗 f y`.
* `DEquiv.hom_pres` - If `x 𝓓 y`, then `f x 𝓓 f y`.
-/

namespace Semigroup

/-! ### Idempotent properties (Prop 1.4.1) -/

/-- An element `x` is 𝓡-below an idempotent `e` if and only if `x = e * x`. -/
theorem RPreorder.le_idempotent (x e : S) (h: IsIdempotentElem e) :
    (x ≤𝓡 e) ↔ (x = e * x) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [← WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [hru, ← mul_assoc, h ]
  · intro hl; use x
    rw[<-WithOne.coe_inj] at hl; exact hl

/-- An element `x` is 𝓛-below an idempotent `e` if and only if `x = x * e`. -/
theorem LPreorder.le_idempotent (x e : S) (h: IsIdempotentElem e) :
    (x ≤𝓛 e) ↔ (x = x * e) := by
  constructor
  · rintro ⟨u, hru⟩
    unfold IsIdempotentElem at h
    rw [← WithOne.coe_inj, WithOne.coe_mul] at h ⊢
    rw [hru, mul_assoc, h ]
  · intro hl; use x
    rw[<-WithOne.coe_inj] at hl; exact hl

theorem HPreorder.le_idempotent (x e : S) (h : IsIdempotentElem e) :
    (x ≤𝓗 e) ↔ (x = e * x ∧ x = x * e) := by
  simp [HPreorder, RPreorder.le_idempotent x e h, LPreorder.le_idempotent x e h]

theorem HPreorder.le_idempotent' (x e : S) (he : IsIdempotentElem e) :
    x ≤𝓗 e ↔ e * x * e = x := by
  rw [HPreorder.le_idempotent x e he]
  constructor
  · rintro ⟨h₁, h₂⟩; rw [← h₁, ← h₂]
  · intro h; constructor
    · nth_rw 2 [← h]
      simp_rw [← mul_assoc]; rw [he, h]
    · nth_rw 2 [← h]
      rw [mul_assoc, he, h]

/-!
### Morphisms

We Prove that All of Green's preorders and Equivalences are Preserved under Morphisms.
Note that these should quantify over `MulHomClass`
-/

#check MulHomClass

variable {S T : Type*} [Semigroup S] [Semigroup T]
variable (F : Type*) [FunLike F S T] [MulHomClass F S T]

theorem RPreorder.hom_pres (f : F) (x y : S) (h : x ≤𝓡 y) : f x ≤𝓡 f y := by
  obtain ⟨z, hz⟩ := h
  cases z with
  | one => simp_all
  | coe z =>
    use f z
    sorry


end Semigroup

#min_imports
