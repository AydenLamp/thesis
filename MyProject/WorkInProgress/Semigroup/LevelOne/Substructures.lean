import Mathlib.Algebra.Group.Defs
import Mathlib.Data.SetLike.Basic

/-!
# Substructures of Semigroups
In this file, we extend Mathlib's `Subsemigroup` structure to define structures
for `Submonoid` and `Subgroup`. Note that these are different that the mathlib notions
of `Submonoid` and `Subgroup` which requrire the outer structure to also be a monoid/group,
so we put all definitions in the `Semigroup` namespace to avoid conflict

## Main Definitions
* `Semigroup.Subsemigroup`
* `Semigroup.Subsemigroup.toSemigroup` The `semigroup` instance on the subtype of a subsemigroup
* `Semigroup.Submonoid`
* `Semigroup.Submonoid.toMonoid` The `Monoid` instance on the subtype of a submonoid
* `Semigroup.Subgroup`
* `Semigroup.Subgroup.toGroup` The `Group` instance on the subtype of a submonoid

## Main Theorems

TODO

## Refrences
See https://avigad.github.io/mathematics_in_lean/C08_Hierarchies.html#sub-objects

## TODO
Redefine group with only left inverse requirement not both.

## Blueprint

TODO
-/

/-!
#### Structure definitions
The definition of `Semigroup.Subsemigroup` is copied from mathlibs `Subsemigroup`,
except we requrie an outer `Semigroup` structure.
These BUNDLED structures come with `SetLike` instances, enabiling a coersion to `Set`
so you can write things like `x ∈ H` for `x : S` and `H : Subsemigroup S`. It also provides
the lattice strucure (`⊓ ⊔ ⊤ ⊥`) and the cannonical subtype `H : Type := {x // x ∈ carrier}`
-/

namespace Semigroup

/-- A subsemigroup of a Semigroup `S` is a subset closed under multiplication. -/
structure Subsemigroup (S : Type*) [Semigroup S] where
  /-- The carrier of a subsemigroup. -/
  carrier : Set S
  /-- The product of two elements of a subsemigroup belongs to the subsemigroup. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier

namespace Subsemigroup

variable {S : Type*} [Semigroup S]

/-- We prove that `Subsemigroup S` has an injective coersion to `Set S` -/
instance : SetLike (Subsemigroup S) S :=
  ⟨Subsemigroup.carrier, fun p q h => by cases p; cases q; congr⟩

/-- We define `*` on the subsemigroup as a subtype -/
instance (T : Subsemigroup S) : Mul (T) :=
  ⟨fun a b => ⟨a.1 * b.1, T.mul_mem a.2 b.2⟩⟩

/-! We relate our defintion of `*` in the subtype to that outside of the subtype -/
variable {T : Subsemigroup S}

@[simp] theorem coe_mul (x y : T) : (↑(x * y) : S) = ↑x * ↑y := rfl

@[simp] theorem mk_mul_mk (x y : S) (hx : x ∈ T) (hy : y ∈ T) :
    (⟨x, hx⟩ : T) * ⟨y, hy⟩ = ⟨x * y, T.mul_mem hx hy⟩ := rfl

@[simp] theorem mul_def (x y : T) :
    x * y = ⟨x * y, T.mul_mem x.2 y.2⟩ := rfl

/-- A subsemigroup is a semigroup on its subtype -/
instance toSemigroup : Semigroup T where
  mul_assoc (x y z : T) := by simp_all [mul_assoc]

end Subsemigroup

/-- A submonoid of a Semigroup `S` is a subset closed under multiplication and containing
and identity element -/
structure Submonoid (S : Type*) [Semigroup S] extends Subsemigroup S where
  /-- The one element -/
  one : S
  /-- The one element is in the carrier -/
  one_mem : one ∈ carrier
  /-- The one element is a left identity in the carrier -/
  one_mul (x : S) : x ∈ carrier → one * x = x
  /-- The one element is a right identity in the carrier -/
  mul_one (x : S) : x ∈ carrier → x * one = x

namespace Submonoid

variable {S : Type*} [Semigroup S]

/-- In Order to obtain the `SetLike` instance, we need to construct an injection
from `Submonoid`s to `Set`s. This means that we must prove that, if the carrier
of two Submonoids is equal, then the one elements must be equal. -/
lemma one_eq {T₁ T₂ : Submonoid S} (heq : T₁.carrier = T₂.carrier) : T₁.one = T₂.one := by
  have h₁ : T₁.one ∈ T₂.carrier := by rw [← heq]; exact T₁.one_mem
  have h₂ : T₂.one ∈ T₁.carrier := by rw [heq]; exact T₂.one_mem
  have h₃ := T₁.one_mul T₂.one h₂
  rw [← h₃]
  have h₄ := T₂.mul_one T₁.one h₁
  exact h₄.symm

/-- We prove that `Submonoid S` has an injective coersion to `Set S` -/
instance : SetLike (Submonoid S) S :=
  ⟨Subsemigroup.carrier ∘ Submonoid.toSubsemigroup, fun T₁ T₂ h => by
    have heq : T₁.carrier = T₂.carrier := by simp_all
    have hone : T₁.one = T₂.one := one_eq heq
    cases T₁
    rename Subsemigroup S => T₁'
    cases T₁'
    cases T₂
    rename Subsemigroup S => T₂'
    congr⟩

/-- We define `*` on the submonoid as a subtype -/
instance (T : Submonoid S) : Mul (T) :=
  ⟨fun a b => ⟨a.1 * b.1, T.mul_mem a.2 b.2⟩⟩

/-! We relate our defintion of `*` in the subtype to that outside of the subtype -/
variable {T : Submonoid S}

@[simp] theorem coe_mul (x y : T) : (↑(x * y) : S) = ↑x * ↑y := rfl

@[simp] theorem mk_mul_mk (x y : S) (hx : x ∈ T) (hy : y ∈ T) :
    (⟨x, hx⟩ : T) * ⟨y, hy⟩ = ⟨x * y, T.mul_mem hx hy⟩ := rfl

@[simp] theorem mul_def (x y : T) :
    x * y = ⟨x * y, T.mul_mem x.2 y.2⟩ := rfl

instance : Semigroup T where
  mul_assoc := by simp [mul_assoc]

instance : One T where
  one := ⟨T.one, T.one_mem⟩

/-! We relate our identiy properties to the subtype -/

theorem one_def : (1 : T) = ⟨T.one, T.one_mem⟩ := rfl

@[simp] theorem coe_one : ↑(1 : T) = T.one := rfl

@[simp] theorem coe_mul_one (x : T) : x * 1 = x := by
  simp
  apply Subtype.eq
  simp
  have h := T.mul_one x.1 x.2
  rw [h]

@[simp] theorem coe_one_mul (x : T) : 1 * x = x:= by
  simp
  apply Subtype.eq
  simp
  have h := T.one_mul x.1 x.2
  rw [h]

/-- A Submonoid is a Monoid on its subtype -/
instance toMonoid : Monoid T where
  mul_assoc (x y z : T) := by simp_all [mul_assoc]
  one := ⟨T.one, T.one_mem⟩
  one_mul := coe_one_mul
  mul_one := coe_mul_one

end Submonoid

/-- A Subgroup of a Semigroup `S` is a subset closed under multiplication and containing
and identity element and an inverse function -/
structure Subgroup (S : Type*) [Semigroup S] extends Submonoid S where
  /-- The inverse function -/
  inv (x : S) : S
  /-- The inverse function is the identity if `x ∉ carrier`. This is to ensure
  injectivity with `Set` -/
  inv_not_mem {x : S} (hin : x ∉ carrier) : inv x = x
  /-- The inverses are in the carrier -/
  inv_mem {x : S} (hin : x ∈ carrier) : inv x ∈ carrier
  /-- The inverse function provides right inverses -/
  inv_mul {x : S} (hin : x ∈ carrier) : inv x * x = one
  /-- The inverse function provides left inverses -/
  mul_inv {x : S} (hin : x ∈ carrier) : x * inv x = one

namespace Subgroup

variable {S : Type*} [Semigroup S]

/-- In Order to obtain the `SetLike` instance, we need to construct an injection
from `Subgroup`s to `Set`s. This means that we must prove that, if the carrier
of two Submonoids is equal, then the one elements and the inverse functions must be equal. -/
lemma one_eq {T₁ T₂ : Subgroup S} (heq : T₁.carrier = T₂.carrier) : T₁.one = T₂.one := by
  have h₁ : T₁.one ∈ T₂.carrier := by rw [← heq]; exact T₁.one_mem
  have h₂ : T₂.one ∈ T₁.carrier := by rw [heq]; exact T₂.one_mem
  have h₃ := T₁.one_mul T₂.one h₂
  rw [← h₃]
  have h₄ := T₂.mul_one T₁.one h₁
  exact h₄.symm

lemma inv_unique' {T : Subgroup S} {x y: S} (hx: x ∈ T.carrier) (hy : y ∈ T.carrier) (heq : T.one = x * y) :
    T.inv y = x := by
  have h₁ := T.inv_mul hy
  rw [heq] at h₁
  have h₂ : T.inv y * y * T.inv y = x * (y * T.inv y) := by
    rw [h₁]
    simp [mul_assoc]
  have h₃ := T.inv_mul hy
  have h₄ := T.mul_inv hy
  rw [h₃] at h₂
  rw [h₄] at h₂
  rw [T.one_mul, T.mul_one] at h₂
  exact h₂
  · exact hx
  · apply T.inv_mem hy

lemma inv_unique {T : Subgroup S} {x y: S} (hx: x ∈ T.carrier) (hy : y ∈ T.carrier) (heq : T.one = x * y) :
    T.inv x = y := by
  have h := inv_unique' hx hy heq
  apply inv_unique'
  · exact hy
  · exact hx
  · rw [← h]
    symm
    apply T.mul_inv hy

lemma inv_eq {T₁ T₂ : Subgroup S} (heq : T₁.carrier = T₂.carrier) : T₁.inv = T₂.inv := by
  ext x
  by_cases hx : x ∈ T₁.carrier
  · have hx₂ : x ∈ T₂.carrier := by rwa [heq] at hx
    have h₁ : T₁.inv x * x = T₁.one := T₁.inv_mul hx
    have h₂ : T₂.inv x * x = T₂.one := T₂.inv_mul hx₂
    have hone : T₁.one = T₂.one := one_eq heq
    rw [hone] at h₁
    have h₁ := h₁.symm
    have h₃ : T₁.inv x ∈ T₂.carrier := by
      rw [← heq]
      apply T₁.inv_mem hx
    have h₄ := inv_unique' h₃ hx₂ h₁
    exact h₄.symm
  · have hx₂ : x ∉ T₂.carrier := by rwa [← heq]
    have h₁ := T₁.inv_not_mem hx
    have h₂ := T₂.inv_not_mem hx₂
    rw [h₁, h₂]

/-- We prove that `Subgroup S` has an injective coersion to `Set S` -/
instance : SetLike (Subgroup S) S :=
  ⟨Subsemigroup.carrier ∘ Submonoid.toSubsemigroup ∘ Subgroup.toSubmonoid , fun T₁ T₂ h => by
    have heq : T₁.carrier = T₂.carrier := by simp_all
    have hone : T₁.one = T₂.one := one_eq heq
    have hinv : T₁.inv = T₂.inv := inv_eq heq
    cases T₁
    rename Submonoid S => T₁'
    cases T₁'
    rename Subsemigroup S => T₁''
    cases T₁''
    cases T₂
    rename Submonoid S => T₂'
    cases T₂'
    rename Subsemigroup S => T₂''
    cases T₂''
    congr⟩

/-- We define `*` on the submonoid as a subtype -/
instance (T : Subgroup S) : Mul (T) :=
  ⟨fun a b => ⟨a.1 * b.1, T.mul_mem a.2 b.2⟩⟩

/-! We relate our defintion of `*` in the subtype to that outside of the subtype -/
variable {T : Subgroup S}

@[simp] theorem coe_mul (x y : T) : (↑(x * y) : S) = ↑x * ↑y := rfl

@[simp] theorem mk_mul_mk (x y : S) (hx : x ∈ T) (hy : y ∈ T) :
    (⟨x, hx⟩ : T) * ⟨y, hy⟩ = ⟨x * y, T.mul_mem hx hy⟩ := rfl

@[simp] theorem mul_def (x y : T) :
    x * y = ⟨x * y, T.mul_mem x.2 y.2⟩ := rfl

instance : Semigroup T where
  mul_assoc := by simp [mul_assoc]

instance : One T where
  one := ⟨T.one, T.one_mem⟩

/-! We relate our identiy properties to the subtype -/

theorem one_def : (1 : T) = ⟨T.one, T.one_mem⟩ := rfl

@[simp] theorem coe_one : ↑(1 : T) = T.one := rfl

@[simp] theorem coe_mul_one (x : T) : x * 1 = x := by
  simp
  apply Subtype.eq
  simp
  have h := T.mul_one x.1 x.2
  rw [h]

@[simp] theorem coe_one_mul (x : T) : 1 * x = x:= by
  simp
  apply Subtype.eq
  simp
  have h := T.one_mul x.1 x.2
  rw [h]

instance : Monoid T where
  one_mul := coe_one_mul
  mul_one := coe_mul_one

instance : Inv T where
  inv (x : T) := ⟨T.inv x, T.inv_mem x.2⟩

@[simp] lemma inv_def (x : T) : x⁻¹ = ⟨T.inv x.1, T.inv_mem x.2⟩ := by rfl

instance : Group T where
  inv_mul_cancel (x : T) := by
    simp [one_def]
    apply T.inv_mul
    simp


end Subgroup

end Semigroup
