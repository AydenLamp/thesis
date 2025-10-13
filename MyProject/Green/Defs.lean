import Mathlib.Algebra.Group.WithOne.Defs

/-!
# Green's Relations Definitions

This file defines Green's preorders and equivalence relations on semigroups.

We prove basic theorems, like `Semigroup.REquiv_lEquiv_comm`, which are neccessary
for instantiating `DEquiv` as an equivalence relation with `Semigroup.DEquiv.isEquivalence`.

We also prove simp lemmas at the end of the file.

## Main definitions

In the following definitions, `S` is a semigroup and `x y : S`.

**Greens Preorder Relations**

* `Semigroup.RPreorder` - `x` is 𝓡-below `y` (notated `x ≤𝓡 y`) iff there exists a
`z : WithOne S` such that `↑x = ↑y * z`

* `Semigroup.LPreorder` - `x` is 𝓛-below `y` (notated `x ≤𝓛 y`) iff there exists a
`z : WithOne S` such that `↑x = z * ↑y`

* `Semigroup.JPreorder` - `x` is 𝓙-below `y` (notated `x ≤𝓙 y`) iff there exists
`z w : WithOne S` such that `↑x = z * ↑y * w`

* `Semigroup.HPreorder` - `x` is 𝓗-below `y` (notated `x ≤𝓗 y`) iff `x ≤𝓛 y` and `x ≤𝓡 y`

We instantiate each preorder in the unbundled `IsPreorder` Class:
* `Semigroup.RPreorder.isPreorder` - instance for `[IsPreorder S RPreorder]`
* `Semigroup.LPreorder.isPreorder` - instance for `[IsPreorder S LPreorder]`
* `Semigroup.JPreorder.isPreorder` - instance for `[IsPreorder S JPreorder]`
* `Semigroup.HPreorder.isPreorder` - instance for `[IsPreorder S HPreorder]`

**Greens Equivalence Relations**

We define the `𝓡, 𝓛, 𝓙, 𝓗` relations as the
symmetric closure of their corresponding preorders:
* `Semigroup.REquiv` - `x 𝓡 y` iff `x ≤𝓡 y` and `y ≤𝓡 x`
* `Semigroup.LEquiv` - `x 𝓛 y` iff `x ≤𝓛 y` and `y ≤𝓛 x`
* `Semigroup.JEquiv` - `x 𝓙 y` iff `x ≤𝓙 y` and `y ≤𝓙 x`
* `Semigroup.HEquiv` - `x 𝓗 y` iff `x ≤𝓗 y` and `y ≤𝓗 x`

The `𝓓` relation is defined as the composition of `𝓡` and `𝓛`:
* `Semigroup.DEquiv` - `x 𝓓 y` iff `∃ z, x 𝓡 z ∧ z 𝓛 y`

Equivalence classes of Elements as Sets:
* `Semigroup.REquiv.set` - Noated `⟦x⟧𝓡`, the `Set S` of elements 𝓡-related to `x`
* `Semigroup.LEquiv.set` - Noated `⟦x⟧𝓛`, the `Set S` of elements 𝓛-related to `x`
* `Semigroup.JEquiv.set` - Noated `⟦x⟧𝓙`, the `Set S` of elements 𝓙-related to `x`
* `Semigroup.HEquiv.set` - Noated `⟦x⟧𝓗`, the `Set S` of elements 𝓗-related to `x`
* `Semigroup.DEquiv.set` - Noated `⟦x⟧𝓓`, the `Set S` of elements 𝓓-related to `x`

## Main Theorems

* `IsPreorder.SymmClosure` - Given a preorder `α : S → S → Prop` and an instance
`[IsPreorder S α]`, the symmectric closure of `α` is an equivalence relation.

We use the preceding theorem to prove that `𝓡, 𝓛, 𝓙, 𝓗` are equivalence relations.
* `Semigroup.REquiv.isEquivalence`
* `Semigroup.LEquiv.isEquivalence`
* `Semigroup.JEquiv.isEquivalence`
* `Semigroup.HEquiv.isEquivalence`

We prove that `≤𝓡` and `𝓡` are compatable with left multiplication.
That is, if `x (≤)𝓡 y`, then `z * x (≤)𝓡 z * y`.
We also prove that `≤𝓛` and `𝓛`  are compatable with right multiplication:
* `Semigroup.RPreorder.lmul_compat`
* `Semigroup.REquiv.lmul_compat`
* `Semigroup.LPreorder.rmul_compat`
* `Semigroup.LEquiv.rmul_compat`

* `Semigroup.rEquiv_lEquiv_comm` - We prove that `𝓡` and `𝓛` commute under composition, i.e.
`(∃ z, x 𝓡 z ∧ z 𝓛 y) ↔ (∃ z, x 𝓛 z ∧ z 𝓡 y)`. This allows to prove that `𝓓` is symmetric.

We prove that `𝓓` is closed under composition with `𝓛` and `𝓡`.
This allows us to prove that `𝓓` is transitive:
* `Semigroup.DEquiv.closed_under_lEquiv` - If `x 𝓓 y` and `y 𝓛 z`, then `x 𝓓 z`.
* `Semigroup.DEquiv.closed_under_rEquiv` - If `x 𝓓 y` and `y 𝓡 z`, then `x 𝓓 z`.

* `Semigroup.DEquiv.isEquivalence` - The `𝓓` relation is reflexive, symmetric, and transitive.

## Implementation Notes

Becuase we defined `𝓗` as the symmectric closure of `≤𝓗`, using `simp [HEquiv]` will
change `x 𝓗 y` to `x ≤𝓗 y ∧ y ≤𝓗 x`. If you want to rewrite to `x 𝓡 y ∧ x 𝓛 y`, use
`HEquiv.iff_rEquiv_and_lEquiv`.

## Refrences

TODO
-/

/-! ### Green's Preorders -/

namespace Semigroup

variable {S} [Semigroup S]

/-- `x` is 𝓡-below `y` if `x = y` or there exists a `z : S` such that `x = y * z` -/
def RPreorder (x y : S) : Prop := ∃ z : WithOne S , ↑x = ↑y * z

infix:50 " ≤𝓡 " => RPreorder

namespace RPreorder

@[simp] lemma refl (x : S) : x ≤𝓡 x := by use 1; simp

@[trans] lemma trans {x y z : S} (hxy : x ≤𝓡 y) (hyz : y ≤𝓡 z) : x ≤𝓡 z := by
  rcases hxy with ⟨w, hw⟩
  rcases hyz with ⟨v, hv⟩
  use (v * w)
  rw [← mul_assoc, ← hv, ← hw]

/-- `≤𝓡` is a Preorder -/
instance isPreorder : IsPreorder S RPreorder where
  refl := refl
  trans := by apply trans

end RPreorder

/-- `x` is 𝓛-below `y` if `x = y` or there exists a `z : S` such that `x = z * y` -/
def LPreorder (x y: S) : Prop := ∃ z : WithOne S, ↑x = z * ↑y

infix:50 " ≤𝓛 " => LPreorder

namespace LPreorder

@[simp] lemma refl (x : S) : x ≤𝓛 x := by use 1; simp

@[trans] lemma trans {x y z : S} (hxy : x ≤𝓛 y) (hyz : y ≤𝓛 z) : x ≤𝓛 z := by
  rcases hxy with ⟨u, hu⟩
  rcases hyz with ⟨v, hv⟩
  use u * v
  rw [hu, hv, mul_assoc]

/-- `≤𝓛` is a Preorder -/
instance isPreorder : IsPreorder S LPreorder where
  refl := refl
  trans := by apply trans

end LPreorder

/-- `x` is 𝓙-below `y` if there exists `w v : WithOne S` such that `↑x = w * ↑y * v` -/
def JPreorder (x y : S) : Prop := ∃ w v : WithOne S, ↑x = w * ↑y * v

infix:50 " ≤𝓙 " => JPreorder

namespace JPreorder

@[simp] lemma refl (x : S) : x ≤𝓙 x := by use 1, 1; simp

@[trans] lemma trans {x y z : S} (hxy : x ≤𝓙 y) (hyz : y ≤𝓙 z) : x ≤𝓙 z := by
  rcases hxy with ⟨u₁, v₁, hu⟩
  rcases hyz with ⟨u₂, v₂, hv⟩
  use u₁ * u₂, v₂ * v₁
  rw [hu, hv]
  simp [mul_assoc]

/-- `≤𝓙` is a Preorder -/
instance isPreorder : IsPreorder S JPreorder where
  refl := refl
  trans := by apply trans

end JPreorder

/-- `x` is 𝓗-below `y` if `x ≤𝓡 y` and `x ≤𝓛 y` -/
def HPreorder (a b : S) : Prop := a ≤𝓡 b ∧ a ≤𝓛 b

notation:50 f " ≤𝓗 " g:50 => HPreorder f g

namespace HPreorder

@[simp] lemma refl (x : S) : x ≤𝓗 x := by simp [HPreorder]

@[trans] lemma trans {x y z : S} (hxy : x ≤𝓗 y) (hyz : y ≤𝓗 z) : x ≤𝓗 z := by
  rcases hxy with ⟨h1, h2⟩
  rcases hyz with ⟨h3, h4⟩
  constructor
  · apply RPreorder.trans h1 h3
  · apply LPreorder.trans h2 h4

/-- `≤𝓗` is a Preorder -/
instance isPreorder : IsPreorder S HPreorder where
  refl := refl
  trans := by apply trans

end HPreorder

/-! ### Green's Equivalences (except 𝓓) -/

/-- Symmectric Csure of a preorder is an Equivalence -/
-- The `_root_` prefix escapes the current `Semigroup` namespace
def _root_.IsPreorder.SymmClosure {α : Type*} (p : α → α → Prop) [h : IsPreorder α p] :
    Equivalence (λ a b  => p a b ∧ p b a) where
  refl := by simp [h.refl]
  symm := by aesop
  trans {x y z : α} (h₁ : p x y ∧ p y x) (h₂ : p y z ∧ p z y) : p x z ∧ p z x := by
    obtain ⟨hxy, hyx⟩ := h₁
    obtain ⟨hyz, hzy⟩ := h₂
    exact ⟨h.trans x y z hxy hyz, h.trans z y x hzy hyx⟩

/-- Green's `𝓡` Equivalence -/
def REquiv (x y : S) : Prop := x ≤𝓡 y ∧ y ≤𝓡 x

notation :50 a " 𝓡 " b:50 => REquiv a b

namespace REquiv

/-- `𝓡` is an Equivalence -/
theorem isEquivalence : Equivalence (fun x y : S ↦ x 𝓡 y) := by
  have H := IsPreorder.SymmClosure (fun x y : S ↦ x ≤𝓡 y)
  simp_all [REquiv]

@[simp] lemma refl (x : S) : x 𝓡 x :=
  REquiv.isEquivalence.refl x

@[simp, symm] lemma symm {x y : S} (h : x 𝓡 y) : y 𝓡 x :=
  REquiv.isEquivalence.symm h

@[trans] lemma trans {x y z : S} (h₁ : x 𝓡 y) (h₂ : y 𝓡 z) : x 𝓡 z :=
  REquiv.isEquivalence.trans h₁ h₂

/-- The set of all elements 𝓡-related to `x` -/
def set (x : S) : Set (S) := {a | a 𝓡 x}

notation "⟦" x "⟧𝓡" => set x

end REquiv

/-- Green's `𝓛` equivalence relation -/
def LEquiv (x y : S) : Prop := x ≤𝓛 y ∧ y ≤𝓛 x

notation :50 a " 𝓛 " b:50 => LEquiv a b

namespace LEquiv

/-- `𝓛` is an Equivalence -/
theorem isEquivalence : Equivalence (fun x y : S ↦ x 𝓛 y) := by
  have H := IsPreorder.SymmClosure (fun x y : S ↦ x ≤𝓛 y)
  simp_all [LEquiv]

@[simp] lemma refl (x : S) : x 𝓛 x :=
  isEquivalence.refl x

@[simp, symm] lemma symm {x y : S} (h : x 𝓛 y) : y 𝓛 x :=
  isEquivalence.symm h

@[trans] lemma trans {x y z : S} (h₁ : x 𝓛 y) (h₂ : y 𝓛 z) : x 𝓛 z :=
  isEquivalence.trans h₁ h₂

/-- The set of all elements 𝓛-related to `x` -/
def set (x : S) : Set (S) := {a | a 𝓛 x}

notation "⟦" x "⟧𝓛" => set x

end LEquiv

/-- Green's `𝓙` equivalence relation -/
def JEquiv (x y : S) : Prop := x ≤𝓙 y ∧ y ≤𝓙 x

notation :50 a " 𝓙 " b:50 => JEquiv a b

namespace JEquiv

/-- `𝓙` is an Equivalence -/
theorem isEquivalence : Equivalence (fun x y : S ↦ x 𝓙 y) := by
  have H := IsPreorder.SymmClosure (fun x y : S ↦ x ≤𝓙 y)
  simp_all [JEquiv]

@[simp] lemma refl (x : S) : x 𝓙 x :=
  isEquivalence.refl x

@[simp, symm] lemma symm {x y : S} (h : x 𝓙 y) : y 𝓙 x :=
  isEquivalence.symm h

@[trans] lemma trans {x y z : S} (h₁ : x 𝓙 y) (h₂ : y 𝓙 z) : x 𝓙 z :=
  isEquivalence.trans h₁ h₂

/-- The set of all elements 𝓙-related to `x` -/
def set (x : S) : Set (S) := {a | a 𝓙 x}

notation "⟦" x "⟧𝓙" => set x

end JEquiv

/-- Green's `𝓗` Equivalence relation -/
def HEquiv (x y : S) : Prop := x ≤𝓗 y ∧ y ≤𝓗 x

notation :50 a " 𝓗 " b:50 => HEquiv a b

namespace HEquiv

theorem isEquivalence : Equivalence (fun x y : S ↦ x 𝓗 y) := by
  have H := IsPreorder.SymmClosure (fun x y : S ↦ x ≤𝓗 y)
  simp_all [HEquiv]

@[simp] lemma refl (x : S) : x 𝓗 x :=
  isEquivalence.refl x

@[simp, symm] lemma symm {x y : S} (h : x 𝓗 y) : y 𝓗 x :=
  isEquivalence.symm h

@[trans] lemma trans {x y z : S} (h₁ : x 𝓗 y) (h₂ : y 𝓗 z) : x 𝓗 z :=
  isEquivalence.trans h₁ h₂

/-- The set of all elements 𝓗-related to `x` -/
def set (x : S) : Set (S) := {a | a 𝓗 x}

notation "⟦" x "⟧𝓗" => set x

/-- The 𝓗 equivalence relation is the intersection of 𝓡 and 𝓛 equivalences. -/
theorem iff_rEquiv_and_lEquiv (x y : S) : x 𝓗 y ↔ x 𝓡 y ∧ x 𝓛 y := by
  simp_all [HEquiv, HPreorder, LEquiv, REquiv]
  tauto

end HEquiv

/-! ### 𝓡 𝓛 Theorems-/

/-- `≤𝓡` is compatable with left multiplication -/
@[simp] lemma RPreorder.lmult_compat (x y z : S) (h : x ≤𝓡 y) : z * x ≤𝓡 z * y := by
  obtain ⟨u, hu⟩ := h; use u
  simp [mul_assoc, hu]

/-- `𝓡` is compatable with left multiplication -/
@[simp] lemma REquiv.lmult_compat (x y z : S) (h : x 𝓡 y) : z * x 𝓡 z * y := by
  simp_all [REquiv]

/-- `≤𝓛` is compatable with right multiplication -/
@[simp] lemma LPreorder.rmult_compat (x y z : S) (h : x ≤𝓛 y) : x * z ≤𝓛 y * z := by
  rcases h with ⟨u, hu⟩
  use u
  simp [← mul_assoc, hu]

/-- `𝓛` is compatable with right multiplication -/
@[simp] lemma LEquiv.rmult_compat (x y z : S) (h : x 𝓛 y) : x * z 𝓛 y * z := by
  simp_all [LEquiv]

/-- `𝓡` and `𝓛` commute under composition -/
theorem rEquiv_lEquiv_comm (x y : S) : (∃ z, x 𝓡 z ∧ z 𝓛 y) ↔ (∃ z, x 𝓛 z ∧ z 𝓡 y) := by
  constructor
  · rintro ⟨z, ⟨hr, hl⟩⟩
    have hr₁ := hr
    have hl₁ := hl
    rcases hr₁ with ⟨⟨w₁, hw₁⟩, ⟨v₁, hv₁⟩⟩
    rcases hl₁ with ⟨⟨w₂, hw₂⟩, ⟨v₂, hv₂⟩⟩
    -- We have `x = w₂ * y * w₁` and `y = v₂ * z * v₁`
    -- We want to use `v₂ * z * w₁`, but we need to destruct on `v₂, w₁ : WithOne S`
    cases hv₂one : v₂ with
    | one =>
      subst v₂ -- trival case where `v₂ = 1`
      simp at hv₂
      subst z -- `z = y`
      use x
      simp [hr]
    | coe v₂ =>
      subst hv₂one
      cases hw₁one : w₁ with
      | one =>
        subst w₁ -- trival case where `w₁ = 1` and `z = x`
        simp at hw₁
        subst hw₁
        use y
        simp [hl]
      | coe w₁ => -- Non-trivial case, use `v₂ * z * w₁`
        subst hw₁one
        use v₂ * z * w₁
        constructor
          <;> constructor
        · use w₂ -- `x ≤𝓛 v₂ * z * w₁`
          simp [← mul_assoc]
          rw [mul_assoc w₂, ← hv₂, ← hw₂, hw₁]
        · use v₂ -- `v₂ * z * w₁ ≤𝓛 x`
          simp [mul_assoc]
          rw [← hw₁]
        · use w₁ -- `v₂ * z * w₁ ≤𝓡 y`
          simp [hv₂]
        · use v₁ -- `y ≤𝓡 v₂ * z * w₁`
          simp [mul_assoc v₂]
          rw [← hw₁, hv₂, hv₁]
          simp [mul_assoc]
  · rintro ⟨z, ⟨hl, hr⟩⟩
    have hr₁ := hr
    have hl₁ := hl
    rcases hr₁ with ⟨⟨w₁, hw₁⟩, ⟨v₁, hv₁⟩⟩
    rcases hl₁ with ⟨⟨w₂, hw₂⟩, ⟨v₂, hv₂⟩⟩
    -- We have `y = v₂ * x * v₁` and `x = w₂ * y * w₁`
    -- We want to use `w₂ * z * v₁`, but we need to destruct on `w₂, v₁ : WithOne S`
    cases hw₂one : w₂ with
    | one =>
      subst w₂ -- trival case where `w₂ = 1`
      simp at hw₂
      subst z -- `z = x`
      use y
      simp [hr]
    | coe w₂ =>
      subst hw₂one
      cases hv₁one : v₁ with
      | one =>
        subst v₁ -- trival case where `v₁ = 1` and `z = y`
        simp at hv₁
        subst hv₁
        use x
        simp [hl]
      | coe v₁ => -- Non-trivial case, use `w₂ * z * v₁`
        subst hv₁one
        use w₂ * z * v₁
        constructor
          <;> constructor
        · use w₁ -- `x ≤𝓡 w₂ * z * v₁`
          simp
          nth_rw 1 [hw₂, hw₁, hv₁]
          simp [← mul_assoc]
        · use v₁ -- `w₂ * z * v₁ ≤𝓡 x`
          simp [hw₂]
        · use w₂ -- `w₂ * z * v₁ ≤𝓛 y`
          simp [hv₁, ← mul_assoc]
        · use v₂ -- `y ≤𝓛 w₂ * z * v₁`
          simp [hv₁]
          nth_rw 1 [hv₂, hw₂]
          simp [← mul_assoc]

/-! ### Green's D relation -/

/-- Green's `𝓓` Equivalence, defined as the composition of `𝓡` and `𝓛` -/
def DEquiv : S → S → Prop := fun x y => ∃ z, x 𝓡 z ∧ z 𝓛 y

infix:50 " 𝓓 " => DEquiv

namespace DEquiv

@[simp] lemma refl (x : S) : x 𝓓 x := by
  use x
  constructor <;> simp

@[simp, symm] lemma symm {x y : S} (h : x 𝓓 y) : y 𝓓 x := by
  obtain ⟨z, ⟨hz1, hz2⟩⟩ := h
  simp [DEquiv]
  rw [rEquiv_lEquiv_comm]
  use z
  simp_all

/-- `𝓓` is closed under composition with `𝓛` -/
lemma closed_under_lEquiv {x y z : S} (hd : x 𝓓 y) (hl : y 𝓛 z) : x 𝓓 z := by
  rcases hd with ⟨w, ⟨hw1, hw2⟩⟩
  use w
  simp_all
  apply LEquiv.trans hw2 hl

/-- `𝓓` is closed under composition with `𝓡` -/
lemma closed_under_rEquiv {x y z : S} (hd : x 𝓓 y) (hl : y 𝓡 z) : x 𝓓 z := by
  simp [DEquiv] at hd
  rw [rEquiv_lEquiv_comm] at hd
  rcases hd with ⟨w, ⟨hw1, hw2⟩⟩
  symm
  use w
  simp_all
  apply REquiv.trans hl.symm hw2.symm

@[trans] lemma trans {x y z : S} (h1 : x 𝓓 y) (h2 : y 𝓓 z) : x 𝓓 z := by
  rcases h2 with ⟨w, ⟨hw1, hw2⟩⟩
  have hd1 : x 𝓓 w := by apply closed_under_rEquiv <;> assumption
  apply closed_under_lEquiv hd1 hw2

/-- `𝓓` is an Equivalence -/
theorem isEquivalence : Equivalence (fun x y : S => x 𝓓 y) where
  refl := refl
  symm := symm
  trans := trans

end DEquiv

/-! ### Simp Lemmas -/

variable {x y z : S}

/-- `x ≤𝓡 y` implies `x ≤𝓙 y` -/
@[simp] lemma RPreorder.implies_jEquiv (h : x ≤𝓡 y) : x ≤𝓙 y := by
  obtain ⟨u, hu⟩ := h
  use 1, u
  simp_all

/-- `x ≤𝓛 y` implies `x ≤𝓙 y` -/
@[simp] lemma LPreorder.implies_jEquiv (h : x ≤𝓛 y) : x ≤𝓙 y := by
  obtain ⟨u, hu⟩ := h
  use u, 1
  simp_all

/-- `x 𝓡 y` implies `x 𝓙 y` -/
@[simp] lemma REquiv.implies_jEquiv (h : x 𝓡 y) : x 𝓙 y := by
  simp_all [JEquiv, REquiv]

/-- `x 𝓛 y` implies `x 𝓙 y` -/
@[simp] lemma LEquiv.implies_jEquiv (h : x 𝓛 y) : x 𝓙 y := by
  simp_all [JEquiv, LEquiv]


/-- `x 𝓓 y` imples `x 𝓙 y` -/
@[simp] lemma DEquiv.implies_jEquiv (h : x 𝓓 y) : x 𝓙 y := by
  rcases h with ⟨z, ⟨hr, hl⟩⟩
  have hr₁ := hr
  have hl₁ := hl
  rcases hr₁ with ⟨⟨o, ho⟩, ⟨u, hu⟩⟩
  rcases hl₁ with ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
  constructor
  · use v, o
    rw [← hv, ho]
  · use w, u
    rw [hw, hu]
    simp [← mul_assoc]

/-- `x * y` is always 𝓡-below `x` -/
@[simp] lemma RPreorder.mul_right_self : x * y ≤𝓡 x := by
  use y; rw [WithOne.coe_mul]

/-- `x * y` is always 𝓛-below `y` -/
@[simp] lemma LPreorder.mul_left_self : x * y ≤𝓛 y := by
  use x; rw [WithOne.coe_mul]

/-- `x * y * z` is always 𝓙-below `y` -/
@[simp] lemma JPreorder.mul_sandwich_self : x * y * z ≤𝓙 y := by
  use x, z; simp

/-- `x ≤𝓡 x * y` implies `x 𝓡 x * y` -/
@[simp] lemma REquiv.of_preorder_mul_right (h : x ≤𝓡 x * y) : x 𝓡 x * y := by
  simp_all [REquiv]

/-- `x ≤𝓛 y * x` implies `x 𝓛 y * x` -/
@[simp] lemma LEquiv.of_preorder_mul_left (h : x ≤𝓛 y * x) : x 𝓛 y * x := by
  simp_all [LEquiv]

/-- `x ≤𝓙 y * x * z` implies `x 𝓙 y * x * z` -/
@[simp] lemma JEquiv.of_preorder_mul_sandwich (h : x ≤𝓙 y * x * z) :
    x 𝓙 y * x * z := by simp_all [JEquiv]

/-- If `x 𝓡 x * y * z`, then `x 𝓡 x * y`. -/
@[simp] lemma REquiv.right_cancel (h : x 𝓡 x * y * z) : x 𝓡 x * y := by
  simp_all [REquiv]
  obtain ⟨⟨u, hu⟩, _⟩ := h
  use z * u
  simp_rw [WithOne.coe_mul, ← mul_assoc] at *
  exact hu

/-- If `x 𝓡 x * y * z`, then `x * y 𝓡 x * y * z`.-/
@[simp] lemma REquiv.right_extend (h : x 𝓡 x * y * z) : x * y 𝓡 x * y * z := by
  simp_all [REquiv]
  obtain ⟨⟨u, hu⟩, _⟩ := h
  use u * y
  simp_rw [WithOne.coe_mul, ← mul_assoc] at *
  rw [← hu]

/-- If `x 𝓛 z * y * x`, then `x 𝓛 y * x`. -/
@[simp] lemma LEquiv.left_cancel (h: x 𝓛 z * y * x ) : x 𝓛 y * x := by
  simp_all [LEquiv]
  obtain ⟨u, hu⟩ := h
  use u * z
  simp_rw [WithOne.coe_mul, ← mul_assoc] at *
  exact hu

/-- If `x 𝓛 z * y * x`, then `y * x 𝓛 z * y * x`. -/
@[simp] lemma LEquiv.left_extend (h : x 𝓛 z * y * x) : y * x 𝓛 z * y * x := by
  simp_all [LEquiv]
  obtain ⟨u, hu⟩ := h
  use y * u
  simp_rw [WithOne.coe_mul, ← mul_assoc] at *
  nth_rw 1 [hu]
  simp [mul_assoc]
