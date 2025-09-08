import Mathlib

/-!
# Chapter 1: Special Elements
-/

/-!
## Local Identities in semigroups
TODO: Put these in a namespace
-/

section SemigroupIdenties

variable {S : Type*} [Semigroup S]

def IsLeftIdentity (e : S) : Prop := ∀ s : S, e * s = s

def IsRightIdentity (e : S) : Prop := ∀ s : S, s * e = s

def IsIdentity (e : S) : Prop := ∀ s : S, s * e = s

lemma idempotent_left_identity {e : S} (h : IsLeftIdentity e) : IsIdempotentElem e := by
  simp_all [IsIdempotentElem, IsLeftIdentity]

lemma idempotent_right_identity {e : S} (h : IsRightIdentity e) : IsIdempotentElem e := by
  simp_all [IsIdempotentElem, IsRightIdentity]

lemma idempotent_identity {e : S} (h : IsIdentity e) : IsIdempotentElem e := by
  simp_all [IsIdempotentElem, IsIdentity]

lemma idempotent_mul_eq {e x y : S} (he : IsIdempotentElem e)
    (hx : e * x * y = x) : e * x = x := by
  simp_all [IsIdempotentElem]
  rw [← hx]
  simp [← mul_assoc]
  rw [he]

lemma idempotent_eq_mul {f x e: S} (he : IsIdempotentElem e)
    (hx : f * x * e = x) : x * e = x := by
  simp_all [IsIdempotentElem]
  rw [← hx]
  simp [mul_assoc]
  rw [he]

end SemigroupIdenties

/-! ## Zero elements and null semigroups -/

section SemigroupZero

variable {S : Type*} [Semigroup S]
def IsLeftZero (x : S) : Prop :=
  ∀ y : S, x * y = x

def IsRightZero (x : S) : Prop :=
  ∀ y : S, y * x = x

def IsZero (x : S) : Prop :=
  IsLeftZero x ∧ IsRightZero x

lemma left_zero_idempotent {x : S} (h : IsLeftZero x) : IsIdempotentElem x := by
  simp_all [IsIdempotentElem, IsLeftZero]

lemma right_zero_idempotent {x : S} (h : IsRightZero x) : IsIdempotentElem x := by
  simp_all [IsIdempotentElem, IsRightZero]

lemma zero_idempotent {x : S} (h : IsZero x) : IsIdempotentElem x := by
  simp_all [IsIdempotentElem, IsZero, IsLeftZero]

/-- A Semigroup has at most one zero element -/
lemma zero_unique {x y : S} (hx : IsZero x) (hy : IsZero y) : x = y := by
  rcases hx with ⟨hx1, hx2⟩
  rcases hy with ⟨hy1, hy2⟩
  simp_all [IsLeftZero, IsRightZero]
  have h₁ : x * y = x := hx1 y
  have h2 : x * y = y := hy2 x
  simp_all

/- Definition of a Semigroup With a Zero element -/
#check SemigroupWithZero
#check zero_mul
#check mul_zero

/- Definition of a Null Semigroup -/
class NullSemigroup (S : Type*) extends SemigroupWithZero S where
  mul_eq_zero : ∀ x y : S, x * y = 0

end SemigroupZero

/- ## Cancellativity -/


#check IsLeftRegular
#check IsRightRegular
#check IsRegular

#check LeftCancelSemigroup
#check RightCancelSemigroup

/- ## Inverses
TODO: Prove that an element can have several semigroup inverses,
and an infinite monoid can have several right/left group inverses, but
a finite monoid can only have one unique left and right inverse per element.
-/

section SemigroupInverses

variable {S : Type*} [Semigroup S]

def IsSemigroupInverse (x y : S) : Prop := x * y * x = x ∧ y * x * y = y

variable {M : Type*} [Monoid M]

/-- Note that this does not require a group structure, just a monoid -/
def IsLeftGroupInverse (x y : M) : Prop := x * y = 1
def IsRightGroupInverse (x y : M) : Prop := y * x = 1
def IsGroupInverse (x y : M) : Prop := IsLeftGroupInverse x y ∧ IsRightGroupInverse x y

/-- Group inverses are always semigroup inverses -/
lemma semigroup_inverse_of_group_inverse {x y : M} (h : IsGroupInverse x y) :
    IsSemigroupInverse x y := by
  simp_all [IsSemigroupInverse, IsGroupInverse, IsLeftGroupInverse, IsRightGroupInverse]

end SemigroupInverses


/-! # Chapter 2 : Ordered Semigroups and Monoids
In mathlib, these are defined but on Communative Semigroups (why?)
-/

class OrderedSemigroup (S : Type*) extends (Semigroup S), (PartialOrder S) where
  mul_le_mul_left : ∀ a b : S, a ≤ b → ∀ c, c * a ≤ c * b
  mul_le_mul_right : ∀ a b : S, a ≤ b → ∀ c, a * c ≤ b * c

class OrderedMonoid (M : Type*) extends Monoid M, PartialOrder M where
  mul_le_mul_left : ∀ a b : M, a ≤ b → ∀ c, c * a ≤ c * b
  mul_le_mul_right : ∀ a b : M, a ≤ b → ∀ c, a * c ≤ b * c

variable {M : Type*}

instance OrderedMonoid.toOrderedSemigroup [inst : OrderedMonoid M] : OrderedSemigroup M where
  mul_le_mul_left := inst.mul_le_mul_left
  mul_le_mul_right := inst.mul_le_mul_right

lemma mul_le_mul_sandwich [inst : OrderedMonoid M] :
    ∀ a b : M, a ≤ b → ∀ c d, c * a * d ≤ c * b * d := by
  intros a b hab c d
  have h : c * a ≤ c * b := inst.mul_le_mul_left a b hab c
  apply inst.mul_le_mul_right (c * a) (c * b)
  exact h


#check Setoid
#check IsPreorder
#check Equivalence
#check Preorder
#check PartialOrder

#check IsOrderedMonoid -- Mathlib, communitive def



/-!
# Chapter 3: Morphisms

When possible, instead of parametrizing results over (f : M →* N),
you should parametrize over (F : Type*) [MonoidHomClass F M N] (f : F).
When you extend this structure, make sure to extend MonoidHomClass
-/

/- Def: Semigroup Morphism -/
#check MulHom
#check MulHomClass
#check MulHomClass.toMulHom
#check map_mul

/- Def: Monoid Morphism-/
#check MonoidHom --note, this is also used for groups
#check MonoidHomClass
#check MonoidHomClass.toMonoidHom
#check MonoidHomClass.toMulHomClass
#check MonoidHomClass.toOneHomClass

#check OneHom
#check OneHomClass
#check map_one

#check ZeroHom
#check ZeroHomClass
#check map_zero
