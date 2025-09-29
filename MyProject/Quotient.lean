import Mathlib

/-!
# Congruences
- A congruence is an equivalence relation that preserves a multiplication.
- TODO: Define Ree's congruence
-/

#check Con  -- A structure that extends `Setoid`
#check Con.mul' -- The proof that the equivalence relation is compatible with multiplication
-- There is a coeersion from `Con α` to `α → α → Prop`


/-
## Complete lattice of congruences on a type
For two congruence relations `c₁, c₁`, `c₁ < c₂` if `c₁` is a finer relation than `c₂`
We write `c₁ ⊓ c₂` for the finest congruence coarser than both `c₁` and `c₂`.
We write `c₁ ⊔ c₂` for the coarsest congruence finer than both `c₁` and `c₂`.
-/
#check Con.le_def
#check Con.inf_iff_and
#check Con.sup_eq_conGen

/-!
## Quotients by Congruences
- A congruence relation invokes a quotient structure representing the type of equivalence classes of the congruence.
- In the case of a Semigroup (Monoid), the quotient structure is also a Semigroup (Monoid)
- There is a coercion from elements of a type to the element's equivalence class under a congruence relation.
-/

#check Con.Quotient -- The type of equivalence classes under a congruence

/- The function on the quotient type induced by a function on the original
type that respects equivalence classes -/
#check Con.liftOn

/- An induction principal that proves propositions about the quotient type by proving it
for all elements of the original type -/
#check Con.induction_on

/- Two elements have the same equivalence class if they are related by the congruence. -/
#check Con.eq

/- The quotient semigroup of a congruence relation -/
#check Con.semigroup

/- The quotient monoid of a monoid and a congruence relation -/
#check Con.monoid

/-
## Morphisms and Congruences
* `Con.ker`: the kernel of a monoid homomorphism as a congruence relation
* `Con.mk'`: the map from a monoid to its quotient by a congruence relation
* `Con.lift`: the homomorphism on the quotient given that the congruence is in the kernel
* `Con.map`: homomorphism from a smaller to a larger quotient
-/

/-  For types `M, N` and a congruence `c : Con N`, a morphism `f : M → N` induces a
congruence on `f`'s domain defined by `x ≃ y ↔ c (f x) (f y)` -/
#check Con.comap

/- If e : M →* N is surjective then (c.comap e).Quotient ≃* c.Quotient with c : Con N -/
#check Con.comapQuotientEquivOfSurj

/- For types `M, N`, a function `f : M → N`, and a congruence `c : Con M`, we define a `d : Con N`
by the coarsest congruence such that `d x y ↔ c (f⁻¹ x) (f⁻¹ y)`-/
#check Con.mapGen

/- For `(c d : Con α)`, from `c = d` we can create an isomorphism `c.Quotient ≃ d.Quotient` -/
#check Con.congr

/- The kernel of a monoid homomorphism as a congruence relatoin -/
#check Con.ker
#check Con.ker_rel -- the definition of this generated congruence

/- The kernel of a mulHom as a congruence relation -/
#check Con.mulKer

/- the Monoid homomorphism from a monoid to its quotient -/
#check Con.mk'
#check Con.mk'_surjective -- that homomorphism is surjective


/- Given a surjective multiplicative-preserving function `f` whose kernel is contained in a
congruence relation `c`, the congruence relation on `f`'s codomain defined by '`x ≈ y` iff the
elements of `f⁻¹(x)` are related to the elements of `f⁻¹(y)` by `c`.' -/
#check Con.mapOfSurjective

/- Given a congruence relation `c` on a type `M` with a multiplication, the order-preserving
bijection between the set of congruence relations containing `c` and the congruence relations
on the quotient of `M` by `c`. -/
#check Con.correspondence

/- Given a monoid homomorphism `f : N → M` and a congruence relation `c` on `M`, the congruence
relation induced on `N` by `f` equals the kernel of (`c`'s quotient homomorphism composed with `f`) -/
#check Con.comap_eq

/- The Monoid homomorphism on the quotient of a monoid by a congruence relation `c` induced by a
homomorphism constant on `c`'s equivalence classes. -/
#check Con.lift

/- For Monoids `M, N`, `f : M →* N`, and a congruence `c : Con M` such that
`c ≤ ker f` (`f` is constant on `c`'s equivalence classes), `f` is equal
to the induced homomorphism on the quotient `c.Lift f` composed with `c.mk'` -/
#check Con.lift_comp_mk'

/- Given a homomorphism `f` from the quotient of a monoid by a congruence relation, `f` equals the
homomorphism on the quotient induced by `f` composed with the natural map from the monoid to
the quotient. -/
#check Con.lift_apply_mk'

/- Homomorphisms on the quotient of a monoid by a congruence relation are equal if they
are equal on elements that are coercions from the monoid. -/
#check Con.lift_funext

/- Surjective monoid homomorphisms constant on a congruence relation `c`'s equivalence classes
induce a surjective homomorphism on `c`'s quotient. -/
#check Con.lift_surjective_of_surjective

/- Given a congruence relation `c` on a monoid and a homomorphism `f` constant on `c`'s
equivalence classes, `f` has the same image as the homomorphism that `f` induces on the
quotient. -/
#check Con.lift_range


/- Given a monoid homomorphism `f` from `M` to `P`, the kernel of `f` is the unique congruence
relation on `M` whose induced map from the quotient of `M` to `P` is injective. -/
#check Con.ker_eq_lift_of_injective

/- The homomorphism induced on the quotient of a monoid by the kernel of a monoid homomorphism. -/
#check Con.kerLift

/- A monoid homomorphism `f` induces an injective homomorphism on the quotient by `f`'s kernel. -/
#check Con.kerLift_injective

/- Given congruence relations `c, d` on a monoid such that `d` contains `c`, `d`'s quotient
map induces a homomorphism from the quotient by `c` to the quotient by `d`. -/
#check Con.map

/-!
## First isomorphism Theorem for Monoids
For monoids `M, P`, and `f : M →* P`, the quotient monoid induced by `ker f` is isomorphic
to the range of `f`
-/

#check Con.quotientKerEquivRange

/- In the case where `f : M →* P` has a right inverse, then the quotient monoid induced by `ker f` is
isomorphic to `P` -/
#check Con.quotientKerEquivOfRightInverse

/- In the case where `f : M →* P` is surjective, the quotient monoid induced by `ker f` is isomorphic
to `P` -/
#check Con.quotientKerEquivOfSurjective

/-!
## Second Isomorphism Theorem for Monoids
given monoids `N M` and `f : N →* M` and `c : Con M`, The quotient monoid on `N` induced by
`c.comap f` is isomorphic to the range of the MonoidHom of(`c.mk'.comp f`
-/

#check Con.comapQuotientEquiv

/-!
## Third Isomorphism Theorem for Monoids
Given two congruences `c d : Con M` with `c ≤ d`, the quotient induced by
`ker (c.map d h)` is isomorphic to the quotient induced by `d`
-/

#check Con.quotientQuotientEquivQuotient


/-!
# Subsemigroups
Mathlib defines a complete lattus on subsemigroups.
-/

#check Subsemigroup

/- A typeclass, `MulMemClass S M` says that `S` is a type of sets `s : Set M`
that are closed under multiplication -/
#check MulMemClass

#check Subsemigroup.ofClass -- Constructs the Subsemigroup obtained from an element of a `MulMemClass`

/- The subsemigroup of elements `x : M` such that `f x = g x` -/
#check MulHom.eqLocus

/- The natural semigroup hom from a subsemigroup of `M` to `M`-/
#check MulMemClass.subtype
