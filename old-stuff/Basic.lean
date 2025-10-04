import MyProject.RegExToENFA

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

/-!
# Languages
- Words are implemented as lists over the alphabet.
- There is a coersion from `List α` → `FreeMonoid α`
-/
variable {α β : Type*}

#check Language α
#check Language.instSemiring

variable (l₁ l₂ : Language α)
#check l₁ + l₂
#check Language.add_def

#check l₁ * l₂
#check Language.mul_def

#check (0 : Language α) + 1
#check ([] : List α) ∈ (1 : Language α)

#check Language.reverse
#check Language.reverseIso

#check Language.map
#check FreeMonoid.map

variable (w₁ : List α)
#check w₁ ∈ l₁
#check Language.ext_iff

-- instance : Monoid (List α) := by infer_instance
instance : Monoid (FreeMonoid α) := by infer_instance

variable (w₂ : FreeMonoid α)
#check w₂ ∈ l₁

#check FreeMonoid.ofList

#check (w₁ : FreeMonoid α)
#check (w₂ : List α)


/-
- TODO: Def of regular language (rather than Mathlib's recognizible?)
   - THeorem : Regular ↔ Recognizible
-/

/- # Questions -/

/- What is a morphism of DFAs? What is a morphism of Languages? Of Regular Expressions?
Mathlib defines `DFA.comap` and `RegularExpression.map` for lifting a functions on alphabets
to function of DFAs / Regular Expressions.

Should I create definitions that convert morphisms on languages to morphisms on DFAs/Regexes?
-/

#check DFA.reindex -- Mathlib's Notion of equality of DFA
#check DFA.comap -- Lifts `f : A → B` to `DFA A _ → DFA B _`

/- Regular vs recognizable -/
-- Textbook calles this "recognizable" not "regular"
#check Language.IsRegular -- Regular if there exists a DFA with a `Fintype` on states accepting `L`
#check Language.isRegular_iff

-- Rational/Reglar Languages
#check RegularExpression
-- "Morphism" on Rational Lanugages
#check RegularExpression.map -- Lifts `f : A → B` to

-- Regex and language map commute
-- Textbook lemma: (prop 2.3) Rational languages are prserved under (semiring) morphisms of the languages
  -- If `L` is a rational language of `A*` then `φ L` is a rational langugae of `B*`
#check RegularExpression.matches'_map

/-! #  quotients preserve regulariety
Mathlib's quotient is defined on languages
Mathlib's deriv proves that derives preserve regularity (recognition by Regex)
  and is used to define the Regex Matches' algorithm
-/

#check Language.leftQuotient
#check RegularExpression.deriv

/- # MINIMAL DFAs
Mathlib Does not have a notion of minimal DFAs
There is two : Minimal amount of states and a more complicated def from textbook:
Textbook def:
  We define a partial order on DFAs (of the same alphabet)
  Let `A₁ : DFA α Q₁` and `A₂ : DFA α Q₂` be DFAs with starting states `q₁` and `q₂` and accepting states `F₁` and `F₂`
  `A₁ ≤ A₂ ↔ ∃ φ : Q₂ → Q₁ , IsSurjective φ ∧ `
    `φ (q₂) = q₁ ∧ `
    `φ (F₂) = φ (F₁) ∧`
    `∀ (u ∈ α*) (q ∈ Q₁), φ (A₁.eval q u) = A₂.eval (φ q) u`
The nerode automaton of L is minimal for this partial order.
-/


/- # Kleene's theorem
Theorem : A language is rational (Regex) ↔ A language is recognizable (DFA)
- Forward direction : PR Does this Regex → εNFA → NFA → DFA
- Backaward direction: DFA → Regex - Another PR does this with DFA → NFA → GNFA → Regex

Coorolary - Recognisable/rational languages are closed under boolean operations,
product, star, quotients, morphisms and inverses of morphisms.
  - what does morphisms mean here? morphisms of languages? of alphabets?
-/
-- Regex → εNFA
theorem toεNFA_correct' {α : Type*} (P : RegularExpression α): P.toεNFA.accepts = P.matches' := by
  apply RegularExpression.toεNFA_correct

def kleene_forward {α : Type*} (P : RegularExpression α) :
    P.matches' = P.toεNFA.toNFA.toDFA.accepts := by sorry

/-!
# Transition Monoids of DFA
Mathlib defines Quotients and defines the Nerode automaton
-/

instance transformationMonoid (σ : Type*) : Monoid (σ → σ) where
  mul := Function.comp
  mul_assoc := by intros; rfl
  one := id
  one_mul := by intros; rfl
  mul_one := by intros; rfl

namespace transformationMonoid

@[simp] lemma one_id {σ : Type*} : (1 : σ → σ) = id := by rfl

@[simp] lemma mul_def {σ : Type*} (f g : σ → σ) : f * g = f ∘ g  := by rfl

variable {α σ : Type*}

end transformationMonoid

@[simp] lemma one_empty {α : Type*} : (1 : FreeMonoid α) = [] := by rfl

lemma mul_def {α : Type*} (a b : FreeMonoid α) : a * b = a.toList ++ b.toList := by rfl

variable {α σ : Type*}

#check FreeMonoid.lift

def DFA.transitionMonoidHom (M : DFA α σ) : FreeMonoid α →* (σ → σ) :=
  FreeMonoid.lift (fun (a : α) (s : σ) ↦ M.step s a)

#check MulHom.isClosed_range_coe

def MulHom.range {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) := { n // ∃ m : M, f m = n }

def DFA.transitionMonoid (M : DFA α σ) : Monoid (MulHom.range (M.transitionMonoidHom)) where
  mul := by
    simp_all [MulHom.range, transitionMonoidHom, ]
    intros f g
    rcases f with ⟨f, hf⟩
    rcases g with ⟨g, hg⟩
    use f ∘ g
    rcases hf with ⟨a, ha⟩
    rcases hg with ⟨b, hb⟩
    use a * b
    simp_all only [map_mul, transformationMonoid.mul_def]
  mul_assoc := by
    simp_all [MulHom.range, transitionMonoidHom]
    intros f a hfa g b hgb h c hc
    rfl
  one := ⟨id, by use 1; rfl⟩
  one_mul f := rfl
  mul_one f := rfl

def Language.toSyntacticMonoid (L : Language α) : Monoid (MulHom.range (L.toDFA.transitionMonoidHom)) := by
  apply DFA.transitionMonoid

-- TODO  Provide def of syntactic monoid from quotient congruence, and prove equivalence with above def

/- # Accessable and complete DFAs
complete = All states have a transition for every letter (transition function is total)
  This is requried by mathlib def
Accessable = Every state can be reached from the start state
Coaccessable = Every state can reach an accepting state
Trimmed = Accessable and Coaccessable

on pg 59, prop requires A be trimmed and complete.
How can it be coaccessable and complete (unless it always accepts?)

Theorem - All dfas are equivalent to a trimmed DFA (implement this)
-/

variable {α σ : Type*} (M : DFA α σ)

def IsAccessableState (s : σ) : Prop :=
  ∃ w : List α, M.evalFrom M.start w = s

def IsCoaccessableState (s : σ) : Prop :=
  ∃ w : List α, M.evalFrom s w ∈ M.reindex_apply_startccepts

/- # Minimization Algorithms
This is not being worked on by any PR.
TODO: Prove that the nerode automaton is Minimal.

These algorithms assume DFAs are trimmed

There are multiple algorithms for unifying nondistinguishable states
Hopcroft's and Morre's work by iterating on some set untill a fixpoint is reached.
They compute the NERODE Equivalence (on states)

Brzozowski's algorithm
By reversing an NFA and converting to a DFA twice, we produce the minimal DFA
Reversing once merges nondistinguishable states, but may produce several accepitng states.

Proving that the nerode automaton is minimal involves proving that it combines states
by the nerode congruence.
-/
