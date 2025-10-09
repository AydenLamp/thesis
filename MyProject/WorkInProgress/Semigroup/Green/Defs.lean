import Mathlib

/-!
# Green's Relations Definitions

This file defines Green's relations 𝓡, 𝓛, 𝓙, and 𝓗 for semigroups.
It also Provides a set-based implementation of the equivalence classes for these relations.

## Main definitions

* Preorder Relations `≤𝓡`, `≤𝓛`, `≤𝓙`, `≤𝓗` with Reflexivity and transativity
* Equivalence Relations `𝓡`, `𝓛`, `𝓙`, `𝓗` with Refl Trans and Symm
* Set-based equivalence classes

## Main Theorems

TODO

## Notation

todo

## Blueprint

TODO

-/
/-! ### Core Green's relations definitions

This section defines the fundamental Green's preorders and equivalences. We start with the
basic preorder definitions using `WithOne` elements, establish their preorder properties,
and then derive the equivalence relations as symmetric closures.
-/

namespace Semigroup

variable {S} [Semigroup S]

/-- the 𝓡 preorder: a ≤𝓡 b iff a*S¹ ⊆ b*S¹ -/
def RPreorder (a b : S) : Prop := ∃ x : WithOne S , ↑a = ↑b * x

/-- the 𝓛 preorder: a ≤𝓛 b iff S¹*a ⊆ S¹*b -/
def LPreorder (a b : S) : Prop := ∃ x : WithOne S, ↑a = x * ↑b
/-- the 𝓙 preorder: a ≤𝓙 b iff S¹*a*S¹ ⊆ S¹*b*S¹ -/
def JPreorder (a b : S) : Prop := ∃ x y : WithOne S, a = x * b * y

/-! Preorder notation, typed \leq\MCR -/
notation:50 f " ≤𝓡 " g:50 => RPreorder f g
notation:50 f " ≤𝓛 " g:50 => LPreorder f g
notation:50 f " ≤𝓙 " g:50 => JPreorder f g

/-- the 𝓗 preorder -/
def HPreorder (a b : S) : Prop := a ≤𝓡 b ∧ a ≤𝓛 b

notation:50 f " ≤𝓗 " g:50 => HPreorder f g

/-! Reflexivity lemmas -/
@[simp] lemma RPreorder.refl (x : S) : x ≤𝓡 x := by use 1; simp
@[simp] lemma LPreorder.refl (x : S) : x ≤𝓛 x := by use 1; simp
@[simp] lemma JPreorder.refl (x : S) : x ≤𝓙 x := by use 1, 1; simp
@[simp] lemma HPreorder.refl (x : S) : x ≤𝓗 x := by simp [HPreorder]

/-! Transitivity lemmas -/
@[simp] lemma RPreorder.trans (x y z : S) : x ≤𝓡 y → y ≤𝓡 z → x ≤𝓡 z := by
  simp [RPreorder]; intros h₁ h₂ h₃ h₄
  use (h₃ * h₁)
  rw [← mul_assoc, ← h₄, h₂]
@[simp] lemma LPreorder.trans (x y z : S) : x ≤𝓛 y → y ≤𝓛 z → x ≤𝓛 z := by
  unfold LPreorder; rintro ⟨u, hu⟩ ⟨v, hv⟩
  use u * v; rw [hu, hv, mul_assoc]
@[simp] lemma JPreorder.trans (x y z : S) : x ≤𝓙 y → y ≤𝓙 z → x ≤𝓙 z := by
  unfold JPreorder; rintro ⟨u₁, v₁, hu⟩ ⟨u₂, v₂, hv⟩
  use u₁ * u₂, v₂ * v₁; rw [hu, hv]; simp [mul_assoc]
@[simp] lemma HPreorder.trans (x y z : S) : x ≤𝓗 y → y ≤𝓗 z → x ≤𝓗 z := by
  unfold HPreorder; rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
  constructor
  · apply RPreorder.trans x y z <;> assumption
  · apply LPreorder.trans x y z <;> assumption

/-! Preorder instances -/
def RPreorder.isPreorder : IsPreorder S RPreorder where
  refl := RPreorder.refl
  trans := RPreorder.trans
def LPreorder.isPreorder : IsPreorder S LPreorder where
  refl := LPreorder.refl
  trans := LPreorder.trans
def JPreorder.isPreorder : IsPreorder S JPreorder where
  refl := JPreorder.refl
  trans := JPreorder.trans
def HPreorder.isPreorder : IsPreorder S HPreorder where
  refl := HPreorder.refl
  trans := HPreorder.trans

/-- The Symmetric Closure of a preorder is an equivalence-/
def _root_.IsPreorder.SymmClosure {α : Type*} (p : α → α → Prop) (h : IsPreorder α p) : Equivalence (λ a b  => p a b ∧ p b a) where
  refl := by simp [h.refl]
  symm := by aesop
  trans {x y z : α} (h₁ : p x y ∧ p y x) (h₂ : p y z ∧ p z y) : p x z ∧ p z x := by
    obtain ⟨hxy, hyx⟩ := h₁
    obtain ⟨hyz, hzy⟩ := h₂
    exact ⟨h.trans x y z hxy hyz, h.trans z y x hzy hyx⟩

def REquiv (x y : S) : Prop := x ≤𝓡 y ∧ y ≤𝓡 x
notation :50 a " 𝓡 " b:50 => REquiv a b

def REquiv.isEquivalence : Equivalence (fun x y : S ↦ x 𝓡 y) := by
  have H := IsPreorder.SymmClosure (fun x y : S ↦ x ≤𝓡 y) (RPreorder.isPreorder)
  simp_all [REquiv]

@[simp] lemma REquiv.refl (x : S) : x 𝓡 x := REquiv.isEquivalence.refl x

@[simp] lemma REquiv.symm {x y : S} (h : x 𝓡 y) : y 𝓡 x := REquiv.isEquivalence.symm h

@[simp] lemma REquiv.trans {x y z : S} (h₁ : x 𝓡 y) (h₂ : y 𝓡 z) : x 𝓡 z := REquiv.isEquivalence.trans h₁ h₂

/-- The equivalence relation `𝓛` -/
def LEquiv (x y : S) : Prop := x ≤𝓛 y ∧ y ≤𝓛 x

notation :50 a " 𝓛 " b:50 => LEquiv a b

def LEquiv.isEquivalence : Equivalence (fun x y : S ↦ x 𝓛 y) := by
  have H := IsPreorder.SymmClosure (fun x y : S ↦ x ≤𝓛 y) (LPreorder.isPreorder)
  simp_all [LEquiv]

@[simp] lemma LEquiv.refl (x : S) : x 𝓛 x := LEquiv.isEquivalence.refl x

@[simp] lemma LEquiv.symm {x y : S} (h : x 𝓛 y) : y 𝓛 x := LEquiv.isEquivalence.symm h

@[simp] lemma LEquiv.trans {x y z : S} (h₁ : x 𝓛 y) (h₂ : y 𝓛 z) : x 𝓛 z := LEquiv.isEquivalence.trans h₁ h₂

/-- The equivalence relation `𝓙` -/
def JEquiv (x y : S) : Prop := x ≤𝓙 y ∧ y ≤𝓙 x

notation :50 a " 𝓙 " b:50 => JEquiv a b

def JEquiv.isEquivalence : Equivalence (fun x y : S ↦ x 𝓙 y) := by
  have H := IsPreorder.SymmClosure (fun x y : S ↦ x ≤𝓙 y) (JPreorder.isPreorder)
  simp_all [JEquiv]

@[simp] lemma JEquiv.refl (x : S) : x 𝓙 x := JEquiv.isEquivalence.refl x

@[simp] lemma JEquiv.symm {x y : S} (h : x 𝓙 y) : y 𝓙 x := JEquiv.isEquivalence.symm h

@[simp] lemma JEquiv.trans {x y z : S} (h₁ : x 𝓙 y) (h₂ : y 𝓙 z) : x 𝓙 z := JEquiv.isEquivalence.trans h₁ h₂

/-- The equivalence relation `𝓗` -/
def HEquiv (x y : S) : Prop := x ≤𝓗 y ∧ y ≤𝓗 x

notation :50 a " 𝓗 " b:50 => HEquiv a b

def HEquiv.isEquivalence : Equivalence (fun x y : S ↦ x 𝓗 y) := by
  have H := IsPreorder.SymmClosure (fun x y : S ↦ x ≤𝓗 y) (HPreorder.isPreorder)
  simp_all [HEquiv]

@[simp] lemma HEquiv.refl (x : S) : x 𝓗 x := HEquiv.isEquivalence.refl x

@[simp] lemma HEquiv.symm {x y : S} (h : x 𝓗 y) : y 𝓗 x := HEquiv.isEquivalence.symm h

@[simp] lemma HEquiv.trans {x y z : S} (h₁ : x 𝓗 y) (h₂ : y 𝓗 z) : x 𝓗 z := HEquiv.isEquivalence.trans h₁ h₂

/-- The 𝓗 equivalence relation is the intersection of 𝓡 and 𝓛 equivalences. -/
theorem HEquiv.iff_REquiv_and_LEquiv (x y : S) : x 𝓗 y ↔ x 𝓡 y ∧ x 𝓛 y := by
  simp_all [HEquiv, HPreorder, LEquiv, REquiv]
  tauto


/-! ### Set-defined classes -/

def REquiv.set (x : S) : Set (S) :=
  {a | a 𝓡 x}
def LEquiv.set (x : S) : Set (S) :=
  { a | a 𝓛 x}
def JEquiv.set (x : S) : Set (S) :=
  { a | a 𝓙 x}
def HEquiv.set (x : S) : Set (S) :=
  { a | a 𝓗 x}

notation "⟦" x "⟧𝓡" => REquiv.set x
notation "⟦" x "⟧𝓛" => LEquiv.set x
notation "⟦" x "⟧𝓙" => JEquiv.set x
notation "⟦" x "⟧𝓗" => HEquiv.set x

/-! ### Simp Lemmas
This section provides lemmas tagged with @[simp]. For lemmas that take hypothesis
like `h : a ≤𝓡 a * b`, make sure that you call `simp [h]` to use them. -/

/-- `x * y` is always `≤𝓡 x` -/
@[simp] lemma RPreorder.mul_right_self (x y : S) : x * y ≤𝓡 x := by
  use y; rw [WithOne.coe_mul]

/-- `x * y` is always `≤𝓛 y` -/
@[simp] lemma LPreorder.mul_left_self (x y : S) : x * y ≤𝓛 y := by
  use x; rw [WithOne.coe_mul]

/-- `x * y * z` is always `≤𝓙 y` -/
@[simp] lemma JPreorder.mul_sandwich_self (x y z : S) : x * y * z ≤𝓙 y := by
  use x, z; simp

/-- `x ≤𝓡 x * y` implies `x 𝓡 x * y` -/
@[simp] lemma REquiv.of_preorder_mul_right (x y : S) (h : x ≤𝓡 x * y) : x 𝓡 x * y := by
  simp_all [REquiv]

/-- `x ≤𝓛 y * x` implies `x 𝓛 y * x` -/
@[simp] lemma LEquiv.of_preorder_mul_left (x y : S) (h : x ≤𝓛 y * x) : x 𝓛 y * x := by
  simp_all [LEquiv]

/-- `x ≤𝓙 y * x * z` implies `x 𝓙 y * x * z` -/
@[simp] lemma JEquiv.of_preorder_mul_sandwich (x y z : S) (h : x ≤𝓙 y * x * z) : x 𝓙 y * x * z := by
  simp_all [JEquiv]

/-! ### Basic Lemmas for 𝓡 and 𝓛 and 𝓙 equivalences (Prop 1.4.3) -/

/-! Compatibility of Green's relations with multiplication -/

@[simp] lemma RPreorder.lmult_compat (x y z : S) (h : x ≤𝓡 y) : z * x ≤𝓡 z * y := by
  obtain ⟨u, hu⟩ := h; use u
  simp [mul_assoc, hu]

@[simp] lemma REquiv.lmult_compat (x y z : S) (h : x 𝓡 y) : z * x 𝓡 z * y := by
  simp_all [REquiv]

@[simp] lemma LPreorder.rmult_compat (x y z : S) (h : x ≤𝓛 y) : x * z ≤𝓛 y * z := by
  obtain ⟨u, hu⟩ := h; use u
  simp [← mul_assoc, hu]

@[simp] lemma LEquiv.rmult_compat (x y z : S) (h : x 𝓛 y) : x * z 𝓛 y * z := by
  simp_all [LEquiv]

/-! cancellation lemmas -/

/-- If `x 𝓡 x * y * z`, then `x 𝓡 x * y`. -/
@[simp] lemma REquiv.right_cancel (x y z : S) (h : x 𝓡 x * y * z) : x 𝓡 x * y := by
  simp_all [REquiv]
  obtain ⟨⟨u, hu⟩, _⟩ := h
  use z * u; simp_rw [WithOne.coe_mul, ← mul_assoc] at *
  exact hu

/-- If `x 𝓡 x * y * z`, then `x * y 𝓡 x * y * z`.-/
@[simp] lemma REquiv.right_extend (x y z : S) (h : x 𝓡 x * y * z) : x * y 𝓡 x * y * z := by
  simp_all [REquiv]
  obtain ⟨⟨u, hu⟩, _⟩ := h
  use u * y; simp_rw [WithOne.coe_mul, ← mul_assoc] at *
  rw [← hu]

/-- If `x 𝓛 z * y * x`, then `x 𝓛 y * x`. -/
@[simp] lemma LEquiv.left_cancel (x y z : S) (h: x 𝓛 z * y * x ) : x 𝓛 y * x := by
  simp_all [LEquiv]
  obtain ⟨u, hu⟩ := h
  use u * z; simp_rw [WithOne.coe_mul, ← mul_assoc] at *
  exact hu

/-- If `x 𝓛 z * y * x`, then `y * x 𝓛 z * y * x`. -/
@[simp] lemma LEquiv.left_extend (x y z : S) (h : x 𝓛 z * y * x) : y * x 𝓛 z * y * x := by
  simp_all [LEquiv]
  obtain ⟨u, hu⟩ := h
  use y * u; simp_rw [WithOne.coe_mul, ← mul_assoc] at *
  nth_rw 1 [hu]
  simp [mul_assoc]

@[simp] lemma RPreorder.implies_J (x y : S) (h : x ≤𝓡 y) : x ≤𝓙 y := by
  simp_all [JPreorder, RPreorder]
  obtain ⟨u, hu⟩ := h
  use 1, u; simp_all

@[simp] lemma LPreorder.implies_J (x y : S) (h : x ≤𝓛 y) : x ≤𝓙 y := by
  simp_all [JPreorder, LPreorder]
  obtain ⟨u, hu⟩ := h
  use u, 1; simp_all

@[simp] lemma REquiv.implies_J (x y : S) (h : x 𝓡 y) : x 𝓙 y := by
  simp_all [JEquiv, REquiv, RPreorder.implies_J]

@[simp] lemma LEquiv.implies_J (x y : S) (h : x 𝓛 y) : x 𝓙 y := by
  simp_all [JEquiv, LEquiv, LPreorder.implies_J]

/-! ### Green's D relation -/

/-- Green's D-relation, defined as the composition of R and L relations -/
def DEquiv : S → S → Prop := λ x y => ∃ z, x 𝓡 z ∧ z 𝓛 y
infix:50 " 𝓓 " => DEquiv

def DEquiv.set (x : S) : Set S := {y: S | y 𝓓 x}
notation "⟦" x "⟧𝓓" => DEquiv.set x

/-- **Green's Commutativity**: R and L relations commute under composition -/
theorem RLEquiv.comm (x y : S) : (∃ z, x 𝓛 z ∧ z 𝓡 y) ↔ (∃ z, x 𝓡 z ∧ z 𝓛 y) := by
  constructor
  · rintro ⟨c, hl, hr⟩
    rcases _ : hl with ⟨hl1, hl2⟩; rcases _ : hr with ⟨hr1, hr2⟩
rw [L_preorder_iff_without_one] at hl1;
    cases hl1 with
    | inl heq => subst heq; use b; constructor; assumption; apply eqv_of_preorder_refl
    | inr hneq =>
      obtain ⟨u, hu⟩ := hneq; subst hu; use u* b
      rw [R_preorder_iff_without_one] at hr2
      cases hr2 with
      | inl heq => subst heq; constructor; apply eqv_of_preorder_refl; assumption
      | inr hneq =>
        obtain ⟨v, hv⟩ := hneq; subst hv
        constructor
        · apply R_eqv_lmult_compat; assumption
        · rw [← mul_assoc]; apply L_eqv_rmult_compat; assumption
  · rintro ⟨c, hl, hr⟩
    rcases _ : hl with ⟨hl1, hl2⟩; rcases _ : hr with ⟨hr1, hr2⟩
    rw [R_preorder_iff_without_one] at hl1;
    cases hl1 with
    | inl heq => subst heq; use b; constructor; assumption; apply eqv_of_preorder_refl
    | inr hneq =>
      obtain ⟨v, hv⟩ := hneq; subst hv; use b*v
      rw [L_preorder_iff_without_one] at hr2
      cases hr2 with
      | inl heq => subst heq; constructor; apply eqv_of_preorder_refl; assumption
      | inr hneq =>
        obtain ⟨u, hu⟩ := hneq; subst hu
        constructor
        · apply L_eqv_rmult_compat; assumption
        · rw [ mul_assoc]; apply R_eqv_lmult_compat; assumption

/-- Alternate Def of Green's `𝓓` equivalence -/
theorem DEquiv.iff_comm (x y : S) : x 𝓓 y ↔ ∃ z, x 𝓛 z ∧ z 𝓡 y := by
  unfold DEquiv; rw [← RLEquiv.comm]

@[simp] lemma DEquiv.refl (x : S) : x 𝓓 x := by
  simp [DEquiv]; use x; constructor <;> simp

@[simp] lemma DEquiv.symm {x y : S} : x 𝓓 y → y 𝓓 x := by
  rw [DEquiv.iff_comm]
  · rintro ⟨z, ⟨hz1, hz2⟩⟩; use z; constructor
    · exact hz2.symm
    · exact hz1.symm

/-- The 𝓓-relation is preserved by 𝓛-equivalent elements on the right.
If `x 𝓓 y` and `y 𝓛 z`, then `x 𝓓 z`. -/
lemma DEquiv.closed_under_L {x y z : S} : x 𝓓 y → y 𝓛 z → x 𝓓 z := by
  simp [DEquiv]; intros w h1 h2 h3; use w; constructor
  · exact h1
  · exact (LEquiv.trans h2 h3)

/-- The 𝓓-relation is preserved by 𝓡-equivalent elements on the right.
If `x 𝓓 y` and `y 𝓡 z`, then `x 𝓓 z`. -/
lemma DEquiv.closed_under_R {x y z : S} : x 𝓓 y → y 𝓡 z → x 𝓓 z := by
  simp [DEquiv.iff_comm]; intros w h1 h2 h3; use w; constructor
  · exact h1
  · exact (REquiv.trans h2 h3)

/-- The 𝓓-relation is transitive. This is proved using closure under 𝓡 and 𝓛. -/
lemma DEquiv.trans {x y z : S} : x 𝓓 y → y 𝓓 z → x 𝓓 z := by
  intros h1 h2
  obtain ⟨w, ⟨hw1, hw2⟩⟩ := h2
  have hd1 : x 𝓓 w := by apply DEquiv.closed_under_R; exact h1; assumption
  apply DEquiv.closed_under_L hd1 hw2

/-- The 𝓓-relation is an equivalence relation on `S`. This instance combines the
reflexivity, symmetry and transitivity proofs. -/
def DEquiv.isEquivalence : Equivalence (fun x y : S => x 𝓓 y) where
  refl := DEquiv.refl
  symm := DEquiv.symm
  trans := DEquiv.trans

/-! ### Idempotent properties (Prop 1.4.1)
This section characterizes elements that are 𝓡- below or 𝓛- below an idempotent. -/


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
