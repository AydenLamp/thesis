import Mathlib

/-
# Accessable DFAs
An Accessable state of a DFA is a state that can be reached from the start state by some word.
An Accessable DFA is a DFA where all states are accessable.
The first step of minimization is to convert a DFA to an accessable DFA.

## Computability
There is a `prop` based definition of an Accessable DFA, where for all states we have the propositon
`∃ w : List α, M.eval w = s`. However, we cannot computably obtain such a `w` for an arbitrary state `s`.
Thus, we define a alternate, more computable structure for Accessable DFAs, which requires a function
`toWord : σ → List α` that computably gives such a `w` for each state `s`. This will either be a
seperate structure or a `toWord` function that is defined on `AccessableDFA` with a `Fintype`.

Question: Are these definitions equivalent for `Fintype` DFAs? Given a `prop` based accessable DFA
over a `Fintype` of states, can we computably obtain such a `toWord` function?
Idea: Use a tree search?
-/

section Accessable

namespace DFA

universe v u

variable {α : Type u} {σ : Type v}

def isAccessableState {M : DFA α σ} (s : σ) : Prop := ∃ a : List α, M.eval a = s

structure AccessableDFA (α : Type u) (σ : Type v) extends toDFA : DFA α σ where
  isAccessable : ∀ s : σ, toDFA.isAccessableState s

/-- We define a function to convert a DFA to an Accessable DFA
TODO: Should I prove that this is a (partial) bijection? -/
def toAccessable (M : DFA α σ) : AccessableDFA α {s // M.isAccessableState s} where
  step := fun s a => ⟨M.step s.val a, by
    simp_all [isAccessableState]
    obtain ⟨s, ⟨w, hs⟩⟩ := s
    use w ++ [a]
    simp_all [eval]
    suffices h : M.evalFrom M.start w = s
    · rw [h]
    · simp_all [eval]⟩
  start := ⟨M.start, by simp_all only [isAccessableState]; use []; simp⟩
  accept := { s | s.val ∈ M.accept}
  isAccessable := by
    intros s
    simp_all [isAccessableState]
    obtain ⟨s, ⟨w, hx⟩⟩ := s
    use w
    apply Subtype.eq
    induction w using List.reverseRecOn generalizing s with
    | nil => simp_all; simp at hx; exact hx
    | append_singleton w a ih =>
      simp at hx
      simp_all


lemma toAccessable.eval (M : DFA α σ) (w : List α) : (M.toAccessable.eval w).val = M.eval w := by
  induction w using List.reverseRecOn with
  | nil => simp_all [toAccessable]
  | append_singleton w a ih =>
    simp_all [toAccessable]

/-- Our `toAccessable` function preserves the language recognized -/
theorem toAccessable.pres_lang (M : DFA α σ) (w : List α) : w ∈ M.accepts ↔ w ∈ (M.toAccessable).accepts := by
  simp_all [mem_accepts]
  constructor
  · intro h
    have h₂ := toAccessable.eval M w
    simp_all [toAccessable]
  · intros h
    have h₂ := toAccessable.eval M w
    simp_all [toAccessable]


end DFA

end Accessable

section AccessableFin

namespace DFA

universe u v

variable {α : Type u} {σ : Type v} [Fintype σ] [Fintype α]

/-- TODO: Use a BFS algorithm?
Brute force + pumping lemma ? -/
def isAccessableStateBool {M : DFA α σ} (s : σ) : Bool := sorry

/-- Proof that the above function is correct -/
lemma isAccessableStateBool_correct {M : DFA α σ} (s : σ) :
    M.isAccessableState s ↔ M.isAccessableStateBool s := by sorry

instance accessableDecidable (M : DFA α σ) : DecidablePred (M.isAccessableState) := by
  intros s
  rcases h : (M.isAccessableStateBool s)
  · apply isFalse
    rw [isAccessableStateBool_correct]
    exact ne_true_of_eq_false h
  · apply isTrue
    rw [isAccessableStateBool_correct]
    exact h

/-- Now that we have a `DecidablePred` instance, we can
use it to construct the `Finset` of accessable states -/
def accessableFinset (M : DFA α σ) : Finset σ :=
  Finset.univ.filter (fun s => M.isAccessableState s)

/-- We can now prove that the `toAccessable` function preserves `Fintype` states -/
instance FintypeAccessable (M : DFA α σ) : Fintype {s // M.isAccessableState s} := by infer_instance

/-- Given that a state is accessable, return the word that accesses it.
Should be simmilar to `isAccessableStateBool` -/
def toWord (M : AccessableDFA α σ) (s : σ) : List α := by sorry

/-- Proof the above function is correct -/
lemma toWord_correct (M : AccessableDFA α σ) (s : σ) :
    M.eval (toWord M s) = s := by sorry

end DFA

end AccessableFin

/-!
# DFA Morphisms
We define morphisms between DFAs. For DFAs `M, N`, a morphism `f : M →ₗ N` is a function
from the states of `M` to the states of `N`
-/

section Morphisms

open DFA

variable {α σ σ₁ σ₂: Type* }

structure DFAHom (M : DFA α σ₁) (N : DFA α σ₂) where
  /-- The underlying function map from States of `M` to States of `N` -/
  toFun : σ₁ → σ₂
  /-- The proposition that the function preserves the start state-/
  map_start : toFun M.start = N.start
  /-- The proposition that the function preserves the set of accepting states -/
  map_accept (q : σ₁) : q ∈ M.accept ↔ toFun q ∈ N.accept
  /-- The proposition that the function preserves state transitions -/
  map_step (q : σ₁) (w : List α) : toFun (M.evalFrom q w) = N.evalFrom (toFun q) w

/-- `M →ₗ N` denotes the type of `DFAHom M N` -/
infixr:25 " →ₗ " => DFAHom

variable {M : DFA α σ₁} {N : DFA α σ₂}

/-- The existance of `f : M →ₗ N` implies that the language of `M` equal to the language of `N`-/
theorem DFAHom.language_contained (f : M →ₗ N) : M.accepts = N.accepts := by
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

def DFAHom.rfl (M : DFA α σ) : M →ₗ M where
  toFun := id
  map_start := by rfl
  map_accept := by intros q; simp
  map_step := by intros q w; simp

structure DFAEquiv (M : DFA α σ₁) (N : DFA α σ₂) where
  toDFAHom : M →ₗ N
  toInvDFAHom : N →ₗ M
  left_inv : Function.LeftInverse toInvDFAHom.toFun toDFAHom.toFun
  right_inv : Function.RightInverse toInvDFAHom.toFun toDFAHom.toFun

/-- `M ≃ₗ N` denotes the type of `DFAEquiv M N` -/
infixr:25 " ≃ₗ " => DFAEquiv

structure AccessableDFAEquiv (M : AccessableDFA α σ₁) (N : AccessableDFA α σ₂) extends M.toDFA ≃ₗ N.toDFA

infixr:25 " ≃ₐ " => AccessableDFAEquiv

/-- A structure for surjective Morphisms of Accessable DFAs -/
structure AccessableDFAHomSurj (M : AccessableDFA α σ₁) (N : AccessableDFA α σ₂) extends M.toDFA →ₗ N.toDFA where
  /-- The proposition that the function is surjective -/
  surjective : Function.Surjective toFun

/-- `M ↠ N` denotes the type of `AccessableDFAHomSurj M N` -/
infixr:25 " ↠ " => AccessableDFAHomSurj

end Morphisms

/-!
# Partial Order on DFAs
We define a partial order on Accessable DFAs.
Let `M : AccessableDFA α σ₁` and `N : AccessableDFA α σ₂`
We say `M ≤ N` if there is a surjective morphism from `N` to `M`.

This is not technically a partial order becuase it is not antisymmetric,
`M ≤ N ∧ N ≤ M` implies `M ≃ₗ N` but not `M = N`
-/

section PartialOrder

variable {α σ₁ σ₂ σ₃: Type*}

namespace DFA

def le (M : AccessableDFA α σ₁) (N : AccessableDFA α σ₂) : Prop := Nonempty (N ↠ M)

infix:50 " ≤ " => le

lemma le_refl (M : AccessableDFA α σ₁) : M ≤ M := by
  simp [le]
  apply Nonempty.intro
  apply AccessableDFAHomSurj.mk (DFAHom.rfl M.toDFA)
  · simp_all [Function.Surjective]
    intros s
    use s
    rfl

lemma le_trans {M : AccessableDFA α σ₁} {N : AccessableDFA α σ₂} {O : AccessableDFA α σ₃}
    (h₁ : M ≤ N) (h₂ : N ≤ O) : M ≤ O := by
  obtain f := h₁.some
  obtain g := h₂.some
  apply Nonempty.intro
  let I : O.toDFA →ₗ M.toDFA := by
    apply DFAHom.mk
      (toFun := f.toFun ∘ g.toFun)
      (map_start := by
        simp
        rw [g.map_start, f.map_start] )
      (map_accept := by
        intros q
        simp_all
        rw [g.map_accept]
        rw [f.map_accept])
      (map_step := by
        intros q w
        simp_all
        rw [g.map_step, f.map_step])
  exact AccessableDFAHomSurj.mk
    (toDFAHom := I)
    (surjective := by
      dsimp [I]
      apply Function.Surjective.comp
      · apply f.surjective
      · apply g.surjective )

lemma le_antisymm (M : AccessableDFA α σ₁) (N : AccessableDFA α σ₂) (h₁ : M ≤ N) (h₂ : N ≤ M) :
    Nonempty (M ≃ₐ N) := by
  obtain f := h₁.some
  obtain g := h₂.some
  apply Nonempty.intro
  apply AccessableDFAEquiv.mk
    (toDFAEquiv := by
      exact DFAEquiv.mk
        (toDFAHom := g.toDFAHom)
        (toInvDFAHom := f.toDFAHom)
        (left_inv := by
          simp_all [Function.LeftInverse]
          intro s
          obtain ⟨w, hs⟩ := M.isAccessable s
          simp_all [eval]
          rw [← hs]
          rw [g.map_step, f.map_step]
          rw [g.map_start, f.map_start])
        (right_inv := by
          simp_all [Function.RightInverse]
          intros s
          obtain ⟨w, hs⟩ := N.isAccessable s
          simp_all [eval]
          rw [← hs]
          rw [f.map_step, g.map_step, f.map_start, g.map_start]
          ))
/-- The proposition saying that `M` is minimal for this preorder-/
def isMinimal (M : AccessableDFA α σ₁) : Prop :=
    ∀ {σ : Type*} (N : AccessableDFA α σ), (M.accepts = N.accepts) → M ≤ N

end DFA

end PartialOrder

/-!
# Minimization
We implement a minimization algorithm to take any Accessable DFA to it's
nerode automaton (which is minimal by the partial order).

The states of the nerode automaton is the set of Left quotients of the language.
Question: How do we computably represent this set of languages?
Idea : Represent a language by a DFA that recognizes it.
IDea : Use other Mathlib PRs to represent it with a REGEX
Idea : Use the EQ classes of the states of the original DFA under myhil congruence
-/

/-!
## Nerode Equivalence
Question: Should this be defined on Accessable DFA?
-/

section NerodeEquivalence

namespace DFA

universe v u

variable {α : Type u} {σ : Type v}

/-- The Nerode equivalence relation on the states of a DFA.
For states `s₁, s₂`, we say `NerodeEquiv s₁ s₂` when the set of accepting words
from that state are equal. -/
def NerodeEquiv (M : DFA α σ) (s₁ s₂ : σ) : Prop :=
  ∀ w : List α, M.evalFrom s₁ w ∈ M.accept ↔ M.evalFrom s₂ w ∈ M.accept

theorem NerodeEquiv.refl (M : DFA α σ) (s : σ) : NerodeEquiv M s s := by
  intro w; rfl

theorem NerodeEquiv.symm (M : DFA α σ) {s₁ s₂ : σ} (h : NerodeEquiv M s₁ s₂) : NerodeEquiv M s₂ s₁ := by
  intro w; rw [h w]

theorem NerodeEquiv.trans (M : DFA α σ) {s₁ s₂ s₃ : σ}
    (h₁ : NerodeEquiv M s₁ s₂) (h₂ : NerodeEquiv M s₂ s₃) : NerodeEquiv M s₁ s₃ := by
  intro w; rw [h₁ w, h₂ w]

instance SetoidNerode (M : DFA α σ) : Setoid σ where
  r := NerodeEquiv M
  iseqv := ⟨NerodeEquiv.refl M, NerodeEquiv.symm M, NerodeEquiv.trans M⟩

/-- Question: How do i define this? -/
def NerodeEquivBool [Fintype α] [Fintype σ] (M : DFA α σ) (s₁ s₂ : σ) : Bool := sorry

lemma NerodeEquivBool_correct [Fintype α] [Fintype σ] (M : DFA α σ) (s₁ s₂ : σ) :
    NerodeEquiv M s₁ s₂ ↔ NerodeEquivBool M s₁ s₂ := by sorry

instance NerodeEquivDecidable (M : DFA α σ) [Fintype σ] [Fintype α] : DecidableRel (NerodeEquiv M) := by
  intros s₁ s₂
  rcases h : (NerodeEquivBool M s₁ s₂)
  · apply isFalse
    rw [NerodeEquivBool_correct]
    exact ne_true_of_eq_false h
  · apply isTrue
    rw [NerodeEquivBool_correct]
    exact h

def NerodeStates (M : DFA α σ) := Quotient (SetoidNerode M)

instance FintypeNerodeStates (M : DFA α σ) [Fintype α] [inst : Fintype σ] : Fintype (NerodeStates M) := by
  apply @Quotient.fintype σ inst (SetoidNerode M) (NerodeEquivDecidable M)


end DFA

end NerodeEquivalence

section Minimization

namespace DFA

variable {α σ : Type*}

#check Language.leftQuotient
#check Nonempty


/-- The states of the nerode automaton is the set of Left quotients of the language -/
def MinimizeStates (M : AccessableDFA α σ) := {L : Language α // ∃ w : List α, L = M.accepts.leftQuotient w}

def Minimize (M : AccessableDFA α σ) : AccessableDFA α (MinimizeStates M) where
  step s a := by -- inputs language s, outputs the left quotient of S with [a]
    refine ⟨s.val.leftQuotient [a], ?_⟩
    obtain ⟨y, hy⟩ := s.prop
    exists y ++ [a]
    rw [hy]
    rw [Language.leftQuotient_append]
  start := ⟨M.accepts, by use []; simp⟩
  accept := {s | [] ∈ s.val}
  isAccessable s := by
    simp [isAccessableState]
    obtain ⟨y, hy⟩ := s.prop
    use y
    apply Subtype.eq
    rw [hy]
    simp_all [eval]
    induction y using List.reverseRecOn generalizing s with
    | nil => simp
    | append_singleton w a ih =>
      have h₁ : M.accepts.leftQuotient w = M.accepts.leftQuotient w := by rfl
      have h := ih ⟨(M.accepts.leftQuotient w), by exists w⟩ (by rfl)
      simp_all
      exact Eq.symm (Language.leftQuotient_append M.accepts w [a])

def rightLang (M : AccessableDFA α σ) (s : σ) : Language α :=
  {w | M.evalFrom s w ∈ M.accept}

lemma rightLang_eq_leftQuotient (M : AccessableDFA α σ) {s : σ} {y : List α}
    (hy : M.eval y = s) :
    rightLang M s = M.accepts.leftQuotient y := by
  -- membership: w ∈ rightLang s  ↔  M.evalFrom s w ∈ accept
  -- left quotient: w ∈ L / y     ↔  w ++ y ∈ L
  ext w; simp_all [rightLang]
  rw [← hy]
  simp [mem_accepts, eval, evalFrom_of_append]
  rfl

def minimize_DFAHom (M : AccessableDFA α σ) : M.toDFA →ₗ (Minimize M).toDFA where
  toFun s := ⟨rightLang M s, by
    obtain ⟨y, hy⟩ := M.isAccessable s
    use y
    apply rightLang_eq_leftQuotient
    exact hy⟩
  map_start := by rfl
  map_accept := by
    intros s
    simp_all [Minimize, rightLang]
    rfl
  map_step := by
    intros s w
    simp_all [rightLang, Minimize]
    apply Subtype.eq
    ext y
    constructor
    · intros h
      have h₂ : M.evalFrom (M.evalFrom s w) y ∈ M.accept := h
      clear h





/- ERROR Tactic `cases` failed with a nested error:
Tactic `induction` failed: recursor `Exists.casesOn` can only eliminate into `Prop`-/


/--/
theorem minimize_le (M : AccessableDFA α σ) : Minimize M ≤ M := by
  apply Nonempty.intro
  exact AccessableDFAHomSurj.mk
    (toDFAHom := by apply DFAHom.mk (fun s ↦ getState s)




    )

    (surjective := by sorry )

    /--/
      (map_start := sorry)
      (map_accept := sorry)
      (map_step := sorry))
    (surjective := by sorry)

noncomputable def minimize_hom (M : AccessableDFA α σ) : M ↠ (Minimize M) where
  toFun s := by
    obtain h  := M.isAccessable s
    simp [isAccessableState] at h
    obtain ⟨y, hy⟩ := h
    exact ⟨M.accepts.leftQuotient (Classical.choose h), by simp⟩
  map_start := by
    simp_all [Minimize]
    apply Subtype.eq
    simp_all
    ext w
    constructor
    · intro h
      simp_all [Classical.choose_spec, mem_accepts, eval, evalFrom_of_append]


















theorem minimize_correct (M : AccessableDFA α σ) : isMinimal (Minimize M) := by
  simp_all [isMinimal, Minimize]


end DFA

end Minimization
