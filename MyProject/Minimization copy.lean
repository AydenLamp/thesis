import Mathlib

/- # Accessable DFAs
An Accessable state of a DFA is a state that can be reached from the start state by some word.
An Accessable DFA is a DFA where all states are accessable.
The first step of minimization is to convert a DFA to an accessable DFA.
-/

section Accessable

namespace DFA

universe v u

variable {α : Type u} {σ : Type v}

def isAccessableState (M : DFA α σ) (s : σ) : Prop := ∃ a : List α, M.eval a = s

structure AccessableDFA (α : Type u) (σ : Type v) extends toDFA : DFA α σ where
  toWord : σ → List α
  toWord_correct (s : σ) : toDFA.eval (toWord s) = s

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
  toWord := by sorry
  toWord_correct := by sorry

lemma toAccessable.eval (M : DFA α σ) (w : List α) : (M.toAccessable.eval w).val = M.eval w := by
  induction w using List.reverseRecOn with
  | nil => simp_all [toAccessable]
  | append_singleton w a ih =>
    simp_all [toAccessable]


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


def isMinimal (M : AccessableDFA α σ₁) : Prop := ∀ {σ : Type*} (N : AccessableDFA α σ), (M.accepts = N.accepts) → M ≤ N

end DFA

end PartialOrder

/-!
# Minimization
We implement a minimization algorithm to take any Accessable DFA to it's
nerode automaton (which is minimal by the partial order)
-/

section Minimization

namespace DFA

variable {α σ : Type*} [Fintype σ]

#check Language.leftQuotient
#check Nonempty

/-- The states of the nerode automaton is the set of Left quotients of the language -/
def MinimizeStates (M : AccessableDFA α σ) := {L : Language α // ∃ w : List α, L = M.accepts.leftQuotient w}

noncomputable def getWord {M : AccessableDFA α σ} (s : MinimizeStates M) : List α := by
  have h := s.prop
  exact Classical.choose h

lemma getWord_correct {M : AccessableDFA α σ} (s : MinimizeStates M) : s.val = M.accepts.leftQuotient (getWord s) := by
  sorry

def getState {M : AccessableDFA α σ} (s : MinimizeStates M) : σ := M.eval (M.toWord s)

def Minimize (M : AccessableDFA α σ) : AccessableDFA α (MinimizeStates M) where
  step s a := by -- inputs language s, outputs the left quotient of S with [a]
    refine ⟨s.val.leftQuotient [a], ?_⟩
    obtain ⟨y, hy⟩ := s.prop
    exists y ++ [a]
    rw [hy]
    rw [Language.leftQuotient_append]
  start := ⟨M.accepts, by use []; simp⟩
  accept := {s | [] ∈ s.val}
  toWord := sorry
  toWord_correct := sorry

def minimize_DFAHom (M : AccessableDFA α σ) : M.toDFA →ₗ (Minimize M).toDFA where
  toFun s := M.accepts.leftQuotient (M.toWord s)
  map_start := by sorry







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
