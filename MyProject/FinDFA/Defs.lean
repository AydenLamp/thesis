import Mathlib

/-!
# FinDFA : Computable deterministic finite automata

This file defines a structure that is equivalent to `Mathlib.Computability.DFA`,
except that the accept states are given as a `Finset` instead of a `Set`, and
we require `Fintype` and `DecidableEq` instances on the alphabet and state space.

We also define `evalFrom` and `acceptsFrom` functions analagously to their DFA versions.

We also define some `FinDFA`-specific functions for working with `Finset`s  of words and letters.

## Main Definitions

* `FinDFA α σ` : A DFA with alphabet `α` and state space `σ`,
both finite and with decidable equality.
* `M.evalFrom s w` : The state reached from reading the word `w : list α`
starting from state `s : σ` for a FinDFA `M`.
* `M.acceptsFrom s` : The language accepted by `M` starting from state `s : σ`.
* `M.toDFA` : The equivalent `Mathlib.Computability.DFA` to the `FinDFA` `M`.
* `M.getWordsLeqLength n` : The `Finset` of all words of length ≤ `n` in the alphabet of `M`.
* `M.isAccessableState` : A predicate for whether a state is accessable from the start state.
* `M.isAccessableStates_decidable` : A decidable procedure for `M.isAccessableState s`.

## Main Theorems

* `M.accepts_toDFA` : The language accepted by `M`
is the same as that accepted by `M.toDFA`.
* `M.getWordsLeqLength_correct` : Characterization of `M.getWordsLeqLength n`.
* `M.getAccessableStates_correct` : Characterization of `M.getAccessableStates`.
-/

universe u v

/-- A *finite and computable* DFA -/
structure FinDFA (α : Type u) (σ : Type v)
  [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ] where
  /-- Transition function. -/
  step  : σ → α → σ
  /-- Start state. -/
  start : σ
  /-- Accepting states as a `Finset`. -/
  accept : Finset σ


namespace FinDFA

variable {α : Type u} [instα : Fintype α]
variable [DecidableEq α]
variable {σ : Type v} [instσ : Fintype σ] [DecidableEq σ]

set_option linter.unusedSectionVars false

/-- Evaluate from a given state. Mirrors `DFA.evalFrom`. -/
def evalFrom (M : FinDFA α σ) (s : σ) : List α → σ :=
  List.foldl M.step s

@[simp] lemma evalFrom_nil (M : FinDFA α σ) (s : σ) : M.evalFrom s [] = s := rfl

@[simp] lemma evalFrom_singleton (M : FinDFA α σ) (s : σ) (a : α) :
    M.evalFrom s [a] = M.step s a := rfl

@[simp] lemma evalFrom_append_singleton (M : FinDFA α σ)
    (s : σ) (x : List α) (a : α) :
    M.evalFrom s (x ++ [a]) = M.step (M.evalFrom s x) a := by
  simp [evalFrom, List.foldl_append]

/-- Evaluate from the start state. Mirrors `DFA.eval`. -/
def eval (M : FinDFA α σ) : List α → σ := M.evalFrom M.start

@[simp] lemma eval_nil (M : FinDFA α σ) : M.eval [] = M.start := rfl

@[simp] lemma eval_singleton (M : FinDFA α σ) (a : α) :
    M.eval [a] = M.step M.start a := rfl

@[simp] lemma eval_append_singleton (M : FinDFA α σ) (x : List α) (a : α) :
    M.eval (x ++ [a]) = M.step (M.eval x) a := by
  simp [eval]

/-- `M.acceptsFrom s` as a language over `α`. -/
def acceptsFrom (M : FinDFA α σ) (s : σ) : Language α :=
  {x | M.evalFrom s x ∈ M.accept}

@[simp] lemma mem_acceptsFrom (M : FinDFA α σ) {s : σ} {x : List α} :
    x ∈ M.acceptsFrom s ↔ M.evalFrom s x ∈ M.accept := Iff.rfl

/-- `M.accepts` is the language accepted from the start state. -/
def accepts (M : FinDFA α σ) : Language α := M.acceptsFrom M.start

@[simp] lemma mem_accepts (M : FinDFA α σ) {x : List α} :
    x ∈ M.accepts ↔ M.eval x ∈ (M.accept) := Iff.rfl

/-!
### Conversions to mathlib's `DFA`
If you want to reuse theorems from `Mathlib/Computability/DFA`,
it’s convenient to convert our `FinDFA` into a standard `DFA` by
coercing the `Finset` of accepts to a `Set` of accepts.
-/

def toDFA (M : FinDFA α σ) : DFA α σ where
  step   := M.step
  start  := M.start
  accept := (M.accept : Set σ)

@[simp] lemma accepts_toDFA (M : FinDFA α σ) :
    (M.toDFA.accepts : Language α) = M.accepts := by
  ext x; rfl

/-- Bridge lemma: evaluating as a `DFA` agrees definitionally with `FinDFA`. -/
@[simp] lemma toDFA_evalFrom (M : FinDFA α σ) (s : σ) (x : List α) :
    M.toDFA.evalFrom s x = M.evalFrom s x := rfl

/-- Bridge lemma: evaluating as a `DFA` agrees definitionally with `FinDFA`. -/
@[simp] lemma toDFA_eval (M : FinDFA α σ) (x : List α) :
    M.toDFA.eval x = M.eval x := rfl

/-!
### FinDFA-specific functions
These are useful for working with `Finset`s of words and letters, and are used later
to obtain the decidability instance for the `Nerode` equivalence.
-/

set_option linter.unusedVariables false

/- Returns a Finset of all letters in the language of `M` -/
@[simp] def getLetters (M : FinDFA α σ) : Finset (α) := Finset.univ

@[simp] lemma getLetters_correct (M : FinDFA α σ) (a : α) : a ∈ M.getLetters := by
  simp

/-- Inputs a word `w` and returns an injection from letters `a` to `a :: w` -/
def prependLetter (M : FinDFA α σ) (w : List α) : α ↪ List α where
  toFun (a : α) := a :: w
  inj' := by simp_all [Function.Injective]

/- Inputs a word `w` and returns the finset of `a :: w` for `a : α` -/
def getNextWords (M : FinDFA α σ) (w : List α) : Finset (List α) :=
  Finset.map (M.prependLetter w) (M.getLetters)

@[simp] lemma getNextWords_correct (M : FinDFA α σ) (w : List α) (a : α) :
    a :: w ∈ M.getNextWords w := by
  simp_all [getNextWords, prependLetter]

/- Returns all the words of length `n` in the alphabet of `M` -/
def getWordsOfLength (M : FinDFA α σ) (n : ℕ) : Finset (List α) :=
  match n with
  | 0 => {[]}
  | n + 1 => Finset.biUnion (M.getWordsOfLength n) M.getNextWords

lemma getWordsOfLength_correct (M : FinDFA α σ) (n : ℕ) (w : List α) :
    w ∈ M.getWordsOfLength (n) ↔ w.length = n := by
  constructor
  · intros h
    induction n generalizing w with
    | zero => simp_all [getWordsOfLength]
    | succ n ih =>
      simp_all [getWordsOfLength]
      obtain ⟨v, ⟨hv₁, hv₂⟩⟩ := h
      simp_all [getNextWords, prependLetter]
      have hvlen := ih v hv₁
      obtain ⟨v, hv⟩ := hv₂
      subst w
      subst n
      simp
  · intros h
    induction w generalizing n with
    | nil =>
      simp_all
      subst n
      unfold getWordsOfLength
      simp
    | cons w ws ih =>
      simp_all
      unfold getWordsOfLength
      subst n
      simp_all
      use ws
      simp_all

/-- Returns a `Finset` of all words of length ≤ `n` -/
def getWordsLeqLength (M : FinDFA α σ) (n : ℕ) : Finset (List α) :=
  match n with
  | 0 => M.getWordsOfLength 0
  | n + 1 => (M.getWordsOfLength (n+1)) ∪ M.getWordsLeqLength n

lemma getWordsLeqLength_correct (M : FinDFA α σ) {n : ℕ} {w : List α} :
    w ∈ M.getWordsLeqLength n ↔ w.length ≤ n := by
  constructor
  · intro hin
    induction n generalizing w with
    |zero =>
      unfold getWordsLeqLength at hin
      unfold getWordsOfLength at hin
      simp_all
    | succ m ih =>
      unfold getWordsLeqLength at hin
      simp_all
      rcases hin with (hin | hin)
      · rw [getWordsOfLength_correct] at hin
        simp_all
      · apply ih at hin
        exact Nat.le_add_right_of_le hin
  · intro hlen
    induction n generalizing w with
    | zero =>
      simp_all [getWordsLeqLength, getWordsOfLength]
    | succ n ih =>
      simp_all [getWordsLeqLength]
      have hn : w.length = n + 1 ∨ w.length ≤ n := by exact Nat.le_succ_iff_eq_or_le.mp hlen
      rcases hn with (hn | hn)
      · left
        rw [getWordsOfLength_correct M (n + 1) w]
        exact hn
      · right
        apply ih
        exact hn

abbrev isAccessableState (M : FinDFA α σ) (s : σ) : Prop :=
  ∃ w, M.evalFrom M.start w = s

/-- The set of all accessable states -/
def getAccessableStates (M : FinDFA α σ) : Finset σ :=
  Finset.biUnion (M.getWordsLeqLength (Fintype.card σ)) (fun s ↦ {M.evalFrom M.start s})

/-- A `FinDFA` version of `DFA.evalFrom_split`, reused via `M.toDFA`. -/
lemma evalFrom_split (M : FinDFA α σ) {w : List α} {s t : σ}
    (hlen : Fintype.card σ ≤ w.length) (hx : M.evalFrom s w = t) :
    ∃ q a b c,
      w = a ++ b ++ c ∧
        a.length + b.length ≤ Fintype.card σ ∧
          b ≠ [] ∧ M.evalFrom s a = q ∧ M.evalFrom q b = q ∧ M.evalFrom q c = t := by
  simpa using
    (DFA.evalFrom_split (M := M.toDFA) (x := w) (s := s) (t := t)
      hlen (by simpa using hx))

/-- If a state `s` is reachable, then it is reachable by some word of length ≤ |σ|. -/
lemma exists_short_access_word (M : FinDFA α σ) (s : σ) {w : List α}
    (hw : M.evalFrom M.start w = s) :
    ∃ v : List α, v.length ≤ Fintype.card σ ∧ M.evalFrom M.start v = s := by
  -- strong recursion on the length of `w`
  refine (Nat.strongRecOn (motive := fun n => ∀ w : List α, w.length = n →
    M.evalFrom M.start w = s → ∃ v, v.length ≤ Fintype.card σ ∧ M.evalFrom M.start v = s)
    w.length ?_ w rfl hw)
  intro n ih w hlen hw'
  by_cases hshort : n ≤ Fintype.card σ
  · subst hlen; exact ⟨w, by simpa using hshort, hw'⟩
  · have hlt : Fintype.card σ < n := Nat.not_le.mp hshort
    have hle : Fintype.card σ ≤ n := le_of_lt hlt
    -- split `w = a ++ b ++ c` with a nonempty loop on `b`
    rcases M.evalFrom_split (w := w) (s := M.start) (t := s)
        (hlen := by simpa [hlen] using hle) (hx := hw') with
      ⟨q, a, b, c, hsplit, _hbnd, hbne, hqa, _hqb, hqc⟩
    -- consider `w' = a ++ c`
    let w' := a ++ c
    have hw'_eval : M.evalFrom M.start w' = s := by
      have : M.evalFrom M.start (a ++ c) = M.evalFrom (M.evalFrom M.start a) c := by
        simpa using
          (DFA.evalFrom_of_append (M := M.toDFA) (start := M.start) (x := a) (y := c))
      aesop
    have hlen_w : w.length = a.length + b.length + c.length := by
      simpa [List.length_append, add_assoc] using congrArg List.length hsplit
    have hlt' : w'.length < n := by
      have hbpos : 0 < b.length := List.length_pos_of_ne_nil hbne
      have hstep : a.length + c.length < a.length + c.length + b.length := by
        aesop
      have : w'.length < a.length + b.length + c.length := by
        aesop
      have hn' : n = a.length + b.length + c.length := by simpa [hlen] using hlen_w
      simpa [hn']
    obtain ⟨v, hvlen, hveq⟩ := ih w'.length hlt' w' rfl hw'_eval
    exact ⟨v, hvlen, hveq⟩

/-- Reachability iff reachability by a short word (length ≤ |σ|). -/
lemma reachable_iff_reachable_short (M : FinDFA α σ) (s : σ) :
    (∃ w, M.evalFrom M.start w = s) ↔ ∃ v, v.length ≤ Fintype.card σ ∧ M.evalFrom M.start v = s := by
  constructor
  · rintro ⟨w, hw⟩; exact M.exists_short_access_word s hw
  · rintro ⟨v, _, hv⟩; exact ⟨v, hv⟩

/-- Characterization of the `Finset` of accessable states. -/
theorem getAccessableStates_correct (M : FinDFA α σ) (s : σ) :
   M.isAccessableState s ↔ s ∈ M.getAccessableStates := by
  simp [isAccessableState, getAccessableStates]
  constructor
  · rintro ⟨w, hw⟩
    -- use a short witness and then the words≤|σ| characterization
    obtain ⟨v, hvlen, hveq⟩ := M.exists_short_access_word s hw
    exact ⟨v, (M.getWordsLeqLength_correct (n := Fintype.card σ) (w := v)).2 hvlen, hveq.symm⟩
  · rintro ⟨w, ⟨hw₁, hw₂⟩⟩
    exact ⟨w, hw₂.symm⟩

/-- Decidability of whether a state is accessable -/
instance isAccessableStateDecidable (M : FinDFA α σ) (s : σ) :
    Decidable (M.isAccessableState s) := by
  have h := M.getAccessableStates_correct s
  rw [h]
  infer_instance

instance (M : FinDFA α σ) : Fintype {s // M.isAccessableState s} := by infer_instance
instance (M : FinDFA α σ) : DecidableEq {s // M.isAccessableState s} := by infer_instance

end FinDFA
