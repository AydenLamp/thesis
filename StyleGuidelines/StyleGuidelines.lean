import Mathlib

/-!
# Style Guidelines

This file is an assembly of the most relevant content in these documents:
* Lean Community website: <https://leanprover-community.github.io/index.html>
* Library Style Guidlines: <https://leanprover-community.github.io/contribute/style.html>

### Line Length
Lines must not be longer than 100 characters.

### Hypotheses Left of Colon

Generally, having arguments to the left of the colon is preferred over having arguments in
universal quantifiers or implications, if the proof starts by introducing these variables.
For instance:
-/

example (n : ℝ) (h : 1 < n) : 0 < n := by linarith

/-! is preferred over -/

example (n : ℝ) : 1 < n → 0 < n := fun h ↦ by linarith

/-
### Multiple Tactics on One Line

For single line tactic proofs (or short tactic proofs embedded in a term), it is acceptable to use
`by tac1; tac2; tac3` with semicolons instead of a new line with indentation.

In general, you should put a single tactic invocation per line, unless you are closing a goal with
a proof that fits entirely on a single line. Short sequences of tactics that correspond to a single
mathematical idea can also be put on a single line, separated by semicolons as in
`cases bla; clear h` or `induction n; simp` or `rw [foo]; simp_rw [bar]`, but even in these
scenarios, newlines are preferred.

### Whitespace and Delimiters

Lean is whitespace-sensitive, and in general we opt for a style which avoids delimiting code.
For instance, when writing tactics, it is possible to write them as `tac1; tac2; tac3`,
separated by `;`, in order to override the default whitespace sensitivity. However, as mentioned
above, we generally try to avoid this except in a few special cases.

Similarly, sometimes parentheses can be avoided by judicious use of the `<|` operator (or its
cousin `|>`). Note: while `$` is a synonym for `<|`, its use in mathlib is disallowed in favor of
`<|` for consistency as well as because of the symmetry with `|>`. These operators have the effect
of parenthesizing everything to the right of `<|` (note that `(` is curved the same direction as `<`)
or to the left of `|>` (and `)` curves the same way as `>`).

A common example of the usage of `|>` occurs with dot notation when the term preceding the `.` is a
function applied to some arguments. For instance, `((foo a).bar b).baz` can be rewritten as
`foo a |>.bar b |>.baz`

A common example of the usage of `<|` occurs with dot notation when the term preceding the `.`
is a function applied to multiple arguments whose last argument is a proof in tactic mode,
especially one that spans multiple lines. In that case, it is natural to use `<| by ...` instead
of `(by ...)`, as in: -/

example {x y : ℝ} (hxy : x ≤ y) (h : ∀ ε > 0, y - ε ≤ x) : x = y :=
  le_antisymm hxy <| le_of_forall_pos_le_add <| by
    intro ε hε
    have := h ε hε
    linarith

/-
### `simp` and `rw` Syntax

When using the tactics `rw` or `simp` there should be a space after the left arrow `←`.
For instance `rw [← add_comm a b]` or `simp [← and_or_left]`. (There should also be a space
between the tactic name and its arguments, as in `rw [h]`.)

#### Squeezing `simp` calls (with simp?)

Unless performance is particularly poor or the proof breaks otherwise, terminal `simp` calls (a
`simp` call is terminal if it closes the current goal or is only followed by flexible tactics such
as `ring`, `field_simp`, `aesop`) should not be squeezed (replaced by the output of `simp?`).
There are two main reasons for this:
1. A squeezed `simp` call might be several lines longer than the corresponding unsqueezed one,
   and therefore drown the useful information of what key lemmas were added to the unsqueezed
   `simp` call to close the goal in a sea of basic `simp` lemmas.
2. A squeezed `simp` call refers to many lemmas by name, meaning that it will break when one such
   lemma gets renamed. Lemma renamings happen often enough for this to matter on a maintenance level.

#### Normal forms

Some statements are equivalent. For instance, there are several equivalent ways to require that a
subset `s` of a type is nonempty. For another example, given `a : α`, the corresponding element of
`Option α` can be equivalently written as `Some a` or `(a : Option α)`. In general, we try to
settle on one standard form, called the normal form, and use it both in statements and conclusions
of theorems. In the above examples, this would be `s.Nonempty` (which gives access to dot notation)
and `(a : Option α)`. Often, `simp` lemmas will be registered to convert the other equivalent forms
to the normal form.

Iff theorems should be notated such that the more normalized version of the statement is on the right
side of the iff. This allows you to use them with `rw` and `simp` without prepending `←`. This also
is the way that `simp` will try to automatically apply the tactic if you tag it @[simp].
-/
