import MyProject.GreensRelations

/-!
# Duality lemmas for Green's relations

This file develops `MulOpposite` duality for Green’s preorders, equivalences,
and equivalence classes. It also defines a named simp set:

* `fromOpp` — lemmas oriented to pull statements **out of** `MulOpposite`.

Use it via `simp [fromOpp]`.

## Implementation Notes

Note that the `.op_iff` style lemmas rewrite the statement INTO the opposite semigroup.
Reverse implications, which rewrite the statement FROM the opposite semigroup,
are put into the `fromOpp` simp set.

When Proving a dual statement, use the `.op_iff` lemmas to convert the statement
to the opposite semigroup, then apply the lemma.
-/

/-! ### Raw `op` arithmetic helpers -/

open MulOpposite

variable {M : Type*} [Monoid M] (x y z u : M)

@[fromOpp ←] theorem mul_eq_op_iff : y * x = z ↔ op x * op y = op z := by simp [← op_mul]

@[fromOpp ←] theorem op_eq_mul_iff :  x = z * y ↔ op x = op y * op z := by simp [← op_mul]

@[fromOpp ←] theorem mul_mul_eq_op_iff : z * y * x = u ↔ op x * op y * op z = op u := by
  simp [← op_mul, ← mul_assoc]

@[fromOpp ←] theorem op_eq_mul_mul_iff : x = u * z * y ↔ op x = op y * op z * op u := by
  simp [← op_mul, ← mul_assoc]

/-! ### Relation Duality -/

@[fromOpp ←] lemma RRel.op_iff : x ≤𝓡 y ↔ op x ≤𝓛 op y := by
  simp [fromOpp, RRel, LRel]

@[fromOpp ←] lemma LRel.op_iff : x ≤𝓛 y ↔ op x ≤𝓡 op y := by
  simp [RRel, LRel, fromOpp]

@[fromOpp ←] lemma JRel.op_iff : x ≤𝓙 y ↔ op x ≤𝓙 op y := by
  simp [fromOpp, JRel]
  aesop

@[fromOpp ←] lemma HRel.op_iff : x ≤𝓗 y ↔ op x ≤𝓗 op y := by
  simp [HRel, fromOpp, and_comm]

/-! ### Equivalence Duality -/

@[fromOpp ←] lemma REquiv.op_iff : x 𝓡 y ↔ op x 𝓛 op y := by
  simp [LEquiv, REquiv, fromOpp]

@[fromOpp ←] lemma LEquiv.op_iff : x 𝓛 y ↔ op x 𝓡 op y := by
  simp [REquiv, LEquiv, fromOpp]

@[fromOpp ←] lemma JEquiv.op_iff : x 𝓙 y ↔ op x 𝓙 op y := by
  simp [JEquiv, fromOpp]

@[fromOpp ←] lemma HEquiv.op_iff : x 𝓗 y ↔ op x 𝓗 op y := by
  simp [HEquiv, fromOpp]

@[fromOpp ← ] lemma DEquiv.op_iff : x 𝓓 y ↔ op x 𝓓 op y := by
  constructor
  · intro hD
    symm
    simp_all [DEquiv, fromOpp, and_comm]
    obtain ⟨z, hL, hR⟩ := hD
    use z
    constructor
    · exact hL.symm
    · exact hR.symm
  · intro hD
    symm
    simp_all [DEquiv, fromOpp, and_comm]
    obtain ⟨z, hL, hR⟩ := hD
    use z
    constructor
    · exact hL.symm
    · exact hR.symm

/-! ## Duality for equivalence classes -/

@[fromOpp ←] theorem LClass.op_iff : x ∈ ⟦y⟧𝓛 ↔ op x ∈ ⟦op y⟧𝓡 := by
  simp [fromOpp]

@[fromOpp ←] theorem RClass.op_iff : x ∈ ⟦y⟧𝓡 ↔ op x ∈ ⟦op y⟧𝓛 := by
  simp [fromOpp]

@[fromOpp ←] theorem JClass.op_iff : x ∈ ⟦y⟧𝓙 ↔ op x ∈ ⟦op y⟧𝓙 := by
  simp [fromOpp]

@[fromOpp ←] theorem HClass.op_iff : x ∈ ⟦y⟧𝓗 ↔ op x ∈ ⟦op y⟧𝓗 := by
  simp [fromOpp]

@[fromOpp ←] theorem DClass.op_iff : x ∈ ⟦y⟧𝓓 ↔ op x ∈ ⟦op y⟧𝓓 := by
  simp [fromOpp]

/-!
### Examples of proving dual statments
We use the lemma `DEquiv.closed_under_rEquiv` to prove a dual statment.
-/

#check DEquiv.closed_under_rEquiv

example (hD : x 𝓓 y) (hL : y 𝓛 z) : x 𝓓 z := by
  rw [DEquiv.op_iff, LEquiv.op_iff] at *
  apply DEquiv.closed_under_rEquiv hD hL
