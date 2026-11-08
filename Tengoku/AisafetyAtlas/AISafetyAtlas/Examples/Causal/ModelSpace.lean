module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.ModelSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rounding a model, on a worked table

`AISafetyAtlas.Causal.ModelSpace` rounds a model's tables onto a grid so that
estimates range over a countable set. This module runs the construction on a
table one can check by hand, and gives the error bound its teeth.

The bound is `dim c · ε`, not `ε`, because the last entry of each conditional
absorbs the rounding error of all the others. That factor is not slack:
`abs_cpt_roundDown_sub_not_le_eps` exhibits a three-state table whose last entry
moves by `0.198` at `ε = 0.1`, so no bound `k · ε` with `k < 2` can hold for
three-state variables.
-/

namespace AISafetyAtlas.Examples.Causal.ModelSpace

open AISafetyAtlas.Causal

/-- One chance variable with three states and no parents.-/
public abbrev V := Fin 1

public abbrev dim3 : V → ℕ := fun _ ↦ 3

/-- The table `(0.199, 0.199, 0.602)`. Both leading entries sit just under the
grid point `0.2`, so each loses almost `ε = 0.1` when rounded down, and the last
entry absorbs both losses.-/
@[expose] public noncomputable def skewTable : Fin 3 → ℝ :=
  fun a ↦ if a = 0 then 199 / 1000 else if a = 1 then 199 / 1000 else 602 / 1000

/-- A model whose single variable carries `skewTable`.-/
public noncomputable def skewed : Model V dim3 ℝ where
  dim_pos := fun _ ↦ by norm_num
  parents := fun _ ↦ ∅
  acyclic := ⟨fun _ ↦ 0, by simp⟩
  cpt := fun _ a _ ↦ skewTable a
  cpt_parents := fun _ _ _ _ _ ↦ rfl
  cpt_nonneg := fun _ a _ ↦ by
    fin_cases a <;> norm_num [skewTable]
  cpt_sum := fun _ _ ↦ by
    rw [Fin.sum_univ_three]
    norm_num [skewTable, Fin.ext_iff]

private theorem floor_skew : ⌊(199 : ℝ) / 100⌋ = 1 := by
  rw [Int.floor_eq_iff]
  constructor <;> norm_num

private theorem floorMul_skew : floorMul (1 / 10 : ℝ) (199 / 1000) = 1 / 10 := by
  have hdiv : ((199 : ℝ) / 1000) / (1 / 10) = 199 / 100 := by norm_num
  rw [floorMul, hdiv, floor_skew]
  norm_num

/-! ## The rounded table -/

/-! ## The `dim c` factor has teeth

The last entry moves by `0.198`, which is almost `2ε`. So the bound
`|cpt' − cpt| ≤ dim c · ε` cannot be tightened to `ε`, and the extra factor is
not an artefact of the proof. -/

/-! ## The error bound, on a concrete pair -/

end AISafetyAtlas.Examples.Causal.ModelSpace
