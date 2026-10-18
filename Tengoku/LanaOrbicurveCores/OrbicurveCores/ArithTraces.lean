/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.Fricke

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Traces in arithmetic subgroups of `SL(2, ℝ)`

A subgroup `Γ ⊆ SL(2, ℝ)` is *arithmetic* (in the non-cocompact sense) if some `GL(2, ℝ)`-conjugate
of it is commensurable with `SL(2, ℤ)`. We use Mathlib's `Subgroup.IsArithmetic` for subgroups of
`GL(2, ℝ)` (commensurable with the image `𝒮ℒ` of `SL(2, ℤ)`).

The non-cocompact arithmetic Fuchsian groups are exactly the groups commensurable (up to
conjugacy) with `SL(2, ℤ)`: the quaternion algebra of a non-cocompact arithmetic group is
`M₂(ℚ)`. So this is the notion of arithmeticity relevant for the `(1;∞)`-groups
([Take2]; [Corr], Def. 2.2–2.3).

## Main results

* `OrbicurveCores.mul_mem_rat_of_mem_commensurator`: every `g` in the commensurator of `SL(2, ℤ)`
  in `GL(2, ℝ)` is a real multiple of a rational matrix. Concretely, all products
  `(g⁻¹)ᵢₐ gᵦⱼ` are rational.
* `OrbicurveCores.tr_mul_tr_inv_mem_rat`: hence `tr g · tr g⁻¹ = (tr g)² / det g ∈ ℚ`.
* `OrbicurveCores.IsArithmeticSL.sq_tr_int`: if `Γ ⊆ SL(2, ℝ)` is arithmetic, then
  `(tr γ)² ∈ ℤ` for every `γ ∈ Γ`. It is rational by the above, and an algebraic integer because
  `γⁿ` is conjugate into `SL(2, ℤ)` for some `n ≥ 1` and `tr γⁿ = Vₙ(tr γ)`.
-/

open Matrix Matrix.SpecialLinearGroup Subgroup Polynomial
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups Pointwise

namespace OrbicurveCores

/-- The rational numbers inside `ℝ`, as a subfield. -/
noncomputable def ratSubfield : Subfield ℝ := (Rat.castHom ℝ).fieldRange

local notation "𝐐" => ratSubfield

lemma intCast_mem_rat (n : ℤ) : (n : ℝ) ∈ 𝐐 := ⟨n, by simp⟩

/-- The lower unipotent generator of `SL(2, ℤ)`. -/
def lowerL : SL(2, ℤ) := ⟨!![1, 0; 1, 1], by simp [det_fin_two]⟩

/-- A subgroup of `SL(2, ℝ)` is **arithmetic** (non-cocompact case) if some `GL(2, ℝ)`-conjugate
of its image in `GL(2, ℝ)` is commensurable with `SL(2, ℤ)`. -/
def IsArithmeticSL (Γ : Subgroup SL(2, ℝ)) : Prop :=
  ∃ g : GL (Fin 2) ℝ, (ConjAct.toConjAct g • Γ.map toGL).IsArithmetic

/-- If `x ∈ ℝ` is a root of `Vₙ - m` for some `n ≥ 1`, `m ∈ ℤ`, then `x` is an algebraic integer. -/
lemma isIntegral_of_lucas_eq {x : ℝ} {n : ℕ} (hn : 0 < n) {m : ℤ}
    (h : (lucas n).eval₂ (Int.castRingHom ℝ) x = m) : IsIntegral ℤ x := by
  refine ⟨lucas n - C m, ?_, ?_⟩
  · apply (lucas_monic hn).sub_of_left
    refine lt_of_le_of_lt degree_C_le ?_
    rw [degree_eq_natDegree (lucas_monic hn).ne_zero]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
    rw [zero_add, (lucas_monic_natDegree k).2]
    exact_mod_cast Nat.succ_pos k
  · rw [eval₂_sub, eval₂_C]
    rw [show algebraMap ℤ ℝ = Int.castRingHom ℝ from rfl, h]
    simp

end OrbicurveCores
