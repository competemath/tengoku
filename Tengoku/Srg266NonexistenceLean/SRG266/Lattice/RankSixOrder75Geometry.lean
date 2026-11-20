/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.RankSixComplements

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

def rankSixOrder75A4Root (i : Fin 4) : rankSixSpace .seventyFive :=
  (simplexSimpleRoot 4 i, 0)

theorem rankSixOrder75A4Root_mem (i : Fin 4) :
    rankSixOrder75A4Root i ∈ rankSixBase .seventyFive :=
  ⟨simplexSimpleRoot_mem 4 i, zero_mem _⟩

theorem rankSixOrder75A4Root_gram (i j : Fin 4) :
    rankSixForm .seventyFive (rankSixOrder75A4Root i) (rankSixOrder75A4Root j) =
      (gramA 4 i j : ℚ) := by
  simpa [rankSixOrder75A4Root, rankSixForm, A4Q15Coordinates.form, prodForm_apply]
    using simplexSimpleRoot_gram 4 i j

def rankSixOrder75Q15Inclusion : Q15Coordinates.Space →ₗ[ℚ] rankSixSpace .seventyFive :=
  LinearMap.inr ℚ (Fin 4 → ℚ) Q15Coordinates.Space

theorem rankSixOrder75Q15Inclusion_pair (x y : Q15Coordinates.Space) :
    rankSixForm .seventyFive (rankSixOrder75Q15Inclusion x) (rankSixOrder75Q15Inclusion y) =
      Q15Coordinates.form x y := by
  simp [rankSixOrder75Q15Inclusion, rankSixForm, A4Q15Coordinates.form, prodForm_apply]

theorem rankSixOrder75Q15Inclusion_mem (x : Q15Coordinates.Space)
    (hx : x ∈ Q15Coordinates.lattice) :
    rankSixOrder75Q15Inclusion x ∈ rankSixBase .seventyFive :=
  ⟨zero_mem _, hx⟩

def rankSixOrder75Q15Vector (i : Fin 2) : rankSixSpace .seventyFive :=
  rankSixOrder75Q15Inclusion (intCoordsToRat (Pi.single i 1))

theorem rankSixOrder75Q15Vector_mem (i : Fin 2) :
    rankSixOrder75Q15Vector i ∈ rankSixBase .seventyFive :=
  rankSixOrder75Q15Inclusion_mem _ (intCoordsToRat_mem _)

theorem rankSixOrder75Q15Vector_gram (i j : Fin 2) :
    rankSixForm .seventyFive (rankSixOrder75Q15Vector i) (rankSixOrder75Q15Vector j) =
      if i = j then 4 else 1 := by
  rw [rankSixOrder75Q15Vector, rankSixOrder75Q15Vector, rankSixOrder75Q15Inclusion_pair]
  fin_cases i <;> fin_cases j <;>
    norm_num [Q15Coordinates.form_apply, intCoordsToRat_apply, Pi.single_apply]

theorem rankSixOrder75_A4_Q15_orthogonal (i : Fin 4) (x : Q15Coordinates.Space) :
    rankSixForm .seventyFive (rankSixOrder75A4Root i) (rankSixOrder75Q15Inclusion x) = 0 := by
  simp [rankSixOrder75A4Root, rankSixOrder75Q15Inclusion, rankSixForm,
    A4Q15Coordinates.form, prodForm_apply]

end SRG266.Lattice
