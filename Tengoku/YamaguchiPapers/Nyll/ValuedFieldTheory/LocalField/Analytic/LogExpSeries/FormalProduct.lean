/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.SetTheory.Cardinal.Finite
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCore

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Proves the formal combinatorial identities behind additivity of the logarithm on products of
principal units.
-/

open Filter
open Polynomial
open scoped Topology
open scoped PowerSeries.WithPiTopology
noncomputable section

attribute [local instance] Classical.propDecidable

universe u

open LocalFieldTheory.DiscreteValuationField

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

variable {K : Type u} [Field K]

/--
Establishes the identity `MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.-/
theorem formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_left_coord_lt
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hleft : q < e (0 : Fin 2)) :
    MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0 := by
  classical
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_eq_zero
  intro l hl
  rw [Finset.mem_finsuppAntidiag] at hl
  by_cases hprod :
      ∏ i ∈ Finset.range q,
        MvPowerSeries.coeff (l i) (formalLogOnePlusProductArgument A) = 0
  · exact hprod
  · exfalso
    have hfactor :
        ∀ i ∈ Finset.range q,
          MvPowerSeries.coeff (l i)
            (formalLogOnePlusProductArgument A) ≠ 0 := by
      intro i hi hzero
      exact hprod (Finset.prod_eq_zero hi hzero)
    have hcoord :
        (∑ i ∈ Finset.range q, l i (0 : Fin 2)) = e (0 : Fin 2) := by
      simpa [Finsupp.finsetSum_apply] using
        congrArg (fun m : Fin 2 →₀ ℕ => m (0 : Fin 2)) hl.1
    have hsum_le :
        (∑ i ∈ Finset.range q, l i (0 : Fin 2)) ≤
          ∑ _i ∈ Finset.range q, 1 := by
      exact Finset.sum_le_sum fun i hi =>
        formalLogOnePlusProductArgument_coeff_ne_zero_left_coord_le_one
          A (l i) (hfactor i hi)
    have hcoord_le : e (0 : Fin 2) ≤ q := by
      simpa [hcoord] using hsum_le
    exact (not_lt_of_ge hcoord_le) hleft

/--
Establishes the identity `MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.-/
theorem formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_right_coord_lt
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hright : q < e (1 : Fin 2)) :
    MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0 := by
  classical
  rw [MvPowerSeries.coeff_pow]
  apply Finset.sum_eq_zero
  intro l hl
  rw [Finset.mem_finsuppAntidiag] at hl
  by_cases hprod :
      ∏ i ∈ Finset.range q,
        MvPowerSeries.coeff (l i) (formalLogOnePlusProductArgument A) = 0
  · exact hprod
  · exfalso
    have hfactor :
        ∀ i ∈ Finset.range q,
          MvPowerSeries.coeff (l i)
            (formalLogOnePlusProductArgument A) ≠ 0 := by
      intro i hi hzero
      exact hprod (Finset.prod_eq_zero hi hzero)
    have hcoord :
        (∑ i ∈ Finset.range q, l i (1 : Fin 2)) = e (1 : Fin 2) := by
      simpa [Finsupp.finsetSum_apply] using
        congrArg (fun m : Fin 2 →₀ ℕ => m (1 : Fin 2)) hl.1
    have hsum_le :
        (∑ i ∈ Finset.range q, l i (1 : Fin 2)) ≤
          ∑ _i ∈ Finset.range q, 1 := by
      exact Finset.sum_le_sum fun i hi =>
        formalLogOnePlusProductArgument_coeff_ne_zero_right_coord_le_one
          A (l i) (hfactor i hi)
    have hcoord_le : e (1 : Fin 2) ≤ q := by
      simpa [hcoord] using hsum_le
    exact (not_lt_of_ge hcoord_le) hright

/--
Establishes the identity `MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.-/
theorem formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_degree_lt
    (A : Type*) [CommRing A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hdegree : Finsupp.degree e < q) :
    MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0 := by
  have hnil :
      MvPowerSeries.constantCoeff (formalLogOnePlusProductArgument A) ^ 1 =
        0 := by
    simp [formalLogOnePlusProductArgument_constantCoeff A]
  exact
    MvPowerSeries.coeff_eq_zero_of_constantCoeff_nilpotent
      (f := formalLogOnePlusProductArgument A) (m := 1) hnil
      (d := e) (n := q) (by
        have hs : Finsupp.degree e + 1 ≤ q :=
          Nat.succ_le_of_lt hdegree
        simpa [Nat.add_comm] using hs)

/--
Establishes the identity `PowerSeries.coeff q (PowerSeries.log A) •
MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_degree_lt
    (A : Type*) [CommRing A] [Algebra ℚ A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hdegree : Finsupp.degree e < q) :
    PowerSeries.coeff q (PowerSeries.log A) •
        MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
      0 := by
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_degree_lt
    A q e hdegree]
  exact smul_zero _

/--
Establishes the identity `PowerSeries.coeff q (PowerSeries.log A) •
MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_left_coord_lt
    (A : Type*) [CommRing A] [Algebra ℚ A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hleft : q < e (0 : Fin 2)) :
    PowerSeries.coeff q (PowerSeries.log A) •
        MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
      0 := by
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_left_coord_lt
    A q e hleft]
  exact smul_zero _

/--
Establishes the identity `PowerSeries.coeff q (PowerSeries.log A) •
MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) = 0`.-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_right_coord_lt
    (A : Type*) [CommRing A] [Algebra ℚ A] (q : ℕ) (e : Fin 2 →₀ ℕ)
    (hright : q < e (1 : Fin 2)) :
    PowerSeries.coeff q (PowerSeries.log A) •
        MvPowerSeries.coeff e ((formalLogOnePlusProductArgument A) ^ q) =
      0 := by
  rw [formalLogOnePlusProductArgument_pow_coeff_eq_zero_of_right_coord_lt
    A q e hright]
  exact smul_zero _

/-- Expands a coefficient of the logarithm substituted at the product
argument as a finite sum bounded by the total degree of the exponent.-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_eq_sum_range_degree_succ
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      ∑ q ∈ Finset.range (Finsupp.degree e + 1),
        PowerSeries.coeff q (PowerSeries.log A) •
          MvPowerSeries.coeff e
            ((formalLogOnePlusProductArgument A) ^ q) := by
  rw [PowerSeries.coeff_subst
    (formalLogOnePlusProductArgument_hasSubst A) (PowerSeries.log A) e]
  apply finsum_eq_sum_of_support_subset
  intro q hq
  by_contra hmem
  rw [Finset.mem_coe, Finset.mem_range] at hmem
  have hdegree : Finsupp.degree e < q := Nat.lt_of_succ_le
    (Nat.le_of_not_gt hmem)
  exact hq
    (formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_degree_lt
      A q e hdegree)

/-- Refines the coefficient expansion to powers at least as large as both
coordinates of the exponent.-/
theorem formalLogOnePlusProductArgument_logSubst_coeff_eq_sum_range_degree_succ_filter_coord_le
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
        (PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A)) =
      ∑ q ∈
        (Finset.range (Finsupp.degree e + 1)).filter
          (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
        PowerSeries.coeff q (PowerSeries.log A) •
          MvPowerSeries.coeff e
            ((formalLogOnePlusProductArgument A) ^ q) := by
  rw [formalLogOnePlusProductArgument_logSubst_coeff_eq_sum_range_degree_succ]
  exact
    (Finset.sum_subset (Finset.filter_subset _ _) (fun q hq hnot => by
      by_cases hleft : e (0 : Fin 2) ≤ q
      · by_cases hright : e (1 : Fin 2) ≤ q
        · exfalso
          exact hnot (by simpa [hleft, hright] using hq)
        · exact
            formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_right_coord_lt
              A q e (Nat.lt_of_not_ge hright)
      · exact
          formalLogOnePlusProductArgument_logSubst_coeff_term_eq_zero_of_left_coord_lt
            A q e (Nat.lt_of_not_ge hleft))).symm

/-- The formal logarithm `log(1 + X)`, viewed as a two-variable series in the
left variable.-/
noncomputable def formalLogOnePlusLeftVariableLogSubst
    (A : Type*) [CommRing A] [Algebra ℚ A] : MvPowerSeries (Fin 2) A :=
  PowerSeries.subst
    (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) A)
    (PowerSeries.log A)

/-- The formal logarithm `log(1 + Y)`, viewed as a two-variable series in the
right variable.-/
noncomputable def formalLogOnePlusRightVariableLogSubst
    (A : Type*) [CommRing A] [Algebra ℚ A] : MvPowerSeries (Fin 2) A :=
  PowerSeries.subst
    (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A)
    (PowerSeries.log A)

/-- The formal right-hand side `log(1 + X) + log(1 + Y)` of the logarithm
product formula.-/
noncomputable def formalLogOnePlusProductRightSide
    (A : Type*) [CommRing A] [Algebra ℚ A] : MvPowerSeries (Fin 2) A :=
  formalLogOnePlusLeftVariableLogSubst A +
    formalLogOnePlusRightVariableLogSubst A

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusLeftVariableLogSubst A) = 0`.-/
theorem formalLogOnePlusLeftVariableLogSubst_coeff_of_ne_axis
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (he : ∀ d : ℕ, e ≠ Finsupp.single (0 : Fin 2) d) :
    MvPowerSeries.coeff e (formalLogOnePlusLeftVariableLogSubst A) = 0 := by
  simp [formalLogOnePlusLeftVariableLogSubst, PowerSeries.coeff_subst_single, he]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusRightVariableLogSubst A) = 0`.-/
theorem formalLogOnePlusRightVariableLogSubst_coeff_of_ne_axis
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (he : ∀ d : ℕ, e ≠ Finsupp.single (1 : Fin 2) d) :
    MvPowerSeries.coeff e (formalLogOnePlusRightVariableLogSubst A) = 0 := by
  simp [formalLogOnePlusRightVariableLogSubst, PowerSeries.coeff_subst_single, he]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) =
MvPowerSeries.coeff e (formalLogOnePlusLeftVariableLogSubst A) + MvPowerSeries.coeff e
(formalLogOnePlusRightVariableLogSubst A)`.-/
theorem formalLogOnePlusProductRightSide_coeff
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) =
      MvPowerSeries.coeff e (formalLogOnePlusLeftVariableLogSubst A) +
        MvPowerSeries.coeff e (formalLogOnePlusRightVariableLogSubst A) := by
  simp [formalLogOnePlusProductRightSide]

/-- Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) = 0`.-/
theorem formalLogOnePlusProductRightSide_coeff_of_ne_axes
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (heLeft : ∀ d : ℕ, e ≠ Finsupp.single (0 : Fin 2) d)
    (heRight : ∀ d : ℕ, e ≠ Finsupp.single (1 : Fin 2) d) :
    MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) = 0 := by
  rw [formalLogOnePlusProductRightSide_coeff]
  simp [formalLogOnePlusLeftVariableLogSubst_coeff_of_ne_axis A e heLeft,
    formalLogOnePlusRightVariableLogSubst_coeff_of_ne_axis A e heRight]

/-- Establishes the inequality `e ≠ Finsupp.single (0 : Fin 2) d`.-/
theorem finsupp_fin_two_ne_single_left_of_right_pos
    (e : Fin 2 →₀ ℕ) (hpos : 0 < e (1 : Fin 2)) (d : ℕ) :
    e ≠ Finsupp.single (0 : Fin 2) d := by
  intro h
  have hcoord : e (1 : Fin 2) = 0 := by
    simp [h]
  exact (Nat.ne_of_gt hpos) hcoord

/-- Establishes the inequality `e ≠ Finsupp.single (1 : Fin 2) d`.-/
theorem finsupp_fin_two_ne_single_right_of_left_pos
    (e : Fin 2 →₀ ℕ) (hpos : 0 < e (0 : Fin 2)) (d : ℕ) :
    e ≠ Finsupp.single (1 : Fin 2) d := by
  intro h
  have hcoord : e (0 : Fin 2) = 0 := by
    simp [h]
  exact (Nat.ne_of_gt hpos) hcoord

/-- Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) = 0`.-/
theorem formalLogOnePlusProductRightSide_coeff_of_pos_coords
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (hleft : 0 < e (0 : Fin 2)) (hright : 0 < e (1 : Fin 2)) :
    MvPowerSeries.coeff e (formalLogOnePlusProductRightSide A) = 0 :=
  formalLogOnePlusProductRightSide_coeff_of_ne_axes A e
    (finsupp_fin_two_ne_single_left_of_right_pos e hright)
    (finsupp_fin_two_ne_single_right_of_left_pos e hleft)

/-- Difference between the two formal sides of the logarithm product formula.
The remaining proof of the formal identity is exactly the vanishing of this
series on mixed monomials.-/
noncomputable def formalLogOnePlusProductFormulaDefect
    (A : Type*) [CommRing A] [Algebra ℚ A] : MvPowerSeries (Fin 2) A :=
  PowerSeries.subst (formalLogOnePlusProductArgument A) (PowerSeries.log A) -
      formalLogOnePlusProductRightSide A

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductFormulaDefect A) = ∑ q ∈
(Finset.range (Finsupp.degree e + 1)).filter (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
PowerSeries.coeff q (PowerSeries.log A) • MvPowerSeries.coeff e
((formalLogOnePlusProductArgument A) ^ q)`.-/
theorem
  formalLogOnePlusProductFormulaDefect_coeff_of_pos_coords_eq_sum_range_degree_succ_filter_coord_le
    (A : Type*) [CommRing A] [Algebra ℚ A] (e : Fin 2 →₀ ℕ)
    (hleft : 0 < e (0 : Fin 2)) (hright : 0 < e (1 : Fin 2)) :
    MvPowerSeries.coeff e
        (formalLogOnePlusProductFormulaDefect A) =
      ∑ q ∈
        (Finset.range (Finsupp.degree e + 1)).filter
          (fun q : ℕ => e (0 : Fin 2) ≤ q ∧ e (1 : Fin 2) ≤ q),
        PowerSeries.coeff q (PowerSeries.log A) •
          MvPowerSeries.coeff e
            ((formalLogOnePlusProductArgument A) ^ q) := by
  simp [formalLogOnePlusProductFormulaDefect,
    formalLogOnePlusProductRightSide_coeff_of_pos_coords A e hleft hright,
    formalLogOnePlusProductArgument_logSubst_coeff_eq_sum_range_degree_succ_filter_coord_le]

/-- The value of the monomial indexed by a finitely supported exponent at a
chosen evaluation point.-/
noncomputable def mvPowerSeriesMonomialValue
    {σ : Type*} {A : Type*} [CommMonoid A]
    (a : σ → A) (d : σ →₀ ℕ) : A :=
  d.prod fun s e => a s ^ e

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
