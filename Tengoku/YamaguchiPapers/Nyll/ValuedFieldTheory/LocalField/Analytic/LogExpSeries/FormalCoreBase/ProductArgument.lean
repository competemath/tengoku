/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.PowerSeriesComposition
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Data.Finset.Finsupp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The two-variable formal logarithm product argument

This module defines `X + Y + XY`, its logarithmic substitution, and the
support description needed for the formal product formula.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

namespace LocalFieldTheory.DiscreteValuationField
namespace MultiplicativeIntegerValuation

/-- The two-variable argument of the product formula:
`(1 + X) * (1 + Y) - 1 = X + Y + X*Y`.-/
def formalLogOnePlusProductArgument
    (A : Type*) [CommRing A] : MvPowerSeries (Fin 2) A :=
  MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2) +
    MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1 : Fin 2)

/-- The polynomial incarnation of the two-variable product argument
`(1 + X) * (1 + Y) - 1 = X + Y + XY`.-/
def formalLogOnePlusProductArgumentPolynomial
    (A : Type*) [CommSemiring A] : MvPolynomial (Fin 2) A :=
  MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) +
    MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)

/-- Evaluating the polynomial product argument at `(x,y)` gives
`x + y + xy`.-/
@[simp] theorem formalLogOnePlusProductArgumentPolynomial_eval_pair
    (A : Type*) [CommSemiring A] (x y : A) :
    MvPolynomial.eval (fun i : Fin 2 => if i = 0 then x else y)
        (formalLogOnePlusProductArgumentPolynomial A) =
      x + y + x * y := by
  simp [formalLogOnePlusProductArgumentPolynomial]

/--
Establishes the identity `formalLogOnePlusProductArgument A = (1 + MvPowerSeries.X (0 : Fin 2)) *
(1 + MvPowerSeries.X (1 : Fin 2)) - 1`.-/
theorem formalLogOnePlusProductArgument_eq_mul_sub_one
    (A : Type*) [CommRing A] :
    formalLogOnePlusProductArgument A =
      (1 + MvPowerSeries.X (0 : Fin 2)) *
          (1 + MvPowerSeries.X (1 : Fin 2)) - 1 := by
  let X0 : MvPowerSeries (Fin 2) A := MvPowerSeries.X (0 : Fin 2)
  let X1 : MvPowerSeries (Fin 2) A := MvPowerSeries.X (1 : Fin 2)
  change X0 + X1 + X0 * X1 = (1 + X0) * (1 + X1) - 1
  ring

/--
Establishes the identity `MvPowerSeries.constantCoeff (formalLogOnePlusProductArgument A) = 0`.-/
theorem formalLogOnePlusProductArgument_constantCoeff
    (A : Type*) [CommRing A] :
    MvPowerSeries.constantCoeff (formalLogOnePlusProductArgument A) = 0 := by
  rw [formalLogOnePlusProductArgument_eq_mul_sub_one]
  simp [MvPowerSeries.constantCoeff_X]

/--
The formal product argument has zero constant coefficient, so it admits substitution into the
logarithm power series.-/
theorem formalLogOnePlusProductArgument_hasSubst
    (A : Type*) [CommRing A] :
    PowerSeries.HasSubst (formalLogOnePlusProductArgument A) :=
  PowerSeries.HasSubst.of_constantCoeff_zero
    (formalLogOnePlusProductArgument_constantCoeff A)

/--
Establishes the identity `MvPowerSeries.coeff e (MvPowerSeries.X (0 : Fin 2) * MvPowerSeries.X (1
: Fin 2) : MvPowerSeries (Fin 2) A) = if e = Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 :
Fin 2) 1 then 1 else 0`.-/
theorem formalLogOnePlusProductArgument_mulVariables_coeff
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e
        (MvPowerSeries.X (0 : Fin 2) *
          MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) =
      if e =
          Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1
      then 1 else 0 := by
  change MvPowerSeries.coeff e
      (MvPowerSeries.monomial (Finsupp.single (0 : Fin 2) 1) (1 : A) *
        MvPowerSeries.monomial (Finsupp.single (1 : Fin 2) 1) (1 : A)) =
    if e =
        Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1
    then 1 else 0
  rw [MvPowerSeries.monomial_mul_monomial]
  simp [MvPowerSeries.coeff_monomial]

/--
Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductArgument A) = (if e =
Finsupp.single (0 : Fin 2) 1 then 1 else 0) + (if e = Finsupp.single (1 : Fin 2) 1 then 1 else 0)
+ (if e = Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 then 1 else 0)`.-/
theorem formalLogOnePlusProductArgument_coeff
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (formalLogOnePlusProductArgument A) =
      (if e = Finsupp.single (0 : Fin 2) 1 then 1 else 0) +
        (if e = Finsupp.single (1 : Fin 2) 1 then 1 else 0) +
          (if e =
              Finsupp.single (0 : Fin 2) 1 +
                Finsupp.single (1 : Fin 2) 1
            then 1 else 0) := by
  simp [formalLogOnePlusProductArgument, MvPowerSeries.coeff_X,
    formalLogOnePlusProductArgument_mulVariables_coeff]

/-- Establishes the identity `MvPowerSeries.coeff e (formalLogOnePlusProductArgument A) = 0`.-/
theorem formalLogOnePlusProductArgument_coeff_eq_zero_of_not_basic
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ)
    (hleft : e ≠ Finsupp.single (0 : Fin 2) 1)
    (hright : e ≠ Finsupp.single (1 : Fin 2) 1)
    (hmixed :
      e ≠
        Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1) :
    MvPowerSeries.coeff e (formalLogOnePlusProductArgument A) = 0 := by
  rw [formalLogOnePlusProductArgument_coeff]
  simp [hleft, hright, hmixed]

/-- Establishes the inequality `Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single (1 : Fin 2) 1`.-/
theorem finsupp_fin_two_single_left_ne_single_right :
    Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single (1 : Fin 2) 1 := by
  intro h
  have hcoord := congrArg (fun e : Fin 2 →₀ ℕ => e (0 : Fin 2)) h
  norm_num [Finsupp.single_apply, Finsupp.add_apply] at hcoord

/--
Establishes the inequality `Finsupp.single (0 : Fin 2) 1 ≠ Finsupp.single (0 : Fin 2) 1 +
Finsupp.single (1 : Fin 2) 1`.-/
theorem finsupp_fin_two_single_left_ne_mixed :
    Finsupp.single (0 : Fin 2) 1 ≠
      Finsupp.single (0 : Fin 2) 1 +
        Finsupp.single (1 : Fin 2) 1 := by
  intro h
  have hcoord := congrArg (fun e : Fin 2 →₀ ℕ => e (1 : Fin 2)) h
  norm_num [Finsupp.single_apply, Finsupp.add_apply] at hcoord

/--
Establishes the inequality `Finsupp.single (1 : Fin 2) 1 ≠ Finsupp.single (0 : Fin 2) 1 +
Finsupp.single (1 : Fin 2) 1`.-/
theorem finsupp_fin_two_single_right_ne_mixed :
    Finsupp.single (1 : Fin 2) 1 ≠
      Finsupp.single (0 : Fin 2) 1 +
        Finsupp.single (1 : Fin 2) 1 := by
  intro h
  have hcoord := congrArg (fun e : Fin 2 →₀ ℕ => e (0 : Fin 2)) h
  norm_num [Finsupp.single_apply, Finsupp.add_apply] at hcoord

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)
(formalLogOnePlusProductArgument A) = 1`.-/
@[simp] theorem formalLogOnePlusProductArgument_coeff_single_left
    (A : Type*) [CommRing A] :
    MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1)
        (formalLogOnePlusProductArgument A) = 1 := by
  rw [formalLogOnePlusProductArgument_coeff]
  simp [finsupp_fin_two_single_left_ne_single_right]

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)
(formalLogOnePlusProductArgument A) = 1`.-/
@[simp] theorem formalLogOnePlusProductArgument_coeff_single_right
    (A : Type*) [CommRing A] :
    MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)
        (formalLogOnePlusProductArgument A) = 1 := by
  rw [formalLogOnePlusProductArgument_coeff]
  have hrightLeft :
      Finsupp.single (1 : Fin 2) 1 ≠
        Finsupp.single (0 : Fin 2) 1 :=
    finsupp_fin_two_single_left_ne_single_right.symm
  simp [hrightLeft]

/--
Establishes the identity `MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 :
Fin 2) 1) (formalLogOnePlusProductArgument A) = 1`.-/
@[simp] theorem formalLogOnePlusProductArgument_coeff_mixed
    (A : Type*) [CommRing A] :
    MvPowerSeries.coeff
        (Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1)
        (formalLogOnePlusProductArgument A) = 1 := by
  rw [formalLogOnePlusProductArgument_coeff]
  have hmixedLeft :
      Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1 ≠
        Finsupp.single (0 : Fin 2) 1 :=
    finsupp_fin_two_single_left_ne_mixed.symm
  have hmixedRight :
      Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1 ≠
        Finsupp.single (1 : Fin 2) 1 :=
    finsupp_fin_two_single_right_ne_mixed.symm
  simp [hmixedLeft, hmixedRight]

/-- Proves the bound `e (0 : Fin 2) ≤ 1`.-/
theorem formalLogOnePlusProductArgument_coeff_ne_zero_left_coord_le_one
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ)
    (hcoeff : MvPowerSeries.coeff e
      (formalLogOnePlusProductArgument A) ≠ 0) :
    e (0 : Fin 2) ≤ 1 := by
  by_contra hle
  have hgt : 1 < e (0 : Fin 2) := Nat.lt_of_not_ge hle
  have hleft : e ≠ Finsupp.single (0 : Fin 2) 1 := by
    intro he
    have hcoord : e (0 : Fin 2) ≤ 1 := by simp [he]
    exact (not_le_of_gt hgt) hcoord
  have hright : e ≠ Finsupp.single (1 : Fin 2) 1 := by
    intro he
    have hcoord : e (0 : Fin 2) ≤ 1 := by simp [he]
    exact (not_le_of_gt hgt) hcoord
  have hmixed :
      e ≠
        Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1 := by
    intro he
    have hcoord : e (0 : Fin 2) ≤ 1 := by simp [he]
    exact (not_le_of_gt hgt) hcoord
  exact hcoeff
    (formalLogOnePlusProductArgument_coeff_eq_zero_of_not_basic
      A e hleft hright hmixed)

/-- Proves the bound `e (1 : Fin 2) ≤ 1`.-/
theorem formalLogOnePlusProductArgument_coeff_ne_zero_right_coord_le_one
    (A : Type*) [CommRing A] (e : Fin 2 →₀ ℕ)
    (hcoeff : MvPowerSeries.coeff e
      (formalLogOnePlusProductArgument A) ≠ 0) :
    e (1 : Fin 2) ≤ 1 := by
  by_contra hle
  have hgt : 1 < e (1 : Fin 2) := Nat.lt_of_not_ge hle
  have hleft : e ≠ Finsupp.single (0 : Fin 2) 1 := by
    intro he
    have hcoord : e (1 : Fin 2) ≤ 1 := by simp [he]
    exact (not_le_of_gt hgt) hcoord
  have hright : e ≠ Finsupp.single (1 : Fin 2) 1 := by
    intro he
    have hcoord : e (1 : Fin 2) ≤ 1 := by simp [he]
    exact (not_le_of_gt hgt) hcoord
  have hmixed :
      e ≠
        Finsupp.single (0 : Fin 2) 1 +
          Finsupp.single (1 : Fin 2) 1 := by
    intro he
    have hcoord : e (1 : Fin 2) ≤ 1 := by simp [he]
    exact (not_le_of_gt hgt) hcoord
  exact hcoeff
    (formalLogOnePlusProductArgument_coeff_eq_zero_of_not_basic
      A e hleft hright hmixed)

end MultiplicativeIntegerValuation
end LocalFieldTheory.DiscreteValuationField

end
