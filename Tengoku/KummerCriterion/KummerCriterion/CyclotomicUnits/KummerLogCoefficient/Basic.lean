module

public import Tengoku.KummerCriterion.KummerCriterion.CyclotomicUnits.KummerLogFormal
public import Tengoku.KummerCriterion.KummerCriterion.CyclotomicUnits.Vandermonde
import Tengoku.Seed.Analysis.SpecialFunctions.Bernstein
import Tengoku.Seed.Tactic.NormNum.Irrational
import Tengoku.Seed.Tactic.NormNum.IsCoprime
import Tengoku.Seed.Tactic.NormNum.IsSquare
import Tengoku.Seed.Tactic.NormNum.LegendreSymbol
import Tengoku.Seed.Tactic.NormNum.ModEq
import Tengoku.Seed.Tactic.NormNum.NatFib
import Tengoku.Seed.Tactic.NormNum.NatLog
import Tengoku.Seed.Tactic.NormNum.NatSqrt
import Tengoku.Seed.Tactic.NormNum.Ordinal
import Tengoku.Seed.Tactic.NormNum.Parity
import Tengoku.Seed.Tactic.NormNum.Prime
import Tengoku.Seed.Tactic.NormNum.RealSqrt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kummer logarithm coefficient congruence

This file specializes the formal coefficient identity from `KummerLogFormal`
at the residue of the Kummer column. The specialization is still a formal
mod-`p` statement; the final bridge to concrete matrix entries is recorded
separately so it cannot be hidden behind a bundled hypothesis.
-/

@[expose] public section

noncomputable section

open NumberField
open NumberField.IsCMField
open scoped BigOperators NumberField

namespace KummerCriterion
namespace CyclotomicUnits

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable [NumberField.IsCMField K]
/-- Matrix row `j` corresponds to the mathematical index `j + 1`.-/
def kummerLogRowIndex (j : Fin (kummerLogRank p)) : ℕ :=
  (j : ℕ) + 1

omit [Fact p.Prime] in
/--
@isnad1 id=le.0h2v.s4.0b54a25ef00f from=translated src=- shape=161cbf40 vocab=cc6385ec
-/
theorem kummerLogRowIndex_one_le (j : Fin (kummerLogRank p)) :
    1 ≤ kummerLogRowIndex (p := p) j := by
  simp [kummerLogRowIndex]

omit [Fact p.Prime] in
/--
@isnad1 id=le.0h2v.s5.ffcca96882ed from=translated src=- shape=894aad4b vocab=db878e6e
-/
theorem two_mul_kummerLogRowIndex_le_sub_three
    (j : Fin (kummerLogRank p)) :
    2 * kummerLogRowIndex (p := p) j ≤ p - 3 := by
  have hjle : (j : ℕ) + 1 ≤ kummerLogRank p :=
    Nat.succ_le_of_lt j.isLt
  have hmulrank : 2 * kummerLogRank p ≤ p - 3 := by
    simpa [kummerLogRank, Nat.mul_comm] using
      Nat.div_mul_le_self (p - 3) 2
  have hle : 2 * ((j : ℕ) + 1) ≤ 2 * kummerLogRank p :=
    Nat.mul_le_mul_left 2 hjle
  simpa [kummerLogRowIndex] using hle.trans hmulrank

/-- The unit factor for the selected matrix row is nonzero modulo `p`.
@isnad1 id=ne.1h2v.s5.acfe7764bfff from=translated src=- shape=e413441d vocab=77ccb347
-/
theorem formalKummerLogCoeffModP_column_unit_ne_zero
    (_hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    kummerLogUnitFactor p (kummerLogRowIndex (p := p) j) ≠ 0 :=
  formalKummerLogCoeffModP_unit_ne_zero
    (p := p) (j := kummerLogRowIndex (p := p) j)
    (kummerLogRowIndex_one_le (p := p) j)
    (two_mul_kummerLogRowIndex_le_sub_three (p := p) j)

/-- specialization of the formal coefficient identity at the Kummer
column residue.
@isnad1 id=eq.2h3v.s8.f7f33b3c08bb from=translated src=- shape=ecc909c1 vocab=3013aa1a
-/
theorem formalKummerLogCoeffModP_eval_kummerLogColumnIndex
    (hp_three : 3 ≤ p) (_hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    Polynomial.eval (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
        (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j)) =
      (kummerLogUnitFactor p (kummerLogRowIndex (p := p) j) *
          bernoulliFactor p (kummerLogRowIndex (p := p) j)) *
        ((kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^
            (2 * kummerLogRowIndex (p := p) j) - 1) :=
  formalKummerLogCoeffModP_eval p (kummerLogRowIndex (p := p) j)
    (kummerLogColumnIndex (p := p) hp_three a : ZMod p)

/-- The right-hand side of Kummer's logarithm coefficient congruence for the
selected row and column.-/
def kummerLogCoeffCongrRhs
    (hp_three : 3 ≤ p) (j a : Fin (kummerLogRank p)) : ZMod p :=
  kummerLogUnitFactor p (kummerLogRowIndex (p := p) j) *
    bernoulliFactor p (kummerLogRowIndex (p := p) j) *
      ((kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^
        (2 * kummerLogRowIndex (p := p) j) - 1)

/-- Formal coefficient congruence after specializing the scalar at the Kummer
column residue, in the normalized-family coefficient convention.
@isnad1 id=eq.2h3v.s6.909e187060e6 from=translated src=- shape=a384bf08 vocab=27291818
-/
theorem formalKummerLogCoeff_congr
    (hp_three : 3 ≤ p) (hp_five : 5 ≤ p)
    (j a : Fin (kummerLogRank p)) :
    Polynomial.eval (kummerLogColumnIndex (p := p) hp_three a : ZMod p)
        (formalKummerLogCoeffModP p (kummerLogRowIndex (p := p) j)) =
      kummerLogCoeffCongrRhs (p := p) hp_three j a := by
  rw [formalKummerLogCoeffModP_eval_kummerLogColumnIndex
    (p := p) (hp_three := hp_three) (_hp_five := hp_five)]
  rfl

/-- The unit factor appearing in the row of the formal Kummer congruence is
nonzero.
@isnad1 id=ne.1h2v.s5.acfe7764bfff from=translated src=- shape=e413441d vocab=77ccb347
-/
theorem kummerLogCoeffCongrRhs_unit_ne_zero
    (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    kummerLogUnitFactor p (kummerLogRowIndex (p := p) j) ≠ 0 :=
  formalKummerLogCoeffModP_column_unit_ne_zero (p := p) hp_five j

/-- The squared-family unit factor. The normalized `C⁺` coefficient uses
`kummerLogUnitFactor`; the currently implemented concrete logarithm columns
come from the squared real cyclotomic-unit family, so their exact coefficient
has this extra factor `2`.-/
def squaredKummerLogUnitFactor (p j : ℕ) [Fact p.Prime] : ZMod p :=
  (2 : ZMod p) * kummerLogUnitFactor p j

/--
@isnad1 id=ne.1h1v.s6.97033146a4d3 from=translated src=- shape=2207af8f vocab=346366e3
-/
theorem two_zmod_ne_zero_of_five_le (hp_five : 5 ≤ p) :
    (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hp_dvd : p ∣ 2 :=
    (ZMod.natCast_eq_zero_iff 2 p).mp hzero
  have hp_le_two : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp_dvd
  omega

/-- The squared-family unit factor is nonzero in the Kummer row range.
@isnad1 id=ne.1h2v.s5.49116465acdd from=translated src=- shape=e413441d vocab=c42c8b5e
-/
theorem squaredKummerLogUnitFactor_ne_zero
    (hp_five : 5 ≤ p) (j : Fin (kummerLogRank p)) :
    squaredKummerLogUnitFactor p (kummerLogRowIndex (p := p) j) ≠ 0 :=
  mul_ne_zero
    (two_zmod_ne_zero_of_five_le (p := p) hp_five)
    (kummerLogCoeffCongrRhs_unit_ne_zero (p := p) hp_five j)

omit [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K] in
/-- The right-hand side for the currently implemented squared-family
logarithm columns.-/
def squaredKummerLogCoeffCongrRhs
    (hp_three : 3 ≤ p) (j a : Fin (kummerLogRank p)) : ZMod p :=
  squaredKummerLogUnitFactor p (kummerLogRowIndex (p := p) j) *
    bernoulliFactor p (kummerLogRowIndex (p := p) j) *
      ((kummerLogColumnIndex (p := p) hp_three a : ZMod p) ^
        (2 * kummerLogRowIndex (p := p) j) - 1)

/--
@isnad1 id=eq.1h3v.s6.e34b2bd55ea0 from=translated src=- shape=48639189 vocab=2601e84b
-/
theorem squaredKummerLogCoeffCongrRhs_eq_two_mul
    (hp_three : 3 ≤ p) (j a : Fin (kummerLogRank p)) :
    squaredKummerLogCoeffCongrRhs (p := p) hp_three j a =
      (2 : ZMod p) * kummerLogCoeffCongrRhs (p := p) hp_three j a := by
  simp [squaredKummerLogCoeffCongrRhs, squaredKummerLogUnitFactor,
    kummerLogCoeffCongrRhs]
  ring

end CyclotomicUnits
end KummerCriterion

end
