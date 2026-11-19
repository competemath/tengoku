import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.Admissible
import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.AnalyticInterfaces
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace Square3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Theorem 14.1 after the character-sum estimate
-/

/-- The Section 14 numerical hypothesis forces more than nine power-good
parameters.
@isnad1 id=ex.5h3v.s7.8a2d24f52718 from=translated src=- shape=8a7ae866 vocab=6d297147
-/
theorem centerOne_power_parameters_card_gt_nine
    (n d : ℕ)
    (hd : 0 < d)
    (hodd : ringChar F ≠ 2)
    (hq : 7 < Fintype.card F)
    (hCount : HasCenterOnePowerCountBound F n d)
    (hmain :
      9 * (d : ℝ) ^ 8 <
        (Fintype.card F : ℝ) -
          centerOneC1 d * Real.sqrt (Fintype.card F : ℝ)) :
    ∃ b : F,
      CenterOneGoodB b ∧ 9 < (centerOnePowerParameters n b).card := by
  obtain ⟨b, hb⟩ := exists_centerOneGoodB (F := F) hodd hq
  have hlower := hCount b hb
  have hprod :
      9 * (d : ℝ) ^ 8 <
        (d : ℝ) ^ 8 * ((centerOnePowerParameters n b).card : ℝ) :=
    lt_of_lt_of_le hmain hlower
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd8 : (0 : ℝ) < (d : ℝ) ^ 8 := pow_pos hdR _
  have hcardR :
      (9 : ℝ) < ((centerOnePowerParameters n b).card : ℝ) := by
    nlinarith
  have hcard : 9 < (centerOnePowerParameters n b).card := by
    exact_mod_cast hcardR
  exact ⟨b, hb, hcard⟩

/-- **Theorem 14.1 (center-one n-th power construction)**, modulo the
specialized character-sum estimate `HasCenterOnePowerCountBound`.

The statement uses an explicit positive index `d`; in the paper one takes
`d = gcd(n, q-1)`. `CenterOne.SharpPowerExistence` supplies the proved
counting estimate and gives the unconditional theorem.
@isnad1 id=ex.5h3v.s7.cfe848d7321a from=translated src=- shape=b0fd7718 vocab=f264aab7
-/
theorem exists_centerOne_magic_of_powers
    (n d : ℕ)
    (hd : 0 < d)
    (hodd : ringChar F ≠ 2)
    (hq : 7 < Fintype.card F)
    (hCount : HasCenterOnePowerCountBound F n d)
    (hmain :
      9 * (d : ℝ) ^ 8 <
        (Fintype.card F : ℝ) -
          centerOneC1 d * Real.sqrt (Fintype.card F : ℝ)) :
    ∃ M : Square3 F, IsMagicOfPowers n M := by
  obtain ⟨b, hb, hcard⟩ :=
    centerOne_power_parameters_card_gt_nine
      (F := F) n d hd hodd hq hCount hmain
  obtain ⟨t, htpow, htbad⟩ :=
    exists_power_parameter_outside_bad (F := F) hcard
  exact exists_centerOne_magic_of_powers_of_parameter
    (F := F) n hb htpow htbad

/-- The same theorem in `n`-Parker language.
@isnad1 id=not.5h3v.s7.eec4a3332fb3 from=translated src=- shape=eda038b2 vocab=22ec8a96
-/
theorem not_isNParker_of_centerOne_bound
    (n d : ℕ)
    (hd : 0 < d)
    (hodd : ringChar F ≠ 2)
    (hq : 7 < Fintype.card F)
    (hCount : HasCenterOnePowerCountBound F n d)
    (hmain :
      9 * (d : ℝ) ^ 8 <
        (Fintype.card F : ℝ) -
          centerOneC1 d * Real.sqrt (Fintype.card F : ℝ)) :
    ¬ IsNParker F n := by
  intro hP
  apply hP
  exact exists_centerOne_magic_of_powers
    (F := F) n d hd hodd hq hCount hmain

end Square3
end MagicSquares
