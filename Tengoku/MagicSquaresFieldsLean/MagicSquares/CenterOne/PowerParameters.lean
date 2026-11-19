import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.Powers
import Tengoku.MagicSquaresFieldsLean.MagicSquares.CenterOne.BadParameterFacts
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace Square3

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Finite set of parameters satisfying all power conditions

The center coefficient is included.  Its corresponding entry is `1`, so the
condition at index `4` is automatic, but keeping all nine positions makes the
final witness theorem very clean.
-/

/-- Parameters for which every entry on the center-one line is an `n`th power.
No distinctness or nonvanishing requirement is imposed yet.-/
noncomputable def centerOnePowerParameters (n : ℕ) (b : F) : Finset F := by
  classical
  exact Finset.univ.filter (fun t =>
    ∀ k : Fin 9, IsNthPower n (1 + centerOneCoeff b k * t))

omit [DecidableEq F] in
/--
@isnad1 id=iff.0h4v.s6.a38395080d20 from=translated src=- shape=7d2fd878 vocab=c62d71d8
-/
@[simp]
theorem mem_centerOnePowerParameters
    (n : ℕ) (b t : F) :
    t ∈ centerOnePowerParameters n b ↔
      ∀ k : Fin 9, IsNthPower n (1 + centerOneCoeff b k * t) := by
  classical
  simp [centerOnePowerParameters]

/-- More than nine power-good parameters force one outside the at-most-nine
bad parameter set.
@isnad1 id=ex.1h3v.s6.450f73d0adf9 from=translated src=- shape=1cfe34ec vocab=67734ef5
-/
theorem exists_power_parameter_outside_bad
    {n : ℕ} {b : F}
    (hcard : 9 < (centerOnePowerParameters n b).card) :
    ∃ t : F,
      t ∈ centerOnePowerParameters n b ∧ t ∉ centerOneBadT b := by
  by_contra h
  push Not at h
  have hsub : centerOnePowerParameters n b ⊆ centerOneBadT b := by
    intro t ht
    exact h t ht
  have hle :
      (centerOnePowerParameters n b).card ≤ (centerOneBadT b).card :=
    Finset.card_le_card hsub
  have hbadcard := centerOneBadT_card_le b
  omega

/-- A power-good parameter outside the bad set gives the desired magic square.
@isnad1 id=ex.3h4v.s6.8ff006972313 from=translated src=- shape=5b78cb3e vocab=6f764a3a
-/
theorem exists_centerOne_magic_of_powers_of_parameter
    (n : ℕ)
    {b t : F}
    (hb : CenterOneGoodB b)
    (htpow : t ∈ centerOnePowerParameters n b)
    (htbad : t ∉ centerOneBadT b) :
    ∃ M : Square3 F, IsMagicOfPowers n M := by
  refine ⟨centerOneLine t b, ?_⟩
  have ht0 : t ≠ 0 := ne_zero_of_not_mem_centerOneBadT htbad
  apply centerOneLine_isMagicOfPowers n hb ht0
  exact (mem_centerOnePowerParameters n b t).mp htpow

end Square3
end MagicSquares
