import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_IsCurveOver
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_Differentials
import Tengoku.Seed.FieldTheory.Perfect
import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Basic
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicCurve_existsUnique_pDigits_of_transcendental
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicCurve_finiteDimensional_adjoin_of_transcendental

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_pDigits_existsUnique.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_pDigits_existsUnique

set_option autoImplicit false

universe u v

open KaehlerDifferential

namespace AlgebraicCurve
export _root_.AlgebraicCurve (IsCurveOver existsUnique_pDigits_of_transcendental finiteDimensional_adjoin_of_transcendental)
open _root_.AlgebraicCurve

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

private theorem transcendental_of_D_ne_zero' [PerfectField K] {t : F}
    (hdt : D K F t ≠ 0) : Transcendental K t := by
  by_contra htr
  rw [Transcendental, not_not] at htr
  have hint : IsIntegral K t := htr.isIntegral
  have hirr := minpoly.irreducible hint
  have hsep : (minpoly K t).Separable := PerfectField.separable_of_irreducible hirr
  have hd0 : (Polynomial.aeval t) (Polynomial.derivative (minpoly K t)) ≠ 0 := by
    intro h0
    by_cases hder : Polynomial.derivative (minpoly K t) = 0
    · exact hirr.1 (isCoprime_zero_right.mp (hder ▸ hsep))
    · exact absurd (Polynomial.degree_le_of_dvd (minpoly.dvd K t h0) hder)
        (not_le.2 (Polynomial.degree_derivative_lt (minpoly.ne_zero hint)))
  apply hdt
  have h0 : (D K F) ((Polynomial.aeval t) (minpoly K t)) = 0 := by
    rw [minpoly.aeval, map_zero]
  rw [Derivation.map_aeval] at h0
  exact (smul_eq_zero.mp h0).resolve_left hd0

private theorem pow_ne_of_D_ne_zero' (p : ℕ) [Fact p.Prime] [CharP K p] {t : F}
    (hdt : D K F t ≠ 0) (a : F) : a ^ p ≠ t := by
  intro ha
  apply hdt
  haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  rw [← ha, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]

private theorem pDigits_existsUnique_impl [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectField K] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (hdt : D K F t ≠ 0) (g : F) :
    ∃! a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) := by
  have htr : Transcendental K t := transcendental_of_D_ne_zero' hdt
  haveI : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F :=
    finiteDimensional_adjoin_of_transcendental x htr
  exact existsUnique_pDigits_of_transcendental p t htr (pow_ne_of_D_ne_zero' p hdt) g

end AlgebraicCurve

theorem solution {K : Type u} {F : Type v} [Field K] [Field F]
    [Algebra K F] [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime] [CharP K p]
    [PerfectField K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {t : F} (hdt : D K F t ≠ 0) (g : F) :
    ∃! a : Fin p → F, g = ∑ i : Fin p, a i ^ p * t ^ (i : ℕ) :=
  AlgebraicCurve.pDigits_existsUnique_impl p x hdt g
