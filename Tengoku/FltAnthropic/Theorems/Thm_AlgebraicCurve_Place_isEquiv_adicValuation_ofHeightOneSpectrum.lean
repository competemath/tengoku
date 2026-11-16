import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_RatFuncPlaces

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `#p2m_type_eq_warn`, 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open AlgebraicCurve
theorem P2M.Dup.AlgebraicCurve.Place.isEquiv_adicValuation_ofHeightOneSpectrum {K F : Type*} [Field K] [Field F] [Algebra K F] {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    [Algebra K R] [IsScalarTower K R F] (w : IsDedekindDomain.HeightOneSpectrum R) :
    (w.valuation F).IsEquiv (Place.ofHeightOneSpectrum (K := K) w).adicValuation := by exact @_root_.P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_ofHeightOneSpectrum.solution K F _ _ _ R _ _ _ _ _ _ w

