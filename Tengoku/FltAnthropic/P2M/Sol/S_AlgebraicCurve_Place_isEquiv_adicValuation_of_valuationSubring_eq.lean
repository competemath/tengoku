import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place)
open _root_.AlgebraicCurve

namespace Place
export _root_.AlgebraicCurve.Place (ext heightOneSpectrum adicValuation toValuationSubring)
open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.adicValuation_valuationSubring :
    v.adicValuation.valuationSubring = v.toValuationSubring := by
  ext x
  rw [Valuation.mem_valuationSubring_iff]
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hx
    exact a.2
  · intro hx
    exact v.heightOneSpectrum.valuation_le_one (⟨x, hx⟩ : v.toValuationSubring)

export _root_.AlgebraicCurve.Place (adicValuation_valuationSubring)
private theorem rowMain {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) : w.IsEquiv v.adicValuation :=
  (Valuation.isEquiv_iff_valuationSubring _ _).mpr
    (h.trans v.adicValuation_valuationSubring.symm)

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_isEquiv_adicValuation_of_valuationSubring_eq.AlgebraicCurve in
/--
@isnad1 id=isequiv.1h5v.s6.4490bca6025c from=translated src=- shape=42bf9343 vocab=1535943b
-/
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] {w : Valuation F Γ}
    (h : w.valuationSubring = v.toValuationSubring) :
    w.IsEquiv v.adicValuation :=
  AlgebraicCurve.Place.rowMain v h
