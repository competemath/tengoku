import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one.lean`: wrote out 6 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 4 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place)
open _root_.AlgebraicCurve

namespace Place
export _root_.AlgebraicCurve.Place (ext heightOneSpectrum adicValuation adicValuation_coe_eq_one_iff toValuationSubring)
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
private theorem _root_.AlgebraicCurve.Place.mem_iff_adicValuation_le_one {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 := by
  rw [← v.adicValuation_valuationSubring]
  exact Valuation.mem_valuationSubring_iff _ _

export _root_.AlgebraicCurve.Place (mem_iff_adicValuation_le_one)
private theorem rowMain (a : v.toValuationSubring) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ v.adicValuation (a : F) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← v.adicValuation_coe_eq_one_iff,
    lt_iff_le_and_ne]
  have hle : v.adicValuation (a : F) ≤ 1 := v.mem_iff_adicValuation_le_one.mp a.2
  tauto

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_mem_maximalIdeal_iff_adicValuation_lt_one.AlgebraicCurve in
/--
@isnad1 id=iff.0h4v.s9.fc7c4bfc85c2 from=translated src=- shape=d05d694b vocab=214d4958
-/
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (a : v.toValuationSubring) :
    a ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔ v.adicValuation (a : F) < 1 :=
  AlgebraicCurve.Place.rowMain v a
