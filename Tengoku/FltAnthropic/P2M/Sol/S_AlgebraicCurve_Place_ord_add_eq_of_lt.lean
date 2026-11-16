import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_ord_add_eq_of_lt.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_ord_add_eq_of_lt

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Place.ord)
namespace FF2S
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_add_eq_of_lt (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (h : v.ord f < v.ord g) : v.ord (f + g) = v.ord f := by
  have hval : v.adicValuation g < v.adicValuation f := by
    have hf' := v.adicValuation_ne_zero hf
    have hg' := v.adicValuation_ne_zero hg
    rw [← WithZero.log_lt_log hg' hf']
    unfold Place.ord at h
    omega
  unfold Place.ord
  rw [Valuation.map_add_eq_of_lt_left _ hval]

end AlgebraicCurve.FF2S

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f :=
  AlgebraicCurve.FF2S.ord_add_eq_of_lt v hf hg h
