import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_min_ord_le_ord_add.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_min_ord_le_ord_add

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Place.ord)
namespace FF2S
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/--
@isnad1 id=le.3h5v.s7.691621096795 from=translated src=- shape=2d917a74 vocab=470e609b
-/
theorem le_ord_add (v : Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  have hf' := v.adicValuation_ne_zero hf
  have hg' := v.adicValuation_ne_zero hg
  have hfg' := v.adicValuation_ne_zero hfg
  have hmax : v.adicValuation (f + g) ≤ max (v.adicValuation f) (v.adicValuation g) :=
    Valuation.map_add _ _ _
  unfold Place.ord
  rcases le_max_iff.mp hmax with hle | hle
  · have := (WithZero.log_le_log hfg' hf').mpr hle
    omega
  · have := (WithZero.log_le_log hfg' hg').mpr hle
    omega

end AlgebraicCurve.FF2S

/--
@isnad1 id=le.3h5v.s7.691621096795 from=translated src=- shape=2d917a74 vocab=470e609b
-/
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) :=
  AlgebraicCurve.FF2S.le_ord_add v hf hg hfg
