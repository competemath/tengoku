import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_ord_neg.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_ord_neg

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Place.ord_algebraMap)
namespace FF2S
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_neg (v : Place K F) (f : F) : v.ord (-f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  · rw [neg_eq_neg_one_mul, v.ord_mul (neg_ne_zero.mpr one_ne_zero) hf,
      show (-1 : F) = algebraMap K F (-1) by simp, v.ord_algebraMap, zero_add]

end AlgebraicCurve.FF2S

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F) (f : F) :
    v.ord (-f) = v.ord f :=
  AlgebraicCurve.FF2S.ord_neg v f
