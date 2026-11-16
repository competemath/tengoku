import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_Correspondence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_one_le_ramificationIndexAlong.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_one_le_ramificationIndexAlong
set_option autoImplicit false

namespace AlgebraicCurve export _root_.AlgebraicCurve (algebraAlong isIntegral_along Place.ramificationIndexAlong Place) namespace Place export _root_.AlgebraicCurve.Place (ramificationIndexAlong ramificationIndex_pos) end AlgebraicCurve.Place
open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in
private theorem AlgebraicCurve.Place.solution_impl
    {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : AlgebraicCurve.Place K F') :
    1 ≤ AlgebraicCurve.Place.ramificationIndexAlong φ w := by
  letI := AlgebraicCurve.algebraAlong φ
  haveI := AlgebraicCurve.isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : AlgebraicCurve.Place K F') :
    1 ≤ AlgebraicCurve.Place.ramificationIndexAlong φ w :=
  AlgebraicCurve.Place.solution_impl φ hφ w
