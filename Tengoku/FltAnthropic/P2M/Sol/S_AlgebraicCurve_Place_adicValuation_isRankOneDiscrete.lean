import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete

open IsDedekindDomain WithZero IsLocalRing

noncomputable section

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place)
open _root_.AlgebraicCurve

namespace Place
export _root_.AlgebraicCurve.Place (adicValuation toValuationSubring)
open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem rowMain : v.adicValuation.IsRankOneDiscrete :=
  IsDiscreteValuationRing.isRankOneDiscrete v.toValuationSubring F

end Place

end AlgebraicCurve

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_Place_adicValuation_isRankOneDiscrete.AlgebraicCurve in
/--
@isnad1 id=isrankon.0h3v.s5.a529a5c0f8c9 from=translated src=- shape=4a2062f4 vocab=77da76b6
-/
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.IsRankOneDiscrete :=
  AlgebraicCurve.Place.rowMain v
