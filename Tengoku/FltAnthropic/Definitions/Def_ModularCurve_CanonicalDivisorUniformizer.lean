import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_CanonicalDivisor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open KaehlerDifferential

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

def uniformizer : F :=
  ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F)

/--
@isnad1 id=eq.0h3v.s5.74da2234069e from=translated src=- shape=67699dbc vocab=74dc9862
-/
theorem ord_uniformizer : v.ord v.uniformizer = 1 := by
  have hirr := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  simpa [uniformizer] using v.ord_coe_irreducible hirr

/--
@isnad1 id=ne.0h3v.s5.065ef66d2543 from=translated src=- shape=18197b12 vocab=c7fa849d
-/
theorem uniformizer_ne_zero : v.uniformizer ≠ 0 := by
  intro h
  simpa [h, v.ord_zero] using v.ord_uniformizer

/--
@isnad1 id=eq.0h3v.s7.bc6864727e77 from=translated src=- shape=e2273a1f vocab=265ab798
-/
theorem dCoord_eq : v.dCoord = KaehlerDifferential.D K F v.uniformizer := rfl

end Place

end AlgebraicCurve

end
