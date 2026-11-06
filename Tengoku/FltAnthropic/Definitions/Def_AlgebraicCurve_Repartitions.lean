import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open WithZero

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/--
@isnad1 id=le.1h4v.s7.d250002e632e from=translated src=- shape=b930e6f8 vocab=48e929d1
-/
theorem adicValuation_le_one_of_mem {x : F} (hx : x ∈ v.toValuationSubring) :
    v.adicValuation x ≤ 1 := by
  have h := (v.adicValuation_coe ⟨x, hx⟩).trans_le
    (v.heightOneSpectrum.intValuation_le_one ⟨x, hx⟩)
  simpa using h

/--
@isnad1 id=le.0h4v.s7.ae8582fd729b from=translated src=- shape=2d95f4e5 vocab=5ab4d933
-/
theorem adicValuation_algebraMap_le_one (a : K) :
    v.adicValuation (algebraMap K F a) ≤ 1 :=
  v.adicValuation_le_one_of_mem (v.algebraMap_mem' a)

end Place

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

variable {K F}

end AlgebraicCurve

end
