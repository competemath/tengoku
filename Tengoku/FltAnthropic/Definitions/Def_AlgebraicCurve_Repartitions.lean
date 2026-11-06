import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open WithZero

namespace AlgebraicCurve

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem adicValuation_le_one_of_mem {x : F} (hx : x ∈ v.toValuationSubring) :
    v.adicValuation x ≤ 1 := by
  have h := (v.adicValuation_coe ⟨x, hx⟩).trans_le
    (v.heightOneSpectrum.intValuation_le_one ⟨x, hx⟩)
  simpa using h

theorem adicValuation_algebraMap_le_one (a : K) :
    v.adicValuation (algebraMap K F a) ≤ 1 :=
  v.adicValuation_le_one_of_mem (v.algebraMap_mem' a)

end Place

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

variable {K F}

end AlgebraicCurve

end
