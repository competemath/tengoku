/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.Seed.NumberTheory.NumberField.ClassNumber
import Tengoku.Seed.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Tengoku.QuadraticNumberFields.QNFMathlib.RingTheory.ClassGroup.Narrow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Narrow Class Groups of Number Fields

This file connects the generic narrow class group API with rings of integers of
number fields.
-/

open scoped NumberField nonZeroDivisors

namespace NarrowClassGroup

namespace RingOfIntegers

variable (K : Type*) [Field K] [NumberField K]

/-- Real embeddings of the fraction field of `𝓞 K` form a finite type.-/
noncomputable instance instFintypeRingOfIntegersFractionRingRealEmbeddings :
    Fintype (FractionRing (𝓞 K) →+* ℝ) := by
  let e := IsLocalization.algEquiv (nonZeroDivisors (𝓞 K)) (FractionRing (𝓞 K)) K
  exact Fintype.ofInjective
    (fun σ : FractionRing (𝓞 K) →+* ℝ => σ.comp e.symm.toRingHom)
    (by
      intro σ τ hστ
      ext x
      obtain ⟨y, rfl⟩ := e.symm.surjective x
      exact RingHom.congr_fun hστ y)

/-- The narrow class group of `𝓞 K` is a finite type.-/
noncomputable instance instFintypeRingOfIntegersNarrowClassGroup :
    Fintype (NarrowClassGroup (𝓞 K)) :=
  Fintype.ofFinite _

end RingOfIntegers

end NarrowClassGroup

namespace NumberField

/-! ### Totally complex fields -/

/-- A totally complex field has no real embeddings.
@isnad1 id=isempty.0h1v.s4.3d018ba16ea1 from=translated src=- shape=4e11b0d0 vocab=f7eb86cd
-/
theorem isEmpty_realEmbeddings_of_isTotallyComplex (K : Type*) [Field K] [IsTotallyComplex K] :
    IsEmpty (K →+* ℝ) := by
  refine ⟨fun σ => ?_⟩
  let φ : K →+* ℂ := Complex.ofRealHom.comp σ
  exact (IsTotallyComplex.complexEmbedding_not_isReal φ) (by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    simp [φ, ComplexEmbedding.conjugate_coe_eq])

variable (K : Type*) [Field K] [NumberField K]

/-- The fraction field of `𝓞 K` has no real embeddings when `K` is totally complex.
@isnad1 id=isempty.0h1v.s6.10d8782d8467 from=translated src=- shape=b7fd1ed6 vocab=59e5d23d
-/
theorem isEmpty_fractionRing_realEmbeddings_of_isTotallyComplex
    [IsTotallyComplex K] :
    IsEmpty (FractionRing (𝓞 K) →+* ℝ) := by
  letI := isEmpty_realEmbeddings_of_isTotallyComplex K
  refine ⟨fun σ => ?_⟩
  let e := IsLocalization.algEquiv (nonZeroDivisors (𝓞 K)) (FractionRing (𝓞 K)) K
  exact isEmptyElim (σ.comp e.symm.toRingHom)

/-- For a totally complex number field, narrow and ordinary principal fractional ideals agree.
@isnad1 id=eq.0h1v.s11.d38bb23d49cd from=translated src=- shape=e5258159 vocab=691dc3d8
-/
theorem narrowPrincipalIdeals_eq_principalIdeals_of_isTotallyComplex
    [IsTotallyComplex K] :
    NarrowClassGroup.narrowPrincipalIdeals (𝓞 K) (FractionRing (𝓞 K)) =
      (toPrincipalIdeal (𝓞 K) (FractionRing (𝓞 K))).range := by
  letI := isEmpty_fractionRing_realEmbeddings_of_isTotallyComplex K
  exact NarrowClassGroup.narrowPrincipalIdeals_eq_principalIdeals_of_isEmpty

/-- For a totally complex number field, the narrow class group is isomorphic to the ordinary
class group.-/
noncomputable def narrowMulEquivClassGroupOfIsTotallyComplex
    [IsTotallyComplex K] :
    NarrowClassGroup (𝓞 K) ≃* ClassGroup (𝓞 K) := by
  letI := isEmpty_fractionRing_realEmbeddings_of_isTotallyComplex K
  exact NarrowClassGroup.mulEquivClassGroupOfIsEmpty (𝓞 K)

/-! ### Class numbers -/

/-- The narrow class number of a number field.-/
noncomputable def narrowClassNumber : ℕ :=
  NarrowClassGroup.narrowClassNumber (𝓞 K)

/-- The narrow class number of a number field is nonzero.
@isnad1 id=ne.0h1v.s4.30553dfae4d6 from=translated src=- shape=21777def vocab=c5164c70
-/
theorem narrowClassNumber_ne_zero : narrowClassNumber K ≠ 0 := Fintype.card_ne_zero

/-- The narrow class number of a number field is positive.
@isnad1 id=lt.0h1v.s4.7281cbea4cd8 from=translated src=- shape=31b077a1 vocab=56826210
-/
theorem narrowClassNumber_pos : 0 < narrowClassNumber K := Fintype.card_pos

end NumberField
