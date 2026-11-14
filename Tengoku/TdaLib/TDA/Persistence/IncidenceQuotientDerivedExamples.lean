import Tengoku.TdaLib.TDA.Persistence.IncidenceQuotientDerived
import Tengoku.Seed.CategoryTheory.Abelian.Projective.Resolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples for higher quotient-extension exactness

These fixtures exercise the positive-degree theorem at degree one and two on a genuine rational
strict vertex, and at degree two on the zero restricted module.
-/

set_option autoImplicit false

namespace TDA.Persistence.IncidenceQuotientDerivedExamples

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceQuotientSimple
open TDA.Persistence.IncidenceQuotientBaseChange
open TDA.Persistence.IncidenceQuotientDerived
open TDA.Persistence.IncidenceQuotientDerivedOne

noncomputable section

local instance : Fintype Unit := Fintype.ofFinite Unit
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (PairPoset Unit) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop Unit × WithTop Unit => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset Unit) := Classical.decRel _
local instance : DecidableLT (PairPoset Unit) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset Unit) :=
  TDA.Persistence.FiniteRankProjectiveEndAlgebra.instLocallyFiniteOrderPairPoset
local instance : DecidableEq (PairPoset Unit) :=
  TDA.Persistence.FiniteRankProjectiveEndAlgebra.instDecidableEqPairPoset
local instance : Fintype (ComparablePair Unit) := Fintype.ofFinite _
/--
@isnad1 id=istwosid.0h1v.s7.9c3d57f512eb from=translated src=- shape=177e3479 vocab=fc375734
-/
local instance diagonalIdealTwoSidedUnit {k : Type} [Field k] :
    (TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
      (k := k) (S := Unit)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := Unit)

private def unitStrictVertex717 : StrictVertex Unit :=
  ⟨⟨((), ⊤), le_top⟩, by simp⟩

private abbrev unitVertexModule717 :=
  RightVertexRestrictedModule (k := ℚ) (S := Unit) unitStrictVertex717

/-- The actual rational strict vertex vanishes in degree one by the restricted-module result.
@isnad1 id=iszero.0h0v.s11.2912ce33184f from=translated src=- shape=228469ce vocab=d1995605
-/
theorem rational_unit_vertex_derived_one_isZero :
    IsZero (((extensionFunctor (k := ℚ) (S := Unit)).leftDerived 1).obj
      unitVertexModule717) :=
  rightVertexExtension_leftDerived_positive_isZero
    (k := ℚ) (S := Unit) unitStrictVertex717 1 (by norm_num)

/-- The same actual rational strict vertex vanishes in degree two by the higher projective-column
argument.
@isnad1 id=iszero.0h0v.s11.0bc9fb3a9588 from=translated src=- shape=228469ce vocab=d1995605
-/
theorem rational_unit_vertex_derived_two_isZero :
    IsZero (((extensionFunctor (k := ℚ) (S := Unit)).leftDerived 2).obj
      unitVertexModule717) :=
  rightVertexExtension_leftDerived_positive_isZero
    (k := ℚ) (S := Unit) unitStrictVertex717 2 (by norm_num)

/-- Every actual resolution of the rational strict vertex maps to a complex exact at degree two.
@isnad1 id=exactat.0h1v.s10.8f02e8c667a1 from=translated src=- shape=2e2b2528 vocab=80c638fe
-/
theorem rational_unit_vertex_resolution_exact_two
    (P : ProjectiveResolution unitVertexModule717) :
    (TDA.Persistence.IncidenceQuotientDerivedOne.extensionMappedResolution
      (k := ℚ) (S := Unit) P).ExactAt 2 :=
  extensionMappedResolution_exactAt_positive_restricted
    (k := ℚ) (S := Unit)
    (RightVertexModule (k := ℚ) (S := Unit) unitStrictVertex717) P 2 (by norm_num)

/-- The restricted zero module has zero second derived extension.
@isnad1 id=iszero.0h0v.s11.a5068f53c601 from=translated src=- shape=503c6208 vocab=9c7cb488
-/
theorem rational_unit_zero_derived_two_isZero :
    IsZero (((extensionFunctor (k := ℚ) (S := Unit)).leftDerived 2).obj
      ((ModuleCat.restrictScalars (quotientHom (k := ℚ) (S := Unit))).obj
        (ModuleCat.of (TDA.Persistence.IncidenceQuotientBaseChange.RightQuotient
          (k := ℚ) (S := Unit)) PUnit.{1}))) :=
  extension_leftDerived_positive_isZero
    (k := ℚ) (S := Unit)
    (ModuleCat.of (TDA.Persistence.IncidenceQuotientBaseChange.RightQuotient
      (k := ℚ) (S := Unit)) PUnit.{1}) 2 (by norm_num)

/-- Every actual resolution of the rational zero quotient module maps to a complex exact at
degree two.
@isnad1 id=exactat.0h1v.s11.d8f7874ab8e9 from=translated src=- shape=69556a85 vocab=a18bee01
-/
theorem rational_unit_zero_resolution_exact_two
    (P : ProjectiveResolution
      ((ModuleCat.restrictScalars (quotientHom (k := ℚ) (S := Unit))).obj
        (ModuleCat.of (TDA.Persistence.IncidenceQuotientBaseChange.RightQuotient
          (k := ℚ) (S := Unit)) PUnit.{1}))) :
    (TDA.Persistence.IncidenceQuotientDerivedOne.extensionMappedResolution
      (k := ℚ) (S := Unit) P).ExactAt 2 :=
  extensionMappedResolution_exactAt_positive_restricted
    (k := ℚ) (S := Unit)
    (ModuleCat.of (TDA.Persistence.IncidenceQuotientBaseChange.RightQuotient
      (k := ℚ) (S := Unit)) PUnit.{1}) P 2 (by norm_num)

end

end TDA.Persistence.IncidenceQuotientDerivedExamples
