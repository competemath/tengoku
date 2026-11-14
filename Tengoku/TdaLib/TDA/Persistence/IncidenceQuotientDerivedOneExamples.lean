import Tengoku.TdaLib.TDA.Persistence.IncidenceQuotientDerivedOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples for degree-one quotient-extension exactness

The fixtures specialize the all-module vanishing to the zero module and to an actual strict
vertex over the singleton lattice.
-/

set_option autoImplicit false

namespace TDA.Persistence.IncidenceQuotientDerivedOneExamples

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceQuotientBaseChange
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
@isnad1 id=istwosid.0h1v.s7.9c3d57f512eb from=translated src=- shape=177e3479 vocab=dd46d519
-/
local instance diagonalIdealTwoSidedUnit {k : Type} [Field k] :
    (TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
      (k := k) (S := Unit)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := Unit)

private def unitStrictVertex :
    TDA.Persistence.FiniteRankProjectiveEndAlgebra.StrictVertex Unit :=
  ⟨⟨((), ⊤), le_top⟩, by simp⟩

/-- The first left-derived extension of the singleton zero module is zero.
@isnad1 id=iszero.0h0v.s11.da10f2e5933e from=translated src=- shape=503c6208 vocab=4b1f7e7d
-/
theorem rational_unit_zero_derived_one_isZero :
    IsZero (((extensionFunctor (k := ℚ) (S := Unit)).leftDerived 1).obj
      ((ModuleCat.restrictScalars (quotientHom (k := ℚ) (S := Unit))).obj
        (ModuleCat.of (RightQuotient (k := ℚ) (S := Unit)) PUnit))) :=
  extension_leftDerived_one_isZero_zero (k := ℚ) (S := Unit)

/-- The actual restricted singleton vertex has zero first derived quotient extension.
@isnad1 id=iszero.0h0v.s11.54fdaabe6383 from=translated src=- shape=b013ca51 vocab=3200bb88
-/
theorem rational_unit_vertex_derived_one_isZero :
    IsZero (((extensionFunctor (k := ℚ) (S := Unit)).leftDerived 1).obj
      (RightVertexRestrictedModule (k := ℚ) (S := Unit) unitStrictVertex)) :=
  rightVertexExtension_leftDerived_one_isZero (k := ℚ) (S := Unit) unitStrictVertex

end

end TDA.Persistence.IncidenceQuotientDerivedOneExamples
