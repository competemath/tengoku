import Tengoku.TdaLib.TDA.Persistence.IncidenceQuotientSimple

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples for simple modules over the right diagonal quotient

These consumers distinguish strict vertices over `Bool`, treat the singleton lattice, and apply
the derived comparison and positive-degree vanishing over arbitrary fields.  The rational-field
instances give a concrete infinite-field specialization.
-/

set_option autoImplicit false

namespace TDA.Persistence.IncidenceQuotientSimpleExamples

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective
open TDA.Persistence.IncidenceQuotientSimple
open TDA.Persistence.IncidenceVertexTensorFunctor
open TDA.Persistence.IncidenceVertexTor

noncomputable section

local instance : Fintype Bool := Fintype.ofFinite Bool
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (PairPoset Bool) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop Bool × WithTop Bool => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset Bool) := Classical.decRel _
local instance : DecidableLT (PairPoset Bool) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset Bool) :=
  TDA.Persistence.FiniteRankProjectiveEndAlgebra.instLocallyFiniteOrderPairPoset
local instance : DecidableEq (PairPoset Bool) :=
  TDA.Persistence.FiniteRankProjectiveEndAlgebra.instDecidableEqPairPoset
local instance : Fintype (ComparablePair Bool) := Fintype.ofFinite _
/--
@isnad1 id=istwosid.0h1v.s7.e74a92d13edd from=translated src=- shape=177e3479 vocab=3c9f39f6
-/
local instance diagonalIdealTwoSidedBool {k : Type} [Field k] :
    (TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
      (k := k) (S := Bool)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := Bool)

private def boolLowerStrictVertex : StrictVertex Bool :=
  ⟨⟨((false : WithTop Bool), (true : WithTop Bool)), by simp⟩, by simp⟩

private def boolUpperStrictVertex : StrictVertex Bool :=
  ⟨⟨((true : WithTop Bool), ⊤), le_top⟩, by simp⟩

/--
@isnad1 id=ne.0h0v.s3.9231d97aaff2 from=translated src=- shape=836e6cbb vocab=a1b1a0cf
-/
theorem bool_strict_vertices_distinct : boolLowerStrictVertex ≠ boolUpperStrictVertex := by
  intro h
  have hfirst := congrArg (fun v : StrictVertex Bool => v.1.val.1) h
  have hcoe : (false : WithTop Bool) = true := by
    simp [boolLowerStrictVertex, boolUpperStrictVertex] at hfirst
  cases (WithTop.coe_injective hcoe)

/--
@isnad1 id=not.0h1v.s8.91d2f9c9cdd6 from=translated src=- shape=aad8ec5c vocab=abc20256
-/
theorem bool_vertex_modules_not_isomorphic {k : Type} [Field k] :
    ¬ Nonempty (RightVertexModule (k := k) (S := Bool) boolLowerStrictVertex ≅
      RightVertexModule (k := k) (S := Bool) boolUpperStrictVertex) := by
  intro h
  exact bool_strict_vertices_distinct
    ((rightVertexModule_iso_iff (k := k) (S := Bool)
      boolLowerStrictVertex boolUpperStrictVertex).mp h)

/-- A rational-field specialization of the arbitrary-field classification theorem.
@isnad1 id=existsun.0h0v.s8.15e6edf797e0 from=translated src=- shape=bc330387 vocab=c17a26f9
-/
theorem rational_bool_vertex_classified :
    ∃! v : StrictVertex Bool,
      Nonempty (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex ≅
        RightVertexModule (k := ℚ) (S := Bool) v) := by
  letI : IsSimpleModule (RightQuotient (k := ℚ) (S := Bool))
      (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex) :=
    rightVertexModule_isSimpleModule (k := ℚ) (S := Bool) boolLowerStrictVertex
  exact simpleModule_existsUnique_vertex (k := ℚ) (S := Bool)
    (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex)

/--
@isnad1 id=infinite.0h0v.s1.eeec4529fb6b from=translated src=- shape=49959d42 vocab=0171e214
-/
theorem rationalField_infinite : Infinite ℚ := inferInstance

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
@isnad1 id=istwosid.0h1v.s7.9c3d57f512eb from=translated src=- shape=177e3479 vocab=e41ce7de
-/
local instance diagonalIdealTwoSidedUnit {k : Type} [Field k] :
    (TDA.Persistence.FiniteRankProjectiveDiagonalIdealProjective.DiagonalIdeal
      (k := k) (S := Unit)).IsTwoSided :=
  diagonalIdeal_isTwoSided (k := k) (S := Unit)

private def singletonStrictVertex : StrictVertex Unit :=
  ⟨⟨((), ⊤), le_top⟩, by simp⟩

/--
@isnad1 id=eq.0h1v.s4.967b31665a6e from=translated src=- shape=f8042301 vocab=c5ceb0c9
-/
theorem singleton_strictVertex_unique (v : StrictVertex Unit) :
    v = singletonStrictVertex := by
  rcases v with ⟨⟨⟨a, b⟩, hab⟩, hv⟩
  cases a with
  | top => cases b <;> simp at hv
  | coe a =>
      cases a
      cases b with
      | top => rfl
      | coe b => cases b; simp at hv

/--
@isnad1 id=subsingl.0h0v.s3.fa9e93e278b8 from=translated src=- shape=87ceb31f vocab=f76e76c4
-/
theorem singleton_strictVertex_subsingleton : Subsingleton (StrictVertex Unit) :=
  ⟨fun v w => (singleton_strictVertex_unique v).trans
    (singleton_strictVertex_unique w).symm⟩

/--
@isnad1 id=existsun.0h0v.s8.5d819b3fb03b from=translated src=- shape=bc330387 vocab=1198b2ff
-/
theorem singleton_rational_vertex_classified :
    ∃! v : StrictVertex Unit,
      Nonempty (RightVertexModule (k := ℚ) (S := Unit) singletonStrictVertex ≅
        RightVertexModule (k := ℚ) (S := Unit) v) := by
  letI : IsSimpleModule (RightQuotient (k := ℚ) (S := Unit))
      (RightVertexModule (k := ℚ) (S := Unit) singletonStrictVertex) :=
    rightVertexModule_isSimpleModule (k := ℚ) (S := Unit) singletonStrictVertex
  exact simpleModule_existsUnique_vertex (k := ℚ) (S := Unit)
    (RightVertexModule (k := ℚ) (S := Unit) singletonStrictVertex)

/--
@isnad1 id=not.0h1v.s9.7a9c1a42f591 from=translated src=- shape=170e30ed vocab=f53f5699
-/
theorem zeroModule_not_simple {k : Type} [Field k] :
    ¬ IsSimpleModule (RightQuotient (k := k) (S := Unit))
      (ModuleCat.of (RightQuotient (k := k) (S := Unit)) PUnit) := by
  intro h
  letI : Nontrivial PUnit := IsSimpleModule.nontrivial
    (RightQuotient (k := k) (S := Unit))
      (ModuleCat.of (RightQuotient (k := k) (S := Unit)) PUnit)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne PUnit
  exact hxy (Subsingleton.elim x y)

/--
@isnad1 id=not.0h1v.s9.51844daa2b4d from=translated src=- shape=d6a20d40 vocab=a5946345
-/
theorem bool_lower_degree_zero_not_isZero {k : Type} [Field k] :
    ¬ IsZero (((vertexTensor (k := k) (S := Bool) boolLowerStrictVertex).leftDerived 0).obj
      (diagonalQuotientModule (k := k) (S := Bool))) :=
  diagonalQuotient_leftDerivedZero_not_isZero
    (k := k) (S := Bool) boolLowerStrictVertex

/--
@isnad1 id=iszero.0h1v.s9.305253953155 from=translated src=- shape=49ab559a vocab=a5946345
-/
theorem bool_lower_degree_one_isZero {k : Type} [Field k] :
    IsZero (((vertexTensor (k := k) (S := Bool) boolLowerStrictVertex).leftDerived 1).obj
      (diagonalQuotientModule (k := k) (S := Bool))) :=
  diagonalQuotient_leftDerived_pos_isZero
    (k := k) (S := Bool) boolLowerStrictVertex 1 (Nat.zero_lt_succ 0)

/--
@isnad1 id=existsun.0h0v.s10.7e677a297768 from=translated src=- shape=fbee5cfa vocab=529cdcc3
-/
theorem bool_lower_simple_positiveDerived_zero :
    ∃! v : StrictVertex Bool,
      Nonempty (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex ≅
        RightVertexModule (k := ℚ) (S := Bool) v) ∧
      IsZero (((vertexTensor (k := ℚ) (S := Bool) v).leftDerived 1).obj
        (diagonalQuotientModule (k := ℚ) (S := Bool))) := by
  letI : IsSimpleModule (RightQuotient (k := ℚ) (S := Bool))
      (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex) :=
    rightVertexModule_isSimpleModule (k := ℚ) (S := Bool) boolLowerStrictVertex
  exact simpleModule_existsUnique_vertex_positiveLeftDerived_isZero
    (k := ℚ) (S := Bool)
    (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex) 1 (Nat.zero_lt_succ 0)

noncomputable def bool_lower_simple_degree_zero_comparison :
    restrictRightQuotientModule (k := ℚ) (S := Bool)
        (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex) ≅
      (((vertexTensor (k := ℚ) (S := Bool) boolLowerStrictVertex).leftDerived 0).obj
        (diagonalQuotientModule (k := ℚ) (S := Bool))) := by
  letI : IsSimpleModule (RightQuotient (k := ℚ) (S := Bool))
      (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex) :=
    rightVertexModule_isSimpleModule (k := ℚ) (S := Bool) boolLowerStrictVertex
  exact simpleModule_leftDerivedZeroIso (k := ℚ) (S := Bool)
    (RightVertexModule (k := ℚ) (S := Bool) boolLowerStrictVertex)
    boolLowerStrictVertex (Iso.refl _)

end

end TDA.Persistence.IncidenceQuotientSimpleExamples
