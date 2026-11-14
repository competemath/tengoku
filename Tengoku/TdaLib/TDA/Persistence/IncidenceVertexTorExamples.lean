import Tengoku.TdaLib.TDA.Persistence.IncidenceVertexTor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples for derived incidence-algebra vertex tensors

These examples instantiate the actual quotient resolution at strict vertices of `Bool` and `Unit`.
They are valid over every field; `ℚ` is included as a concrete infinite coefficient field.
-/

set_option autoImplicit false

namespace TDA.Persistence.IncidenceVertexTorExamples

open CategoryTheory
open CategoryTheory.Limits
open TDA.Persistence.FiniteRankProjectiveEndAlgebra
open TDA.Persistence.IncidenceVertexTensorFunctor
open TDA.Persistence.IncidenceVertexTor

noncomputable section

local instance : Fintype Bool := Fintype.ofFinite Bool
local instance : DecidableLE Bool := Classical.decRel _
local instance : DecidableLT Bool := Classical.decRel _
local instance : DecidableEq Bool := Classical.decEq _
local instance : DecidableEq (WithTop Bool) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (PairPoset Bool) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop Bool × WithTop Bool => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset Bool) := Classical.decRel _
local instance : DecidableLT (PairPoset Bool) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset Bool) := Fintype.toLocallyFiniteOrder
local instance : DecidableEq (PairPoset Bool) := Classical.decEq _
local instance : Fintype (ComparablePair Bool) := Fintype.ofFinite _

private def boolStrictVertex : StrictVertex Bool :=
  ⟨⟨(true, ⊤), le_top⟩, by simp⟩

/--
@isnad1 id=iszero.0h1v.s9.954d66b87e63 from=translated src=- shape=49ab559a vocab=d4d4c5e6
-/
theorem bool_degree_one_leftDerived_isZero {k : Type} [Field k] :
    IsZero (((vertexTensor (k := k) (S := Bool) boolStrictVertex).leftDerived 1).obj
      (diagonalQuotientModule (k := k) (S := Bool))) :=
  diagonalQuotient_leftDerived_pos_isZero (k := k) (S := Bool) boolStrictVertex 1
    (Nat.zero_lt_succ 0)

/--
@isnad1 id=iszero.0h1v.s9.fc51514327a1 from=translated src=- shape=49ab559a vocab=d4d4c5e6
-/
theorem bool_degree_three_leftDerived_isZero {k : Type} [Field k] :
    IsZero (((vertexTensor (k := k) (S := Bool) boolStrictVertex).leftDerived 3).obj
      (diagonalQuotientModule (k := k) (S := Bool))) :=
  diagonalQuotient_leftDerived_pos_isZero (k := k) (S := Bool) boolStrictVertex 3
    (Nat.zero_lt_succ 2)

/--
@isnad1 id=not.0h1v.s9.4d9a17804217 from=translated src=- shape=d6a20d40 vocab=d4d4c5e6
-/
theorem bool_degree_zero_leftDerived_not_isZero {k : Type} [Field k] :
    ¬ IsZero (((vertexTensor (k := k) (S := Bool) boolStrictVertex).leftDerived 0).obj
      (diagonalQuotientModule (k := k) (S := Bool))) :=
  diagonalQuotient_leftDerivedZero_not_isZero (k := k) (S := Bool) boolStrictVertex

/--
@isnad1 id=eq.0h1v.s14.6407a5fd592f from=translated src=- shape=1b1195f2 vocab=efcfc88f
-/
theorem bool_degree_zero_unit_law {k : Type} [Field k] :
    (diagonalQuotient_leftDerivedZeroIso (k := k) (S := Bool) boolStrictVertex).hom
      (((Functor.leftDerivedZeroIsoSelf
        (vertexTensor (k := k) (S := Bool) boolStrictVertex)).app
        (diagonalQuotientModule (k := k) (S := Bool))).inv.hom
        (mk (k := k) (S := Bool) boolStrictVertex
          (diagonalQuotientModule (k := k) (S := Bool)) 1)) = (1 : k) :=
  diagonalQuotient_leftDerivedZeroIso_hom_unit
    (k := k) (S := Bool) boolStrictVertex

local instance : Fintype Unit := Fintype.ofFinite Unit
local instance : DecidableLE Unit := Classical.decRel _
local instance : DecidableLT Unit := Classical.decRel _
local instance : DecidableEq Unit := Classical.decEq _
local instance : DecidableEq (WithTop Unit) := Classical.decEq _
local instance (p : Prop) : Decidable p := Classical.propDecidable p
local instance : Fintype (PairPoset Unit) :=
  Fintype.subtype (Finset.univ.filter fun ab : WithTop Unit × WithTop Unit => ab.1 ≤ ab.2)
    (by intro ab; simp)
local instance : DecidableLE (PairPoset Unit) := Classical.decRel _
local instance : DecidableLT (PairPoset Unit) := Classical.decRel _
local instance : LocallyFiniteOrder (PairPoset Unit) := Fintype.toLocallyFiniteOrder
local instance : DecidableEq (PairPoset Unit) := Classical.decEq _
local instance : Fintype (ComparablePair Unit) := Fintype.ofFinite _

private def singletonStrictVertex : StrictVertex Unit :=
  ⟨⟨((), ⊤), le_top⟩, by simp⟩

/--
@isnad1 id=iszero.0h1v.s9.b32f24cab0dc from=translated src=- shape=49ab559a vocab=5bfbf0ef
-/
theorem singleton_degree_one_leftDerived_isZero {k : Type} [Field k] :
    IsZero (((vertexTensor (k := k) (S := Unit) singletonStrictVertex).leftDerived 1).obj
      (diagonalQuotientModule (k := k) (S := Unit))) :=
  diagonalQuotient_leftDerived_pos_isZero (k := k) (S := Unit) singletonStrictVertex 1
    (Nat.zero_lt_succ 0)

/--
@isnad1 id=iszero.0h1v.s9.5e7f5941f3a7 from=translated src=- shape=49ab559a vocab=5bfbf0ef
-/
theorem singleton_degree_two_leftDerived_isZero {k : Type} [Field k] :
    IsZero (((vertexTensor (k := k) (S := Unit) singletonStrictVertex).leftDerived 2).obj
      (diagonalQuotientModule (k := k) (S := Unit))) :=
  diagonalQuotient_leftDerived_pos_isZero (k := k) (S := Unit) singletonStrictVertex 2
    (Nat.zero_lt_succ 1)

/--
@isnad1 id=not.0h1v.s9.cfb749d9b0db from=translated src=- shape=d6a20d40 vocab=5bfbf0ef
-/
theorem singleton_degree_zero_leftDerived_not_isZero {k : Type} [Field k] :
    ¬ IsZero (((vertexTensor (k := k) (S := Unit) singletonStrictVertex).leftDerived 0).obj
      (diagonalQuotientModule (k := k) (S := Unit))) :=
  diagonalQuotient_leftDerivedZero_not_isZero (k := k) (S := Unit) singletonStrictVertex

/--
@isnad1 id=eq.0h1v.s14.c3464cf4d349 from=translated src=- shape=1b1195f2 vocab=0ae320b6
-/
theorem singleton_degree_zero_unit_law {k : Type} [Field k] :
    (diagonalQuotient_leftDerivedZeroIso (k := k) (S := Unit) singletonStrictVertex).hom
      (((Functor.leftDerivedZeroIsoSelf
        (vertexTensor (k := k) (S := Unit) singletonStrictVertex)).app
        (diagonalQuotientModule (k := k) (S := Unit))).inv.hom
        (mk (k := k) (S := Unit) singletonStrictVertex
          (diagonalQuotientModule (k := k) (S := Unit)) 1)) = (1 : k) :=
  diagonalQuotient_leftDerivedZeroIso_hom_unit
    (k := k) (S := Unit) singletonStrictVertex

/--
@isnad1 id=infinite.0h0v.s1.eeec4529fb6b from=translated src=- shape=49959d42 vocab=0171e214
-/
theorem rationalField_infinite : Infinite ℚ := inferInstance

end

end TDA.Persistence.IncidenceVertexTorExamples
