/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.RealClosure.Quadratic.Order
import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.RealClosure.Odd.Maximal
import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Ordering.Obstruction
import Tengoku.Seed.FieldTheory.IsRealClosed.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The maximal ordered intermediate field is real closed

The quadratic and odd-degree maximality bridges provide exactly the two
premises required by `IsRealClosed.of_linearOrderedField`.
-/

namespace RatFuncWittLocalGlobal
namespace OrderedRealClosure

universe u

variable {F : Type u} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

/-- A maximal ordered intermediate field is real closed.
@isnad1 id=isrealcl.1h2v.s7.61a884a579da from=translated src=- shape=27a543ef vocab=2017c0d7
-/
theorem maximal_isRealClosed
    (M : Intermediate F) (hmax : IsMax M) : IsRealClosed M.carrier :=
  IsRealClosed.of_linearOrderedField
    (fun {_} hx => nonnegative_isSquare_of_isMax (F := F) M hmax hx)
    (fun {_} hp => exists_root_of_odd_natDegree_of_isMax (F := F) M hmax hp)

/-- Every ordered field has a real-closed ordered extension in the same universe.

The extension is the carrier of a maximal ordered intermediate field in an
algebraic closure; its algebra map is the canonical intermediate-field map.
@isnad1 id=orderedf.0h0v.s0.d8796b546aa3 from=translated src=- shape=45709ebd vocab=7a31378e
-/
theorem orderedFieldRealClosedExtension_same_universe :
    RatFunc.OrderedFieldRealClosedExtension.{u, u} := by
  intro F _instField _instLinearOrder _instStrictOrdered
  obtain ⟨M, _hbase, hmax, _halgebraic, hpos⟩ :=
    exists_maximal_ordered_algebraic_extension (F := F)
  let _ : IsRealClosed M.carrier := maximal_isRealClosed (F := F) M hmax
  exact ⟨M.carrier, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, hpos⟩

/-- The maximal-intermediate construction discharges the normalized-ordering
realization principle in the same universe.
@isnad1 id=normaliz.0h1v.s3.14963153f1fb from=translated src=- shape=c6850a32 vocab=3f847b70
-/
theorem normalizedOrderingRealization_of_maximal_orderedIntermediate
    {R : Type u} [Field R] :
    RatFunc.NormalizedOrderingRealization.{u, u} R :=
  RatFunc.normalizedOrderingRealization_of_orderedFieldRealClosedExtension
    orderedFieldRealClosedExtension_same_universe

end OrderedRealClosure
end RatFuncWittLocalGlobal
