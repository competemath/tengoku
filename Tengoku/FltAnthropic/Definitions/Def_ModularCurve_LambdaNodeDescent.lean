import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LambdaNodeLocalized
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_NodeDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace ModularCurve
namespace LambdaNodeLocalized
noncomputable section

open NodeLocalized

def lambdaFieldOver (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Subfield (LaurentSeries (AlgebraicClosure ℚ)) :=
  Subfield.closure (Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring)
    ∪ {lambdaModC (AlgebraicClosure ℚ), lambdaNModC (AlgebraicClosure ℚ) N})

def lambdaRing (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Subring (LaurentSeries (AlgebraicClosure ℚ)) :=
  Subring.closure (Set.range (CharPReduction.constSeries (coeffSubring A K)) ∪ {lambdaModC (AlgebraicClosure ℚ)})

def lambdaIntegralClosure (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    Subring (LaurentSeries (AlgebraicClosure ℚ)) where
  carrier := {x | x ∈ lambdaFieldOver N K ∧ IsIntegral (lambdaRing A K) x}
  zero_mem' := ⟨zero_mem _, isIntegral_zero⟩
  one_mem' := ⟨one_mem _, isIntegral_one⟩
  add_mem' := fun hx hy => ⟨add_mem hx.1 hy.1, hx.2.add hy.2⟩
  neg_mem' := fun hx => ⟨neg_mem hx.1, hx.2.neg⟩
  mul_mem' := fun hx hy => ⟨mul_mem hx.1 hy.1, hx.2.mul hy.2⟩

/--
@isnad1 id=iff.0h4v.s10.fbb253c4cd5b from=translated src=- shape=a3c9e52e vocab=0308f773
-/
theorem mem_lambdaIntegralClosure (N : ℕ) [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) {x : LaurentSeries (AlgebraicClosure ℚ)} :
    x ∈ lambdaIntegralClosure N A K ↔ x ∈ lambdaFieldOver N K ∧ IsIntegral (lambdaRing A K) x :=
  Iff.rfl

/--
@isnad1 id=mem.0h2v.s8.d67c0f31a448 from=translated src=- shape=242104fa vocab=341fe9e5
-/
theorem lambdaModC_mem_lambdaFieldOver (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    lambdaModC (AlgebraicClosure ℚ) ∈ lambdaFieldOver N K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert _ _))

/--
@isnad1 id=mem.0h2v.s8.afb8bda52fe3 from=translated src=- shape=4819db07 vocab=abab5342
-/
theorem lambdaNModC_mem_lambdaFieldOver (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    lambdaNModC (AlgebraicClosure ℚ) N ∈ lambdaFieldOver N K :=
  Subfield.subset_closure (Or.inr (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end
end LambdaNodeLocalized
end ModularCurve
