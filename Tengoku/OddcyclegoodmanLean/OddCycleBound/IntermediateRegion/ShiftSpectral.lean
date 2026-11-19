import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.DirectedKernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.DenseRegion
open OddCycleBound.Spectral
open OddCycleBound.Spectral.InfiniteSpectral

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

/--
@isnad1 id=eq.0h4v.s7.86a0a0a18fb2 from=translated src=- shape=558664ef vocab=94c13b2c
-/
lemma linearIter_toLinearMap_eq_opIter
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →L[Real] E) (n : Nat) (v : E) :
    linearIter T.toLinearMap n v = opIter T n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change T (linearIter T.toLinearMap n v) = T (opIter T n v)
      rw [ih]

noncomputable def centeredReturnQuadratic
    (hW : IsGraphon W mu) (p : Real) (m : Nat) (v : Lp Real 2 mu) : Real :=
  p ^ (m - 2) * inner Real v v +
    ∑ k ∈ Finset.range (m - 2),
      p ^ (m - 3 - k) *
        inner Real v (opIter (centeredGraphonOp hW) (k + 1) v)

end OddCycleBound.IntermediateRegion
