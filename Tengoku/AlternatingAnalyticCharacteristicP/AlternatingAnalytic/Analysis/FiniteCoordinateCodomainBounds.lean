import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.FiniteCoordinateDeterminant
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.LiftCriterion
import Tengoku.Seed.LinearAlgebra.ExteriorPower.Basis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Norm bounds for the codomain determinant lift

The triangle-inequality bound for the determinant lift of Proposition 4.1(2), with an
explicit real constant `finiteCoordinateCodomainBound`.
-/

noncomputable section

namespace AlternatingAnalytic

open scoped BigOperators
open Module

variable {K E E' F : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F]
  {d : ℕ}

/-- A coordinate functional of `b`, as a continuous linear map.-/
def finiteCoordinateCodomainFunctional (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (i : Fin d) : E' →L[K] K :=
  ⟨b.coord i, hb i⟩

@[simp] theorem finiteCoordinateCodomainFunctional_apply (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (i : Fin d) (x : E') :
    finiteCoordinateCodomainFunctional b hb i x = b.coord i x := rfl

/-- The norm constant of the codomain determinant lift.-/
def finiteCoordinateCodomainBound (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * ∑ s : Set.powersetCard (Fin d) k,
    ∏ a : Fin k,
      (‖finiteCoordinateCodomainFunctional b hb (Set.powersetCard.ofFinEmbEquiv.symm s a)‖ *
        ‖b (Set.powersetCard.ofFinEmbEquiv.symm s a)‖)

theorem finiteCoordinateCodomainBound_nonneg (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) (k : ℕ) :
    0 ≤ finiteCoordinateCodomainBound b hb k := by
  unfold finiteCoordinateCodomainBound
  positivity

/-- There are no `k`-element subsets of `Fin d` when `d < k`.-/
theorem finiteCoordinateCodomainIndices_isEmpty {d k : ℕ} (h : d < k) :
    IsEmpty (Set.powersetCard (Fin d) k) := by
  refine ⟨fun s => ?_⟩
  have hs : k ≤ d := by
    have hc := Finset.card_le_univ s.val
    simpa only [Set.powersetCard.card_eq, Fintype.card_fin] using hc
  omega

theorem finiteCoordinateCodomainBound_eq_zero_of_lt (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) {k : ℕ} (h : d < k) :
    finiteCoordinateCodomainBound b hb k = 0 := by
  let := finiteCoordinateCodomainIndices_isEmpty h
  simp [finiteCoordinateCodomainBound]

theorem finiteCoordinateCodomainBound_zero (b : Basis (Fin d) K E')
    (hb : ∀ i, Continuous (b.coord i)) : finiteCoordinateCodomainBound b hb 0 = 1 := by
  let : Unique (Set.powersetCard (Fin d) 0) :=
    ⟨⟨∅, rfl⟩, fun s => Subtype.ext (Finset.card_eq_zero.mp s.prop)⟩
  simp [finiteCoordinateCodomainBound]

end AlternatingAnalytic
