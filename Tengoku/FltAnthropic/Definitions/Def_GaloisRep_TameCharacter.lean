import Tengoku.Seed.RingTheory.Valuation.ValuationSubring
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.Algebra.Algebra.Rat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace ValuationSubring

noncomputable def tameCharacter (P : ValuationSubring (AlgebraicClosure ℚ)) (π : AlgebraicClosure ℚ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : IsLocalRing.ResidueField P := by
  classical
  exact if h : σ π / π ∈ P then IsLocalRing.residue P ⟨σ π / π, h⟩ else 0

end ValuationSubring
