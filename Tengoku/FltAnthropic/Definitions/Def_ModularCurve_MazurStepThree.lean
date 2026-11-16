import Tengoku.FltAnthropic.Definitions.Def_EllipticCurve_ZeroComponentAt
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine in

def MazurStepThree (p : ℕ) : Prop :=
  p.Prime → p ∉ ({2, 3, 5, 7, 13} : Finset ℕ) →
  ∀ (W : WeierstrassCurve ℤ), W.Δ ≠ 0 →
    (∀ q : ℕ, q.Prime → (q : ℤ) ∣ W.Δ → ¬ (q : ℤ) ∣ W.c₄) →
    ∀ (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point),
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q) →
      addOrderOf Q = p →
      (2 : ℤ) ∣ W.Δ →
      (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 2 →
        ¬ W.InZeroComponentAt A Q) →
      (3 : ℤ) ∣ W.Δ →
      (∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 →
        ¬ W.InZeroComponentAt A Q) →
      ∀ (ℓ : ℕ), ℓ.Prime → ℓ ≠ 2 → ℓ ≠ 3 → ℓ ≠ p → (ℓ : ℤ) ∣ W.Δ →
        ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
          ¬ W.InZeroComponentAt A Q
