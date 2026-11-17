import Tengoku
import Tengoku.AgrawalR5.AgrawalCore.FinalRowSize

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Submitted proofs for the independent final-row size challenge.
-/
namespace FinalRowSizeChallenge

theorem three_factor_exclusion {P q T : ℕ}
    (hP : 1 < P) (hPq : P < q ^ 2) (hqT : q ^ 2 ≤ T)
    (hrow : P ≡ 1 [MOD T] ∨ P ≡ q ^ 2 [MOD T]) : False :=
  AgrawalCore.threeFactor_finalRow_size_exclusion hP hPq hqT hrow

theorem second_product_unique {A B₁ B₂ c q T : ℕ}
    (hq : 0 < q) (hqT : q ^ 2 ≤ T) (hAT : Nat.Coprime A T)
    (hB₁ : B₁ < q ^ 2) (hB₂ : B₂ < q ^ 2)
    (h₁ : A * B₁ ≡ c [MOD T]) (h₂ : A * B₂ ≡ c [MOD T]) :
    B₁ = B₂ :=
  AgrawalCore.mitm_secondProduct_unique hq hqT hAT hB₁ hB₂ h₁ h₂

end FinalRowSizeChallenge
