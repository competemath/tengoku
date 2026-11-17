import Tengoku
import Tengoku.AgrawalR5.AgrawalCore.FinalRowSize

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Submitted proofs for the independent final-row size challenge.
-/
namespace FinalRowSizeChallenge

/--
@isnad1 id=false.4h3v.s6.0ccd6060a2d2 from=translated src=- shape=18f32aef vocab=137ffae1
-/
theorem three_factor_exclusion {P q T : ℕ}
    (hP : 1 < P) (hPq : P < q ^ 2) (hqT : q ^ 2 ≤ T)
    (hrow : P ≡ 1 [MOD T] ∨ P ≡ q ^ 2 [MOD T]) : False :=
  AgrawalCore.threeFactor_finalRow_size_exclusion hP hPq hqT hrow

/--
@isnad1 id=eq.7h6v.s6.7d0d497e0d56 from=translated src=- shape=c85780c4 vocab=28d41342
-/
theorem second_product_unique {A B₁ B₂ c q T : ℕ}
    (hq : 0 < q) (hqT : q ^ 2 ≤ T) (hAT : Nat.Coprime A T)
    (hB₁ : B₁ < q ^ 2) (hB₂ : B₂ < q ^ 2)
    (h₁ : A * B₁ ≡ c [MOD T]) (h₂ : A * B₂ ≡ c [MOD T]) :
    B₁ = B₂ :=
  AgrawalCore.mitm_secondProduct_unique hq hqT hAT hB₁ hB₂ h₁ h₂

end FinalRowSizeChallenge
