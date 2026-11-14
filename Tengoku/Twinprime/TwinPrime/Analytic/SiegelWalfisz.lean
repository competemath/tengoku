import Tengoku.Twinprime.TwinPrime.Analytic.CharacterMaximal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit uniform centered Siegel--Walfisz statements

Both propositions include primitive conductor one and quantify all real
logarithmic exponents and uniform constants. They are definitions, not
axioms or proofs of prime distribution.
-/

noncomputable section

namespace TwinPrime.Analytic

/-- A uniform centered character estimate at the stated endpoint.-/
def PointwiseSiegelWalfisz : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ C : ℝ, 0 < C ∧
    ∃ T₀ : ℕ, 2 ≤ T₀ ∧ ∀ T : ℕ, T₀ ≤ T → ∀ r : ℕ, 1 ≤ r →
      (r : ℝ) ≤ (Real.log T) ^ B → ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive →
        ‖centeredCharacterPsi T χ‖ ≤ C * T / (Real.log T) ^ A

/-- The same uniform estimate for all natural endpoints through `T`.-/
def MaximalSiegelWalfisz : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ C : ℝ, 0 < C ∧
    ∃ T₀ : ℕ, 2 ≤ T₀ ∧ ∀ T : ℕ, T₀ ≤ T → ∀ r : ℕ, 1 ≤ r →
      (r : ℝ) ≤ (Real.log T) ^ B → ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive →
        characterMaxError T χ ≤ C * T / (Real.log T) ^ A

end TwinPrime.Analytic
