import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.HigherDimensionalAsymptotic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Main result for burning path-token configurations

This file packages the five parts of the main theorem as compact public
wrappers.
-/

open Asymptotics Filter Topology

namespace BurningPath

/--
Part (A): the exact finite ranked-volume lower bound and its fixed-dimensional
explicit-constant liminf consequence.-/
theorem burningPathToken_partA (k : ℕ) (hk : 2 ≤ k) :
    (∀ {n : ℕ} (hnk : k + 1 ≤ n),
      volumeThreshold k (n.choose k) ≤
        pathTokenBurningNumber n k ((Nat.le_add_right k 1).trans hnk)) ∧
      (((k + 1 : ℝ) / (2 : ℝ) ^ k) ^ (k + 1 : ℝ)⁻¹) ≤
        liminf
          (fun n : ℕ ↦
            (pathTokenBurningNumberTotal k n : ℝ) /
              (n : ℝ) ^ ((k : ℝ) / (k + 1 : ℝ)))
          atTop := by
  constructor
  · intro n hnk
    exact pathToken_volumeThreshold_lower hnk
  · have hlimit := generalLowerAsymptotic_real_liminf k hk
    have hfun :
        pathTokenBurningRatio k =
          fun n : ℕ ↦
            (pathTokenBurningNumberTotal k n : ℝ) /
              (n : ℝ) ^ ((k : ℝ) / (k + 1 : ℝ)) := by
      funext n
      rw [pathTokenBurningRatio, pathTokenAsymptoticScale_eq_rpow]
    rw [hfun] at hlimit
    simpa only [volumeLowerConstant, volumeLowerPowerConstant] using hlimit

/--
Part (B): the exact finite optimal block upper bound and its
fixed-dimensional explicit-constant limsup consequence.-/
theorem burningPathToken_partB (k : ℕ) (hk : 2 ≤ k) :
    (∀ {n : ℕ} (hnk : k + 1 ≤ n),
      pathTokenBurningNumber n k ((Nat.le_add_right k 1).trans hnk) ≤
        optimalBlockUpperBound n k) ∧
      limsup
          (fun n : ℕ ↦
            (pathTokenBurningNumberTotal k n : ℝ) /
              (n : ℝ) ^ ((k : ℝ) / (k + 1 : ℝ)))
          atTop ≤
        (k + 1 : ℝ) /
          (k.factorial : ℝ) ^ (k + 1 : ℝ)⁻¹ := by
  constructor
  · intro n hnk
    exact pathTokenBurningNumber_le_optimalBlockUpperBound hnk
  · exact generalUpperAsymptotic_limsup k hk

/-- Part (C): the fixed-dimensional `Θ` estimate on the standard scale.-/
theorem burningPathToken_partC (k : ℕ) (hk : 2 ≤ k) :
    (fun n ↦ (pathTokenBurningNumberTotal k n : ℝ)) =Θ[atTop]
      pathTokenStandardScale k :=
  pathTokenBurning_isTheta_standardScale k hk

/--
Part (D): the exact two-token cubic threshold, the sharp normalized limit,
and the equivalent asymptotic expansion.-/
theorem burningPathToken_partD :
    (∀ {n : ℕ} (hn : 2 ≤ n),
      twoTokenCubicThreshold (n.choose 2) ≤
        pathTokenBurningNumber n 2 hn) ∧
      Tendsto
          (fun n : ℕ ↦
            (pathTokenBurningNumberTotal 2 n : ℝ) /
              (n : ℝ) ^ (2 / 3 : ℝ))
          atTop (𝓝 ((3 / 4 : ℝ) ^ (3 : ℝ)⁻¹)) ∧
      (fun n : ℕ ↦ (pathTokenBurningNumberTotal 2 n : ℝ)) ~[atTop]
        (fun n : ℕ ↦
          ((3 / 4 : ℝ) ^ (3 : ℝ)⁻¹) *
            (n : ℝ) ^ (2 / 3 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    exact twoTokenCubicThreshold_lower hn
  · change Tendsto twoTokenNormalizedBurning atTop (𝓝 shelfSharpConstant)
    exact tendsto_twoTokenNormalizedBurning
  · simpa only [shelfSharpConstant] using
      twoTokenBurning_isEquivalent_sharp

end BurningPath
