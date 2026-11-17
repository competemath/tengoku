import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proof of Lemma A.3

Uses Mathlib's `LinearMap.toContinuousLinearMap` and `FiniteDimensional.complete`.
-/

namespace AlternatingAnalyticChallenge.LemA_3

/-- Every linear functional on `U` is bounded.
@isnad1 id=ex.0h3v.s8.e09b6372ac84 from=translated src=- shape=b0be2840 vocab=17c09bae
-/
theorem part1_linearFunctional_bounded
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (U : Type*) [NormedAddCommGroup U] [NormedSpace K U] [FiniteDimensional K U] :
    ∀ g : U →ₗ[K] K, ∃ C : ℝ, ∀ x : U, ‖g x‖ ≤ C * ‖x‖ := by
  intro g
  exact ⟨‖LinearMap.toContinuousLinearMap g‖,
    fun x => (LinearMap.toContinuousLinearMap g).le_opNorm x⟩

/-- `U` is complete.
@isnad1 id=complete.0h2v.s6.a774cca2fec7 from=translated src=- shape=301fdfde vocab=ba2c3cb0
-/
theorem part2_completeSpace
    (K : Type*) [NontriviallyNormedField K] [CompleteSpace K]
    (U : Type*) [NormedAddCommGroup U] [NormedSpace K U] [FiniteDimensional K U] :
    CompleteSpace U := by
  exact FiniteDimensional.complete K U

end AlternatingAnalyticChallenge.LemA_3
