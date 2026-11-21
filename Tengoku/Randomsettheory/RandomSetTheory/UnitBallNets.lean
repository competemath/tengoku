/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite nets of finite-dimensional unit balls

The centres of the net are retained inside the unit ball.  This seemingly
minor strengthening is the form needed by directional support-function
concentration inequalities.
-/

open Set Metric

noncomputable section

namespace RandomSetTheory

/-- Every positive scale admits a finite strict net of the closed unit ball,
whose centres also belong to the closed unit ball.
@isnad1 id=ex.1h2v.s7.24caac9c2a36 from=translated src=- shape=5e8fef1d vocab=653242af
-/
theorem exists_finset_unitBall_net_with_centers
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset E,
      (∀ v ∈ N, ‖v‖ ≤ 1) ∧
      ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v < ε := by
  classical
  obtain ⟨t, htunit, htfinite, hcover⟩ :=
    finite_cover_balls_of_compact
      (isCompact_closedBall (0 : E) 1) hε
  refine ⟨htfinite.toFinset, ?_, ?_⟩
  · intro v hv
    have hvt : v ∈ t := by simpa using hv
    have hvball := htunit hvt
    simpa [mem_closedBall, dist_zero_right] using hvball
  · intro u hu
    have hu' : u ∈ closedBall (0 : E) 1 := by
      simpa [mem_closedBall, dist_zero_right] using hu
    obtain ⟨v, hvt, huv⟩ := Set.mem_iUnion₂.mp (hcover hu')
    exact ⟨v, by simpa using hvt, by simpa [mem_ball] using huv⟩

/-- Non-strict version of `exists_finset_unitBall_net_with_centers`.
@isnad1 id=ex.1h2v.s7.d4243abb0a95 from=translated src=- shape=88b25611 vocab=653242af
-/
theorem exists_finset_unitBall_closedNet_with_centers
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset E,
      (∀ v ∈ N, ‖v‖ ≤ 1) ∧
      ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ ε := by
  obtain ⟨N, hN, hnet⟩ :=
    exists_finset_unitBall_net_with_centers (E := E) hε
  exact ⟨N, hN, fun u hu => by
    obtain ⟨v, hv, huv⟩ := hnet u hu
    exact ⟨v, hv, huv.le⟩⟩

end RandomSetTheory
