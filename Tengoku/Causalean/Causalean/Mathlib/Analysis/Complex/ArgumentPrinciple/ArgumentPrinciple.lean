/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module

public import Tengoku.Causalean.Causalean.Mathlib.Analysis.Complex.ArgumentPrinciple.Basic

/-!
# The argument principle for a positively oriented circle

This module proves the circle argument principle: the normalized
logarithmic-derivative integral equals the multiplicity-weighted number of
zeros strictly inside the disk. It also records its integrality and positivity
consequences.
-/

@[expose] public section

noncomputable section

open Filter Function Metric Set
open scoped Topology

namespace Causalean.Mathlib.Analysis.Complex.ArgumentPrinciple

/-- A complex function analytic on a neighborhood of a closed disk and nonzero on its boundary
has only finitely many zeros strictly inside that disk. -/
theorem finite_interiorZeros {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0) :
    (interiorZeros f c R).Finite := by
  let w : ℂ := c + R
  have hwS : w ∈ sphere c R := by simp [w, abs_of_pos hR]
  have hwC : w ∈ closedBall c R := sphere_subset_closedBall hwS
  have hmw : meromorphicOrderAt f w ≠ ⊤ := by
    rw [(hf w hwC).meromorphicOrderAt_eq,
      (hf w hwC).analyticOrderAt_eq_zero.2 (hboundary w hwS)]
    simp
  have hfinite : ∀ z ∈ closedBall c R, meromorphicOrderAt f z ≠ ⊤ :=
    fun z hz ↦ hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c R).isPreconnected hwC hz hmw
  apply ((MeromorphicOn.divisor f (closedBall c R)).finiteSupport
    (isCompact_closedBall c R)).subset
  intro z hz
  rcases hz with ⟨hzball, hzf⟩
  have hzC : z ∈ closedBall c R := ball_subset_closedBall hzball
  have hmzero : meromorphicOrderAt f z ≠ 0 := by
    rw [(hf z hzC).meromorphicOrderAt_eq]
    simpa using (hf z hzC).analyticOrderAt_ne_zero.2 hzf
  rw [Function.mem_support, MeromorphicOn.divisor_apply hf.meromorphicOn hzC]
  intro h
  rw [WithTop.untop₀_eq_zero] at h
  exact h.elim hmzero (hfinite z hzC)

open Classical in
/-- Under disk analyticity and boundary nonvanishing, the function assigning each interior zero
its analytic multiplicity and all other points zero has finite support. -/
theorem finiteSupport_orderWithinBall {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0) :
    Function.HasFiniteSupport
      (fun z : ℂ ↦ if z ∈ ball c R then analyticOrderNatAt f z else 0) := by
  apply (finite_interiorZeros hR hf hboundary).subset
  intro z hz
  rw [Function.mem_support] at hz
  by_cases hzb : z ∈ ball c R
  · exact ⟨hzb, apply_eq_zero_of_analyticOrderNatAt_ne_zero (by simpa [hzb] using hz)⟩
  · simp [hzb] at hz

/-- A boundary-zero-free analytic function that vanishes somewhere strictly inside the disk has
a strictly positive multiplicity-weighted interior zero count. -/
theorem zeroMultiplicityCount_pos_of_exists_zero {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0)
    (hzero : ∃ z ∈ ball c R, f z = 0) :
    0 < zeroMultiplicityCount f c R := by
  classical
  rcases hzero with ⟨z, hzball, hzf⟩
  let w : ℂ := c + R
  have hwS : w ∈ sphere c R := by simp [w, abs_of_pos hR]
  have hwC : w ∈ closedBall c R := sphere_subset_closedBall hwS
  have hmw : meromorphicOrderAt f w ≠ ⊤ := by
    rw [(hf w hwC).meromorphicOrderAt_eq,
      (hf w hwC).analyticOrderAt_eq_zero.2 (hboundary w hwS)]
    simp
  have hzC : z ∈ closedBall c R := ball_subset_closedBall hzball
  have hmfinite : meromorphicOrderAt f z ≠ ⊤ :=
    hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c R).isPreconnected hwC hzC hmw
  have hafinite : analyticOrderAt f z ≠ ⊤ := by
    rw [(hf z hzC).meromorphicOrderAt_eq] at hmfinite
    simpa using hmfinite
  have hzpos : 0 < analyticOrderNatAt f z := Nat.pos_of_ne_zero fun hz0 ↦ by
    have := (hf z hzC).analyticOrderAt_ne_zero.2 hzf
    apply this
    rw [← Nat.cast_analyticOrderNatAt hafinite, hz0]
    rfl
  unfold zeroMultiplicityCount
  apply finsum_pos
  · intro u
    positivity
  · exact ⟨z, by simpa [hzball]⟩
  · exact finiteSupport_orderWithinBall hR hf hboundary

end Causalean.Mathlib.Analysis.Complex.ArgumentPrinciple
