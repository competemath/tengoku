/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.AumannExpectation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Aumann expectations of random balls

The Aumann expectation of a random closed ball with integrable centre and
integrable nonnegative radius is the closed ball whose centre and radius are
the corresponding integrals.  The formula holds in an arbitrary real Banach
space and does not require atomlessness.
-/

open Set Metric MeasureTheory

noncomputable section

namespace RandomSetTheory

/-- **Aumann expectation of a random closed ball.**
@isnad1 id=eq.3h5v.s7.a4c4ee239b0c from=translated src=- shape=537e5fa1 vocab=5ad993ac
-/
theorem aumannExpectation_closedBall
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} {c : Ω → E} {r : Ω → ℝ}
    (hc : Integrable c μ) (hr : Integrable r μ)
    (hrnonneg : ∀ ω, 0 ≤ r ω) :
    aumannExpectation μ (fun ω => closedBall (c ω) (r ω)) =
      closedBall (∫ ω, c ω ∂μ) (∫ ω, r ω ∂μ) := by
  have hRnonneg : 0 ≤ ∫ ω, r ω ∂μ :=
    integral_nonneg hrnonneg
  apply Set.Subset.antisymm
  · rintro x ⟨f, hf, rfl⟩
    have hdiff : Integrable (fun ω => f ω - c ω) μ := hf.1.sub hc
    have hnorm : ∀ᵐ ω ∂μ, ‖f ω - c ω‖ ≤ r ω := by
      filter_upwards [hf.2] with ω hω
      simpa [mem_closedBall, dist_eq_norm] using hω
    have hint :
        ‖∫ ω, f ω - c ω ∂μ‖ ≤ ∫ ω, r ω ∂μ :=
      norm_integral_le_of_norm_le hr hnorm
    rw [integral_sub hf.1 hc] at hint
    simpa [mem_closedBall, dist_eq_norm] using hint
  · intro x hx
    have hxnorm : ‖x - ∫ ω, c ω ∂μ‖ ≤ ∫ ω, r ω ∂μ := by
      simpa [mem_closedBall, dist_eq_norm] using hx
    by_cases hR : (∫ ω, r ω ∂μ) = 0
    · have hxcenter : x = ∫ ω, c ω ∂μ := by
        have : x - ∫ ω, c ω ∂μ = 0 :=
          norm_eq_zero.mp (le_antisymm (by simpa [hR] using hxnorm) (norm_nonneg _))
        exact sub_eq_zero.mp this
      refine ⟨c, ⟨hc, ?_⟩, ?_⟩
      · filter_upwards [] with ω
        simpa [mem_closedBall] using hrnonneg ω
      · simp [hxcenter]
    · let R : ℝ := ∫ ω, r ω ∂μ
      let u : E := R⁻¹ • (x - ∫ ω, c ω ∂μ)
      let f : Ω → E := fun ω => c ω + r ω • u
      have hRpos : 0 < R := lt_of_le_of_ne hRnonneg (Ne.symm hR)
      have hu : ‖u‖ ≤ 1 := by
        dsimp [u, R]
        rw [norm_smul, norm_inv, Real.norm_eq_abs,
          abs_of_pos hRpos, inv_mul_le_one₀ hRpos]
        exact hxnorm
      have hfint : Integrable f μ := hc.add (hr.smul_const u)
      have hfmem : ∀ ω, f ω ∈ closedBall (c ω) (r ω) := by
        intro ω
        change dist (c ω + r ω • u) (c ω) ≤ r ω
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg (hrnonneg ω)]
        exact mul_le_of_le_one_right (hrnonneg ω) hu
      refine ⟨f, ⟨hfint, Filter.Eventually.of_forall hfmem⟩, ?_⟩
      calc
        (∫ ω, f ω ∂μ) =
            (∫ ω, c ω ∂μ) + ∫ ω, r ω • u ∂μ :=
          integral_add hc (hr.smul_const u)
        _ = (∫ ω, c ω ∂μ) + R • u := by rw [integral_smul_const]
        _ = x := by
          dsimp [u]
          rw [smul_smul, mul_inv_cancel₀ hR, one_smul, add_sub_cancel]

/-- In finite dimension, the preceding exact formula immediately supplies
compactness of the unclosed Aumann expectation.
@isnad1 id=iscompac.3h5v.s7.1429d25b1160 from=translated src=- shape=579d2201 vocab=3adbd097
-/
theorem aumannExpectation_isCompact_closedBall
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {μ : Measure Ω} {c : Ω → E} {r : Ω → ℝ}
    (hc : Integrable c μ) (hr : Integrable r μ)
    (hrnonneg : ∀ ω, 0 ≤ r ω) :
    IsCompact (aumannExpectation μ (fun ω => closedBall (c ω) (r ω))) := by
  rw [aumannExpectation_closedBall hc hr hrnonneg]
  exact isCompact_closedBall _ _

/-- Hence the closure wrapper is redundant for integrable random balls in
finite dimension.
@isnad1 id=eq.3h5v.s7.9deb0bf97c77 from=translated src=- shape=53255abe vocab=df28ddae
-/
theorem closure_aumannExpectation_closedBall
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    {μ : Measure Ω} {c : Ω → E} {r : Ω → ℝ}
    (hc : Integrable c μ) (hr : Integrable r μ)
    (hrnonneg : ∀ ω, 0 ≤ r ω) :
    closure (aumannExpectation μ (fun ω => closedBall (c ω) (r ω))) =
      aumannExpectation μ (fun ω => closedBall (c ω) (r ω)) :=
  (aumannExpectation_isCompact_closedBall hc hr hrnonneg).isClosed.closure_eq

end RandomSetTheory
