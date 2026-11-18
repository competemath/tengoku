import Tengoku.WasowAsymptoticsLean.NormalFormGoal
import Tengoku.Seed.Topology.Instances.Matrix
import Tengoku.Seed.Analysis.Normed.Group.Continuity
import Tengoku.Seed.Analysis.Matrix.Normed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms WasowMatrixBounds.mulVec_norm_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowMatrixBounds.tendsto_inv_of_tendsto_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowMatrixBounds.eventually_det_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowMatrixBounds.eventually_inverse_identities` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowMatrixBounds.eventually_uniform_mulVec_bounds` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Tail bounds for matrices converging to the identity.  Matrix inversion is the
actual nonsingular inverse.  The convergence hypothesis supplies eventual
nonsingularity as well as a common bound on the matrix and its inverse.
The norm estimate is proved for the entrywise supremum norm and does
not assume that this matrix norm is submultiplicative.
-/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology BigOperators
open scoped Matrix.Norms.Elementwise

namespace WasowMatrixBounds

/--
@isnad1 id=le.0h3v.s7.fcbd2559b2f8 from=translated src=- shape=61bcd7cc vocab=e1fbbae9
-/
theorem mulVec_norm_le {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ) :
    ‖M.mulVec x‖ ≤ (m : ℝ) * ‖M‖ * ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc
    ‖M.mulVec x i‖ = ‖∑ j, M i j * x j‖ := rfl
    _ ≤ ∑ j, ‖M i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin m, ‖M‖ * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul
        ((norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i))
        (norm_le_pi_norm x j) (norm_nonneg _) (norm_nonneg _)
    _ = (m : ℝ) * ‖M‖ * ‖x‖ := by simp [mul_assoc]

/--
@isnad1 id=tendsto.1h4v.s7.7c8f0330b541 from=translated src=- shape=df05cd55 vocab=2d3af796
-/
theorem tendsto_inv_of_tendsto_one {α : Type*} {m : ℕ} {l : Filter α}
    {U : α → Matrix (Fin m) (Fin m) ℂ}
    (hU : Tendsto U l (𝓝 1)) :
    Tendsto (fun r => (U r)⁻¹) l (𝓝 1) := by
  have hinv : ContinuousAt (Inv.inv : Matrix (Fin m) (Fin m) ℂ → _) 1 :=
    continuousAt_matrix_inv 1 (by
      rw [Matrix.det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero)
  simpa [Function.comp_def] using hinv.tendsto.comp hU

/--
@isnad1 id=eventual.1h4v.s6.a116d12f6c36 from=translated src=- shape=8de7b827 vocab=44f0d5d8
-/
theorem eventually_det_ne_zero {α : Type*} {m : ℕ} {l : Filter α}
    {U : α → Matrix (Fin m) (Fin m) ℂ}
    (hU : Tendsto U l (𝓝 1)) :
    ∀ᶠ r in l, (U r).det ≠ 0 := by
  have hdet : Tendsto (fun r => (U r).det) l (𝓝 1) := by
    simpa [Function.comp_def] using continuous_id.matrix_det.continuousAt.tendsto.comp hU
  exact hdet.eventually_ne one_ne_zero

/--
@isnad1 id=eventual.1h4v.s7.15a5bb240c60 from=translated src=- shape=463fa81f vocab=069571fe
-/
theorem eventually_inverse_identities {α : Type*} {m : ℕ} {l : Filter α}
    {U : α → Matrix (Fin m) (Fin m) ℂ}
    (hU : Tendsto U l (𝓝 1)) :
    ∀ᶠ r in l, (U r)⁻¹ * U r = 1 ∧ U r * (U r)⁻¹ = 1 := by
  filter_upwards [eventually_det_ne_zero hU] with r hr
  exact ⟨Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hr),
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hr)⟩

/-- A single constant controls both operators on one common tail.
@isnad1 id=ex.1h4v.s8.7cc28f557513 from=translated src=- shape=254755ff vocab=ddfbde3c
-/
theorem eventually_uniform_mulVec_bounds {α : Type*} {m : ℕ} {l : Filter α}
    {U : α → Matrix (Fin m) (Fin m) ℂ}
    (hU : Tendsto U l (𝓝 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in l,
      (U r)⁻¹ * U r = 1 ∧ U r * (U r)⁻¹ = 1 ∧
      (∀ x : Fin m → ℂ, ‖(U r).mulVec x‖ ≤ C * ‖x‖) ∧
      (∀ x : Fin m → ℂ, ‖((U r)⁻¹).mulVec x‖ ≤ C * ‖x‖) := by
  let B : ℝ := ‖(1 : Matrix (Fin m) (Fin m) ℂ)‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hUb : ∀ᶠ r in l, ‖U r‖ < B := hU.norm.eventually (gt_mem_nhds (by
    dsimp [B]; linarith))
  have hVb : ∀ᶠ r in l, ‖(U r)⁻¹‖ < B :=
    (tendsto_inv_of_tendsto_one hU).norm.eventually (gt_mem_nhds (by
      dsimp [B]; linarith))
  refine ⟨((m : ℝ) + 1) * B, mul_pos (by positivity) hB, ?_⟩
  filter_upwards [eventually_inverse_identities hU, hUb, hVb] with r hr hUr hVr
  refine ⟨hr.1, hr.2, ?_, ?_⟩
  · intro x
    refine (mulVec_norm_le (U r) x).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    exact mul_le_mul (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)
      hUr.le (norm_nonneg _) (by positivity)
  · intro x
    refine (mulVec_norm_le ((U r)⁻¹) x).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    exact mul_le_mul (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)
      hVr.le (norm_nonneg _) (by positivity)

end WasowMatrixBounds

