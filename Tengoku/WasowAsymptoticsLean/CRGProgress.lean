import Tengoku.WasowAsymptoticsLean.CRGRay
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Tengoku.Seed.MeasureTheory.Integral.IntegralEqImproper
import Tengoku.Seed.Analysis.Calculus.Deriv.Mul
import Tengoku.Seed.Topology.Instances.Matrix

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms eventually_det_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms polynomial_exp_integrable` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms perturbation_integrable` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_small_tail` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms gauge_cancellation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms conjugated_perturbation_bound` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms derivative_of_gauged_vector` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Additional checked steps in the manuscript's ray reduction.
This module does not prove the rational-system normal-form theorem,
Gundersen's estimate, or the global CRG criterion.
-/
open Filter MeasureTheory Set
open scoped Topology
namespace CRGProgress

/-- A polynomially weighted exponential is integrable on the positive half-line.
Only K > -1 is needed at zero; on a ray tail one may enlarge K to a nonnegative one.
@isnad1 id=integrab.2h3v.s6.a617f58c3944 from=translated src=- shape=4e77eab7 vocab=b56e25ae
-/
theorem polynomial_exp_integrable (K c C : ℝ) (hK : -1 < K) (hc : 0 < c) :
    IntegrableOn (fun r : ℝ => C * (r ^ K * Real.exp (-c * r))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := K) (p := 1) hK (by norm_num) hc
  simpa only [Real.rpow_one, IntegrableOn] using h.const_mul C

/-- The actual perturbation is L1 when its norm has the claimed exponential bound.
@isnad1 id=integrab.5h6v.s7.f3e0b85b4899 from=translated src=- shape=545e317a vocab=dd792e0c
-/
theorem perturbation_integrable {E : Type*} [NormedAddCommGroup E]
    (R : ℝ → E) (K c C r₀ : ℝ) (hK : -1 < K) (hc : 0 < c) (hr₀ : 0 ≤ r₀)
    (hmeas : AEStronglyMeasurable R (volume.restrict (Ioi r₀)))
    (hbound : ∀ᵐ r ∂volume.restrict (Ioi r₀),
      ‖R r‖ ≤ C * (r ^ K * Real.exp (-c * r))) :
    IntegrableOn R (Ioi r₀) := by
  exact ((polynomial_exp_integrable K c C hK hc).mono_set
    (Ioi_subset_Ioi hr₀)).mono' hmeas hbound

/-- Choosing a large starting radius makes the L1 tail smaller than any tolerance.
@isnad1 id=ex.2h4v.s6.5e10d441479e from=translated src=- shape=89e4c705 vocab=2de50564
-/
theorem exists_small_tail {E : Type*} [NormedAddCommGroup E]
    (R : ℝ → E) (r₀ ε : ℝ) (_hR : IntegrableOn R (Ioi r₀)) (hε : 0 < ε) :
    ∃ a ≥ r₀, (∫ r in Ioi a, ‖R r‖) < ε := by
  have hlim : Tendsto (fun a : ℝ => ∫ r in Ioi a, ‖R r‖) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  have hsmall := hlim.eventually (gt_mem_nhds hε)
  obtain ⟨a, ha, hsmall⟩ := (hsmall.and (eventually_ge_atTop r₀)).exists
  exact ⟨a, hsmall, ha⟩

/-- Exact gauge cancellation for possibly noncommuting operators. The order of
T, its inverse S, A, and E is preserved throughout.
@isnad1 id=eq.3h9v.s11.5dea412ed562 from=translated src=- shape=f34a8c56 vocab=ae314c3a
-/
theorem gauge_cancellation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T S A D T' P : E →L[ℂ] E) (z z' : E)
    (hST : S.comp T = ContinuousLinearMap.id ℂ E)
    (hgauge : S.comp (A.comp T) - S.comp T' = D)
    (hsystem : T' z + T z' = A (T z) + P (T z)) :
    z' = D z + S (P (T z)) := by
  have hSTz : S (T z') = z' := by
    simpa using congrArg (fun L : E →L[ℂ] E => L z') hST
  have hDz : S (A (T z)) - S (T' z) = D z := by
    simpa using congrArg (fun L : E →L[ℂ] E => L z) hgauge
  have hx := congrArg S hsystem
  simp only [map_add] at hx
  rw [hSTz] at hx
  calc
    z' = (S (A (T z)) + S (P (T z))) - S (T' z) := by
      simpa only [add_sub_cancel_left] using congrArg (fun v => v - S (T' z)) hx
    _ = (S (A (T z)) - S (T' z)) + S (P (T z)) := by abel
    _ = _ := by rw [hDz]

/-- Operator norms supply the polynomial loss in the conjugated perturbation.
@isnad1 id=le.0h4v.s9.a348807c6ef8 from=translated src=- shape=2f4fbdb8 vocab=a2362292
-/
theorem conjugated_perturbation_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T S P : E →L[ℂ] E) :
    ‖S.comp (P.comp T)‖ ≤ ‖S‖ * ‖P‖ * ‖T‖ := by
  calc
    ‖S.comp (P.comp T)‖ ≤ ‖S‖ * ‖P.comp T‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖S‖ * (‖P‖ * ‖T‖) := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

/-- A genuine derivative product rule supplies the equation used by the algebraic
cancellation theorem. No derivative identity is hidden in a normal-form interface.
@isnad1 id=hasderiv.2h6v.s9.ff595dc240d8 from=translated src=- shape=6413653d vocab=5deb790c
-/
theorem derivative_of_gauged_vector {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ → E →L[ℝ] E) (z : ℝ → E) (T' : E →L[ℝ] E) (z' : E) (r : ℝ)
    (hT : HasDerivAt T T' r) (hz : HasDerivAt z z' r) :
    HasDerivAt (fun s => T s (z s)) (T' (z r) + T r z') r := by
  exact hT.clm_apply hz

/-- The normalized matrix is eventually nonsingular once its entries converge to I.
This is the actual last invertibility step of the mixed-integral construction.
@isnad1 id=eventual.1h4v.s6.4de00ed26b82 from=translated src=- shape=3620291b vocab=44f0d5d8
-/
theorem eventually_det_ne_zero {α : Type*} {l : Filter α} (m : ℕ)
    (U : α → Matrix (Fin m) (Fin m) ℂ) (hU : Tendsto U l (𝓝 1)) :
    ∀ᶠ r in l, (U r).det ≠ 0 := by
  have hd : Continuous (fun M : Matrix (Fin m) (Fin m) ℂ => M.det) :=
    continuous_id.matrix_det
  have hlim : Tendsto (fun r => (U r).det) l (𝓝 (1 : ℂ)) := by
    simpa only [Matrix.det_one, Function.comp_def] using (hd.tendsto 1).comp hU
  exact hlim.eventually (eventually_ne_nhds (one_ne_zero : (1 : ℂ) ≠ 0))

end CRGProgress
