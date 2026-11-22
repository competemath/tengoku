/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Tengoku

/-!
# Metric Energy Evolution
-/

@[expose] public section
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool 
noncomputable section

namespace EulerMetricEnergyEvolution

open InnerProductSpace Real

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The exact time derivative of a quadratic energy with a moving metric.
@isnad1 id=hasderiv.3h6v.s10.a6f8074d7369 from=translated src=- shape=2790c190 vocab=7d2f74f9
-/
theorem metric_energy_hasDerivAt (K : ℝ → H →L[ℝ] H) (e : ℝ → H)
    (t : ℝ) (K' : H →L[ℝ] H) (e' : H)
    (hK : HasDerivAt K K' t) (he : HasDerivAt e e' t)
    (hsym : ∀ v w, ⟪K t v, w⟫_ℝ = ⟪v, K t w⟫_ℝ) :
    HasDerivAt (fun s => ⟪K s (e s), e s⟫_ℝ)
      (⟪K' (e t), e t⟫_ℝ + 2 * ⟪K t (e t), e'⟫_ℝ) t := by
  refine ((hK.clm_apply he).inner ℝ he).congr_deriv ?_
  rw [inner_add_left, hsym e' (e t), real_inner_comm e' (K t (e t))]
  ring

/-- Cancellation of pressure and integration by parts for transport leave only
metric variation and the forcing in the time derivative.
@isnad1 id=hasderiv.5h9v.s10.f7d0cdb82034 from=translated src=- shape=8803a918 vocab=e3215272
-/
theorem metric_energy_evolution (K : ℝ → H →L[ℝ] H) (e : ℝ → H)
    (t : ℝ) (K' : H →L[ℝ] H) (e' transport pressure forcing : H)
    (hK : HasDerivAt K K' t) (he : HasDerivAt e e' t)
    (hsym : ∀ v w, ⟪K t v, w⟫_ℝ = ⟪v, K t w⟫_ℝ)
    (heq : e' + transport + pressure = forcing)
    (hp : ⟪K t (e t), pressure⟫_ℝ = 0) :
    HasDerivAt (fun s => ⟪K s (e s), e s⟫_ℝ)
      (⟪K' (e t), e t⟫_ℝ + 2 * ⟪K t (e t), forcing⟫_ℝ -
        2 * ⟪K t (e t), transport⟫_ℝ) t := by
  refine (metric_energy_hasDerivAt K e t K' e' hK he hsym).congr_deriv ?_
  have h := congrArg (fun v => ⟪K t (e t), v⟫_ℝ) heq
  simp only [inner_add_right, hp, add_zero] at h
  linarith

/--
@isnad1 id=le.2h7v.s10.ba0a757c5221 from=translated src=- shape=59e12c0c vocab=d7bda0ad
-/
theorem energy_derivative_bound (K K' : H →L[ℝ] H) (e transport forcing : H)
    (B : ℝ) (_hB : 0 ≤ B) (ht : |⟪K e, transport⟫_ℝ| ≤ B * ‖e‖ ^ 2) :
    ⟪K' e, e⟫_ℝ + 2 * ⟪K e, forcing⟫_ℝ - 2 * ⟪K e, transport⟫_ℝ ≤
      (‖K'‖ + 2 * B) * ‖e‖ ^ 2 + 2 * ‖K‖ * ‖e‖ * ‖forcing‖ := by
  have hk : ⟪K' e, e⟫_ℝ ≤ ‖K'‖ * ‖e‖ ^ 2 := by
    calc
      _ ≤ ‖K' e‖ * ‖e‖ := real_inner_le_norm _ _
      _ ≤ (‖K'‖ * ‖e‖) * ‖e‖ := by gcongr; exact K'.le_opNorm e
      _ = _ := by ring
  have hf : ⟪K e, forcing⟫_ℝ ≤ ‖K‖ * ‖e‖ * ‖forcing‖ := by
    exact (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (K.le_opNorm e) (norm_nonneg _))
  have ht' := (abs_le.mp ht).1
  linarith

/-- A positive regularization gives a differentiable metric norm even at zero.
@isnad1 id=hasderiv.5h7v.s10.a2bacc209afc from=translated src=- shape=b0ce6313 vocab=22c8bb10
-/
theorem regularized_metric_norm_hasDerivAt (K : ℝ → H →L[ℝ] H) (e : ℝ → H)
    (t δ : ℝ) (K' : H →L[ℝ] H) (e' : H)
    (hδ : 0 < δ) (hpos : 0 ≤ ⟪K t (e t), e t⟫_ℝ)
    (hK : HasDerivAt K K' t) (he : HasDerivAt e e' t)
    (hsym : ∀ v w, ⟪K t v, w⟫_ℝ = ⟪v, K t w⟫_ℝ) :
    HasDerivAt (fun s => √(⟪K s (e s), e s⟫_ℝ + δ ^ 2))
      ((⟪K' (e t), e t⟫_ℝ + 2 * ⟪K t (e t), e'⟫_ℝ) /
        (2 * √(⟪K t (e t), e t⟫_ℝ + δ ^ 2))) t := by
  exact HasDerivAt.sqrt
    ((metric_energy_hasDerivAt K e t K' e' hK he hsym).add_const (δ ^ 2)) (by nlinarith)

/-- The norm estimate used before summing Gevrey weights. All terms come from
the actual differential equation; no estimate for the energy derivative is assumed.
@isnad1 id=le.10h12v.s11.b18e68a23b9e from=translated src=- shape=c64f2f85 vocab=6e9af3f5
-/
theorem regularized_metric_norm_evolution (K : ℝ → H →L[ℝ] H) (e : ℝ → H)
    (t δ c B : ℝ) (K' : H →L[ℝ] H) (e' transport pressure forcing : H)
    (hδ : 0 < δ) (hc : 0 < c) (hB : 0 ≤ B)
    (hcoercive : c ^ 2 * ‖e t‖ ^ 2 ≤ ⟪K t (e t), e t⟫_ℝ)
    (hK : HasDerivAt K K' t) (he : HasDerivAt e e' t)
    (hsym : ∀ v w, ⟪K t v, w⟫_ℝ = ⟪v, K t w⟫_ℝ)
    (heq : e' + transport + pressure = forcing)
    (hp : ⟪K t (e t), pressure⟫_ℝ = 0)
    (ht : |⟪K t (e t), transport⟫_ℝ| ≤ B * ‖e t‖ ^ 2) :
    deriv (fun s => √(⟪K s (e s), e s⟫_ℝ + δ ^ 2)) t ≤
      ((‖K'‖ + 2 * B) / (2 * c ^ 2)) * √(⟪K t (e t), e t⟫_ℝ + δ ^ 2) +
        (‖K t‖ / c) * ‖forcing‖ := by
  let E := √(⟪K t (e t), e t⟫_ℝ + δ ^ 2)
  have hq : 0 ≤ ⟪K t (e t), e t⟫_ℝ :=
    (mul_nonneg (sq_nonneg c) (sq_nonneg ‖e t‖)).trans hcoercive
  have hE : 0 < E := sqrt_pos.2 (by nlinarith)
  have hE2 : E ^ 2 = ⟪K t (e t), e t⟫_ℝ + δ ^ 2 := sq_sqrt (by nlinarith)
  have hnorm : ‖e t‖ ≤ E / c := by
    apply (le_div_iff₀ hc).2
    nlinarith [norm_nonneg (e t)]
  have hnorm2 : ‖e t‖ ^ 2 ≤ E ^ 2 / c ^ 2 := by
    rw [← div_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hdiff := metric_energy_evolution K e t K' e' transport pressure forcing hK he hsym heq hp
  have hroot := HasDerivAt.sqrt (hdiff.add_const (δ ^ 2)) (by nlinarith :
    ⟪K t (e t), e t⟫_ℝ + δ ^ 2 ≠ 0)
  rw [hroot.deriv]
  change (_ / (2 * E)) ≤ _
  apply (div_le_iff₀ (by positivity : 0 < 2 * E)).2
  have hb := energy_derivative_bound (K t) K' (e t) transport forcing B hB ht
  have h1 := mul_le_mul_of_nonneg_left hnorm2
    (show 0 ≤ ‖K'‖ + 2 * B by positivity)
  have h2 := mul_le_mul_of_nonneg_left hnorm
    (show 0 ≤ 2 * ‖K t‖ * ‖forcing‖ by positivity)
  calc
    _ ≤ (‖K'‖ + 2 * B) * ‖e t‖ ^ 2 + 2 * ‖K t‖ * ‖e t‖ * ‖forcing‖ := hb
    _ ≤ (‖K'‖ + 2 * B) * (E ^ 2 / c ^ 2) +
        2 * ‖K t‖ * (E / c) * ‖forcing‖ := by linarith
    _ = _ := by dsimp [E]; field_simp

end EulerMetricEnergyEvolution
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
