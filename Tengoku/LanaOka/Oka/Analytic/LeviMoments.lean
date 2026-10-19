/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Analysis.Meromorphic.Basic
import Tengoku.Seed.Algebra.Polynomial.Roots
import Tengoku.LanaOka.Oka.Analytic.Laurent.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Moments of meromorphic functions on a disc

This file collects the one-variable facts behind the extension of meromorphic functions across
sets of codimension two.

The *moments* of `f` on the circle of radius `ρ` are the integrals `∮_{‖z‖ = ρ} z ^ k f z dz`,
`k ≥ 0`. They are the Laurent coefficients of negative degree of `f`, so they all vanish if and
only if `f` has no principal part on the annulus. If `f` is meromorphic on a closed disc, a
polynomial `p` vanishing at the poles of `f` to high enough order makes `p * f` holomorphic on
the disc, so all moments of `p * f` vanish.

## Main results

- `Laurent.cauchyIntegral_eq_of_forall_moment_eq_zero`: if all moments of `f` vanish on a circle
  in an annulus on which `f` is holomorphic, then the Cauchy integral of `f` over this circle is
  `f` on the part of the annulus inside the circle.
- `circleIntegral_pow_mul_eq_zero`: the moments of a function holomorphic on a closed disc
  vanish.
- `exists_monic_analyticOnNhd_eval_mul`: for `f` meromorphic at every point of a compact set `K`,
  there is a monic polynomial `p` such that `p * f` is analytic near every point of `K`, and
  whose roots are points at which `f` is not analytic.
-/

open Set Filter Metric Complex Polynomial
open scoped Real Topology

namespace Laurent

variable {f : ℂ → ℂ} {r : ℝ} {R : ENNReal} {ρ : ℝ}

/-- If `f` is holomorphic on an annulus and all its moments `∮ z ^ k f z dz`, `k ≥ 0`, on a
circle of radius `ρ` in the annulus vanish, then the Cauchy integral over this circle is `f` on
the part of the annulus inside the circle. -/
theorem cauchyIntegral_eq_of_forall_moment_eq_zero (hf : DifferentiableOn ℂ f (annulus r R))
    (hρ : IsRadius r R ρ) (hmom : ∀ k : ℕ, ∮ z in C(0, ρ), z ^ k * f z = 0) {w : ℂ}
    (hw : r < ‖w‖) (hwρ : ‖w‖ < ρ) :
    (2 * π * I)⁻¹ * ∮ z in C(0, ρ), (z - w)⁻¹ * f z = f w := by
  have hwA : w ∈ annulus r R := ⟨hw, by
    rw [enorm_lt_iff_ofReal_lt]
    exact (ENNReal.ofReal_le_ofReal hwρ.le).trans_lt hρ.2.2⟩
  have hminus : minusPart f ρ w = 0 := by
    have h0 : ∀ k : ℕ, coeff f ρ (-((k : ℤ) + 1)) = 0 := fun k ↦ by
      have : (-(-((k : ℤ) + 1)) - 1) = (k : ℤ) := by ring
      simp only [coeff, this, zpow_natCast, hmom k, mul_zero]
    simp only [minusPart, h0, zero_mul, tsum_zero]
  have hplus : plusPart f ρ w = (2 * π * I)⁻¹ * ∮ z in C(0, ρ), (z - w)⁻¹ * f z :=
    (hasSum_coeff_nat hρ.pos (hf.continuousOn.mono (sphere_subset_annulus hρ)) hwρ).tsum_eq
  rw [← plusPart_add_minusPart hf hρ hwA, hminus, add_zero, hplus]

end Laurent

/-- The moments of a function holomorphic near a closed disc vanish. -/
theorem circleIntegral_pow_mul_eq_zero {f : ℂ → ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 ρ)) (k : ℕ) :
    ∮ z in C(0, ρ), z ^ k * f z = 0 := by
  refine DiffContOnCl.circleIntegral_eq_zero hρ ?_
  have hd : DifferentiableOn ℂ (fun z ↦ z ^ k * f z) (closedBall 0 ρ) := fun z hz ↦
    ((differentiableAt_pow k).mul (hf z hz).differentiableAt).differentiableWithinAt
  exact ⟨hd.mono ball_subset_closedBall, hd.continuousOn.mono closure_ball_subset_closedBall⟩

/-- The points of a compact set `K` at which a function meromorphic at every point of `K` is not
analytic form a finite set. -/
theorem finite_setOf_not_analyticAt {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hf : ∀ t ∈ K, MeromorphicAt f t) : {t ∈ K | ¬AnalyticAt ℂ f t}.Finite := by
  have hclosed : IsClosed {t : ℂ | ¬AnalyticAt ℂ f t} := by
    simpa [compl_ofPred] using (isOpen_analyticAt ℂ f).isClosed_compl
  refine (hK.inter_right hclosed).finite (isDiscrete_iff_nhdsNE.mpr fun x hx ↦ ?_)
  refine eq_bot_iff.mpr fun s _ ↦ ?_
  have h := (hf x hx.1).eventually_analyticAt
  rw [Filter.mem_inf_principal]
  filter_upwards [h] with y hy hy'
  exact absurd hy hy'.2

/-- For `f` meromorphic at every point of a compact set `K` there is a monic polynomial `p` such
that `p * f` is analytic at every point of `K`, and every root of `p` is a point at which `f` is
not analytic. -/
theorem exists_monic_analyticOnNhd_eval_mul {f : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hf : ∀ t ∈ K, MeromorphicAt f t) :
    ∃ p : ℂ[X], p.Monic ∧ AnalyticOnNhd ℂ (fun z ↦ p.eval z * f z) K ∧
      ∀ t, AnalyticAt ℂ f t → p.eval t ≠ 0 := by
  classical
  set P := (finite_setOf_not_analyticAt hK hf).toFinset
  have hP : ∀ t, t ∈ P ↔ t ∈ K ∧ ¬AnalyticAt ℂ f t := fun t ↦ by simp [P]
  choose! n hn using fun t (ht : t ∈ K) ↦ hf t ht
  set p : ℂ[X] := ∏ t ∈ P, (X - C t) ^ n t
  have hpeval : ∀ z, p.eval z = ∏ t ∈ P, (z - t) ^ n t := fun z ↦ by
    simp [p, eval_prod]
  have hprod : ∀ (Q : Finset ℂ) (z : ℂ), AnalyticAt ℂ (fun w ↦ ∏ t ∈ Q, (w - t) ^ n t) z :=
    fun Q z ↦ Finset.analyticAt_fun_prod _ fun t _ ↦
      ((analyticAt_id (𝕜 := ℂ)).sub analyticAt_const).pow _
  refine ⟨p, monic_prod_of_monic _ _ fun t _ ↦ (monic_X_sub_C t).pow _, fun z hz ↦ ?_,
    fun t ht ↦ ?_⟩
  · by_cases hzP : z ∈ P
    · have hsplit : (fun w ↦ p.eval w * f w) =
          fun w ↦ (∏ t ∈ P.erase z, (w - t) ^ n t) * ((w - z) ^ n z • f w) := by
        funext w
        rw [hpeval, ← Finset.mul_prod_erase P _ hzP, smul_eq_mul]
        ring
      rw [hsplit]
      refine AnalyticAt.mul ?_ (hn z ((hP z).mp hzP).1)
      exact hprod _ z
    · have hfz : AnalyticAt ℂ f z := by
        by_contra h
        exact hzP ((hP z).mpr ⟨hz, h⟩)
      have hpa : AnalyticAt ℂ (fun w ↦ p.eval w) z := by
        simp_rw [hpeval]
        exact hprod P z
      exact hpa.mul hfz
  · rw [hpeval, Finset.prod_ne_zero_iff]
    intro s hs
    refine pow_ne_zero _ (sub_ne_zero.mpr fun hts ↦ ?_)
    exact ((hP s).mp hs).2 (hts ▸ ht)
