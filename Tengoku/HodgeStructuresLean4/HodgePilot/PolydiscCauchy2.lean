import Tengoku.HodgeStructuresLean4.HodgePilot.PolydiscCauchy
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Analysis.SpecificLimits.Normed
import Tengoku.Seed.Analysis.Normed.Ring.InfiniteSum
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Ring
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Module
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Constructions
import Tengoku.Seed.MeasureTheory.Integral.DominatedConvergence
import Tengoku.Seed.Analysis.Analytic.Basic
import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Basic
import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Curry
import Tengoku.Seed.Data.Fin.Tuple.NatAntidiagonal
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Algebra.Order.Field.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Cauchy power-series expansion on closed polydiscs in `ℂⁿ`

Stage 2 of the several-complex-variables campaign (route P1 of the Wall-1
Poincaré design memo, §4.4): the **multivariable power-series expansion**
derived from the stage-1 polydisc Cauchy integral formula
(`HodgePilot.PolydiscCauchy.torusIntegral_sub_inv_smul`).

If `f : (Fin n → ℂ) → E` is complex differentiable (jointly, in the Fréchet
sense) on the closed polydisc `closedPolydisc c R` and `z` lies in the open
polydisc, then expanding the Cauchy kernel `∏ i, (w i - z i)⁻¹` as a
multivariable geometric series and exchanging sum and integral gives

`f z = ∑_{α : Fin n → ℕ} (∏ i, (z i - c i) ^ α i) • cauchyCoeff f c R α`,

an unconditionally convergent sum over the multi-index lattice, where
`cauchyCoeff f c R α` is the normalized torus integral
`((2πI)^n)⁻¹ • ∯ w in T(c, R), (∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w`.

## Main declarations

* `HodgePilot.PolydiscCauchy.hasSum_prod_geometric_of_norm_lt_one`: the
  multivariable geometric series `∑_{α} ∏ i, q i ^ α i = ∏ i, (1 - q i)⁻¹`
  (unconditional convergence over `Fin n → ℕ`), with the real summability
  companion `summable_prod_pow_of_lt_one`.
* `HodgePilot.PolydiscCauchy.hasSum_cauchyKernel`: the geometric-series
  expansion of the Cauchy kernel itself.
* `HodgePilot.PolydiscCauchy.cauchyCoeff`: the `α`-th Cauchy coefficient of
  `f` on the polydisc, as a normalized torus integral.
* `HodgePilot.PolydiscCauchy.norm_cauchyCoeff_le`: the **Cauchy inequalities**
  on polydiscs: `‖cauchyCoeff f c R α‖ ≤ M / ∏ i, R i ^ α i`.
* `HodgePilot.PolydiscCauchy.hasSum_cauchyCoeff_smul`: the **expansion
  theorem** stated above — every jointly differentiable function on a closed
  polydisc is the sum of its monomial Cauchy expansion at every point of the
  open polydisc, in every dimension `n`.
* `HodgePilot.PolydiscCauchy.polydiscSeries`,
  `hasFPowerSeriesOnBall_polydiscSeries`: the expansion regrouped by total
  degree into a `FormalMultilinearSeries` together with
  `HasFPowerSeriesOnBall`; consequently
  `analyticAt_of_mem_polydisc`/`analyticOnNhd_polydisc`: such an `f` is
  jointly analytic at every point of the open polydisc.

## Scope discipline

This module contains **series-expansion content only** (stage 2 of the memo's
staged route).  All hypotheses are *joint* (Fréchet) complex
differentiability on a closed polydisc; nothing here weakens them to
separate differentiability.  It does **not** provide: Osgood's lemma or any
"separately holomorphic ⇒ jointly analytic" statement, Hartogs-type
theorems, analyticity statements on open sets other than (interiors of)
polydiscs, or any statement toward a several-variables holomorphic Poincaré
lemma.  Those are later stages of the campaign and are not claimed anywhere
here.  No comparison-type statement of any kind is made.
-/

open Metric Set MeasureTheory

open scoped NNReal ENNReal

namespace HodgePilot
namespace PolydiscCauchy

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ## The multivariable geometric series -/

/-- Real multivariable geometric series: for componentwise ratios
`0 ≤ r i < 1`, the family `α ↦ ∏ i, r i ^ α i` is summable over the
multi-index lattice `Fin n → ℕ`.-/
theorem summable_prod_pow_of_lt_one :
    ∀ {n : ℕ} {r : Fin n → ℝ}, (∀ i, 0 ≤ r i) → (∀ i, r i < 1) →
      Summable fun α : Fin n → ℕ => ∏ i, r i ^ α i := by
  intro n
  induction n with
  | zero =>
    intro r _ _
    have h : (fun α : Fin 0 → ℕ => ∏ i, r i ^ α i) = fun _ => (1 : ℝ) :=
      funext fun α => by simp
    rw [h]
    exact (hasSum_single (f := fun _ : Fin 0 → ℕ => (1 : ℝ)) default
      fun b hb => absurd (Subsingleton.elim b default) hb).summable
  | succ n ih =>
    intro r h0 h1
    have hhead : Summable fun k : ℕ => r 0 ^ k := summable_geometric_of_lt_one (h0 0) (h1 0)
    have htail : Summable fun β : Fin n → ℕ => ∏ j, r j.succ ^ β j :=
      ih (fun j : Fin n => h0 j.succ) fun j : Fin n => h1 j.succ
    have hprod : Summable fun x : ℕ × (Fin n → ℕ) => r 0 ^ x.1 * ∏ j, r j.succ ^ x.2 j :=
      Summable.mul_of_nonneg (f := fun k : ℕ => r 0 ^ k)
        (g := fun β : Fin n → ℕ => ∏ j, r j.succ ^ β j) hhead htail
        (Pi.le_def.mpr fun k => pow_nonneg (h0 0) k)
        (Pi.le_def.mpr fun β => Finset.prod_nonneg fun j _ => pow_nonneg (h0 j.succ) _)
    refine ((Fin.consEquiv fun _ => ℕ).summable_iff
      (f := fun α : Fin (n + 1) → ℕ => ∏ i, r i ^ α i)).mp (hprod.congr fun x => ?_)
    show r 0 ^ x.1 * ∏ j, r j.succ ^ x.2 j = ∏ i, r i ^ (Fin.cons x.1 x.2 : Fin (n + 1) → ℕ) i
    rw [Fin.prod_univ_succ, Fin.cons_zero]
    exact congrArg (r 0 ^ x.1 * ·) (Finset.prod_congr rfl fun j _ => by rw [Fin.cons_succ])

/-- Multivariable geometric series: for `q : Fin n → ℂ` with `‖q i‖ < 1` in
every coordinate,

`∑_{α : Fin n → ℕ} ∏ i, q i ^ α i = ∏ i, (1 - q i)⁻¹`

with unconditional convergence over the multi-index lattice.-/
theorem hasSum_prod_geometric_of_norm_lt_one :
    ∀ {n : ℕ} {q : Fin n → ℂ}, (∀ i, ‖q i‖ < 1) →
      HasSum (fun α : Fin n → ℕ => ∏ i, q i ^ α i) (∏ i, (1 - q i)⁻¹) := by
  intro n
  induction n with
  | zero =>
    intro q _
    have h : (fun α : Fin 0 → ℕ => ∏ i, q i ^ α i) = fun _ => (1 : ℂ) :=
      funext fun α => by simp
    have h2 : (∏ i, (1 - q i)⁻¹) = 1 := by simp
    rw [h, h2]
    exact hasSum_single (f := fun _ : Fin 0 → ℕ => (1 : ℂ)) default
      fun b hb => absurd (Subsingleton.elim b default) hb
  | succ n ih =>
    intro q hq
    have hhead : HasSum (fun k : ℕ => q 0 ^ k) (1 - q 0)⁻¹ :=
      hasSum_geometric_of_norm_lt_one (hq 0)
    have htail : HasSum (fun β : Fin n → ℕ => ∏ j, q j.succ ^ β j)
        (∏ j : Fin n, (1 - q j.succ)⁻¹) := ih fun j : Fin n => hq j.succ
    have hs1 : Summable fun k : ℕ => ‖q 0 ^ k‖ := by
      have := summable_geometric_of_lt_one (norm_nonneg (q 0)) (hq 0)
      exact this.congr fun k => (norm_pow _ _).symm
    have hs2 : Summable fun β : Fin n → ℕ => ‖∏ j, q j.succ ^ β j‖ := by
      have := summable_prod_pow_of_lt_one (fun j : Fin n => norm_nonneg (q j.succ))
        fun j : Fin n => hq j.succ
      refine this.congr fun β => ?_
      rw [Complex.norm_prod]
      exact Finset.prod_congr rfl fun j _ => (norm_pow _ _).symm
    have H := HasSum.mul (f := fun k : ℕ => q 0 ^ k)
      (g := fun β : Fin n → ℕ => ∏ j, q j.succ ^ β j) hhead htail
      (summable_mul_of_summable_norm (R := ℂ) (f := fun k : ℕ => q 0 ^ k)
        (g := fun β : Fin n → ℕ => ∏ j, q j.succ ^ β j) hs1 hs2)
    rw [show (∏ i, (1 - q i)⁻¹) = (1 - q 0)⁻¹ * ∏ j : Fin n, (1 - q j.succ)⁻¹ from
      Fin.prod_univ_succ _]
    refine ((Fin.consEquiv fun _ => ℕ).hasSum_iff
      (f := fun α : Fin (n + 1) → ℕ => ∏ i, q i ^ α i)).mp ?_
    have hfe : ((fun α : Fin (n + 1) → ℕ => ∏ i, q i ^ α i) ∘
        (Fin.consEquiv fun _ => ℕ)) =
        fun x : ℕ × (Fin n → ℕ) => q 0 ^ x.1 * ∏ j, q j.succ ^ x.2 j := by
      funext x
      show (∏ i, q i ^ (Fin.cons x.1 x.2 : Fin (n + 1) → ℕ) i) = _
      rw [Fin.prod_univ_succ, Fin.cons_zero]
      exact congrArg (q 0 ^ x.1 * ·) (Finset.prod_congr rfl fun j _ => by rw [Fin.cons_succ])
    rw [hfe]
    exact H

/-! ## Expansion of the Cauchy kernel -/

/-- Geometric-series expansion of the Cauchy kernel: if
`‖z i - c i‖ < ‖w i - c i‖` in every coordinate, then

`∑_{α : Fin n → ℕ} (∏ i, (z i - c i) ^ α i) * ∏ i, ((w i - c i) ^ (α i + 1))⁻¹
  = ∏ i, (w i - z i)⁻¹`.-/
theorem hasSum_cauchyKernel {c z w : Fin n → ℂ}
    (h : ∀ i, ‖z i - c i‖ < ‖w i - c i‖) :
    HasSum
      (fun α : Fin n → ℕ =>
        (∏ i, (z i - c i) ^ α i) * ∏ i, ((w i - c i) ^ (α i + 1))⁻¹)
      (∏ i, (w i - z i)⁻¹) := by
  have hw : ∀ i, w i - c i ≠ 0 := fun i =>
    norm_pos_iff.mp ((norm_nonneg _).trans_lt (h i))
  have hq : ∀ i, ‖(z i - c i) / (w i - c i)‖ < 1 := fun i => by
    rw [norm_div]
    exact (div_lt_one ((norm_nonneg _).trans_lt (h i))).mpr (h i)
  have H := (hasSum_prod_geometric_of_norm_lt_one hq).mul_right (∏ i, (w i - c i)⁻¹)
  have hfun : (fun α : Fin n → ℕ =>
      (∏ i, ((z i - c i) / (w i - c i)) ^ α i) * ∏ i, (w i - c i)⁻¹) =
      fun α : Fin n → ℕ =>
        (∏ i, (z i - c i) ^ α i) * ∏ i, ((w i - c i) ^ (α i + 1))⁻¹ := by
    funext α
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [div_pow, div_eq_mul_inv, mul_assoc, ← mul_inv, ← pow_succ]
  have hval : (∏ i, (1 - (z i - c i) / (w i - c i))⁻¹) * ∏ i, (w i - c i)⁻¹ =
      ∏ i, (w i - z i)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_inv]
    congr 1
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (hw i)]
    ring
  rw [hfun, hval] at H
  exact H

/-! ## Cauchy coefficients and the Cauchy inequalities -/

/-- The closed polydisc is compact.-/
theorem isCompact_closedPolydisc (c : Fin n → ℂ) (R : Fin n → ℝ) :
    IsCompact (closedPolydisc c R) :=
  isCompact_univ_pi fun i => isCompact_closedBall (c i) (R i)

/-- Torus integrability of the power-kernel-weighted integrand
`w ↦ (k * ∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w` for `f` continuous on the
closed polydisc with positive radii.-/
theorem torusIntegrable_pow_kernel_smul {f : (Fin n → ℂ) → E} {c : Fin n → ℂ}
    {R : Fin n → ℝ} (hR : ∀ i, 0 < R i)
    (hf : ContinuousOn f (closedPolydisc c R)) (k : ℂ) (α : Fin n → ℕ) :
    TorusIntegrable (fun w => (k * ∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w) c R := by
  have hne : ∀ (θ : Fin n → ℝ) (i : Fin n), torusMap c R θ i - c i ≠ 0 := fun θ i =>
    norm_pos_iff.mp
      (by rw [norm_torusMap_apply_sub_center c (hR i).le]; exact hR i)
  have hker : Continuous fun θ : Fin n → ℝ =>
      k * ∏ i, ((torusMap c R θ i - c i) ^ (α i + 1))⁻¹ := by
    refine continuous_const.mul (continuous_finsetProd _ fun i _ => ?_)
    refine Continuous.inv₀ ?_ fun θ => pow_ne_zero _ (hne θ i)
    exact (((continuous_apply i).comp (continuous_torusMap c R)).sub continuous_const).pow _
  have hfc : ContinuousOn (fun θ : Fin n → ℝ => f (torusMap c R θ))
      (Set.Icc (0 : Fin n → ℝ) fun _ => 2 * Real.pi) :=
    hf.comp (continuous_torusMap c R).continuousOn
      fun θ _ => torusMap_mem_closedPolydisc (fun i => (hR i).le) θ
  exact (hker.continuousOn.smul hfc).integrableOn_Icc

/-- The `α`-th Cauchy coefficient of `f` on the closed polydisc with center
`c` and radii `R`: the normalized torus integral

`((2πI)^n)⁻¹ • ∯ w in T(c, R), (∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w`.-/
noncomputable def cauchyCoeff (f : (Fin n → ℂ) → E) (c : Fin n → ℂ)
    (R : Fin n → ℝ) (α : Fin n → ℕ) : E :=
  ((2 * (Real.pi : ℂ) * Complex.I) ^ n)⁻¹ •
    ∯ w in T(c, R), (∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w

/-- The norm of the Cauchy normalization constant.-/
theorem norm_two_pi_I : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
  have h : 2 * (Real.pi : ℂ) * Complex.I = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_of_nonneg Real.two_pi_pos.le]

/-- **Cauchy inequalities on a closed polydisc**: if `‖f‖ ≤ M` on the
distinguished boundary, then `‖cauchyCoeff f c R α‖ ≤ M / ∏ i, R i ^ α i`.-/
theorem norm_cauchyCoeff_le {f : (Fin n → ℂ) → E} {c : Fin n → ℂ}
    {R : Fin n → ℝ} (hR : ∀ i, 0 < R i) {M : ℝ}
    (hM : ∀ θ : Fin n → ℝ, ‖f (torusMap c R θ)‖ ≤ M) (α : Fin n → ℕ) :
    ‖cauchyCoeff f c R α‖ ≤ M / ∏ i, R i ^ α i := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hkernel : ∀ θ : Fin n → ℝ,
      ‖∏ i, ((torusMap c R θ i - c i) ^ (α i + 1))⁻¹‖ =
        (∏ i, R i ^ (α i + 1))⁻¹ := by
    intro θ
    rw [Complex.norm_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_inv, norm_pow, norm_torusMap_apply_sub_center c (hR i).le]
  have hbound : ∀ θ : Fin n → ℝ,
      ‖(∏ i, ((torusMap c R θ i - c i) ^ (α i + 1))⁻¹) • f (torusMap c R θ)‖ ≤
        (∏ i, R i ^ (α i + 1))⁻¹ * M := by
    intro θ
    rw [norm_smul, hkernel θ]
    exact mul_le_mul_of_nonneg_left (hM θ)
      (inv_nonneg.mpr (Finset.prod_nonneg fun i _ => pow_nonneg (hR i).le _))
  have hint := norm_torusIntegral_le_of_norm_le_const
    (f := fun w => (∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w) (c := c) (R := R) hbound
  have h2π : (0 : ℝ) < (2 * Real.pi) ^ n := pow_pos Real.two_pi_pos n
  have hPR : (0 : ℝ) < ∏ i, R i := Finset.prod_pos fun i _ => hR i
  have hQ : (0 : ℝ) < ∏ i, R i ^ α i := Finset.prod_pos fun i _ => pow_pos (hR i) _
  have habs : (∏ i, |R i|) = ∏ i, R i :=
    Finset.prod_congr rfl fun i _ => abs_of_pos (hR i)
  have hsplit : (∏ i, R i ^ (α i + 1)) = (∏ i, R i ^ α i) * ∏ i, R i := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => pow_succ _ _
  have hnorm2πn : ‖(2 * (Real.pi : ℂ) * Complex.I) ^ n‖ = (2 * Real.pi) ^ n := by
    rw [norm_pow, norm_two_pi_I]
  rw [cauchyCoeff, norm_smul, norm_inv, hnorm2πn]
  calc ((2 * Real.pi) ^ n)⁻¹ *
        ‖∯ w in T(c, R), (∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w‖ ≤
      ((2 * Real.pi) ^ n)⁻¹ *
        (((2 * Real.pi) ^ n * ∏ i, |R i|) * ((∏ i, R i ^ (α i + 1))⁻¹ * M)) := by
        exact mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr h2π.le)
    _ = M / ∏ i, R i ^ α i := by
        rw [habs, hsplit]
        field_simp

/-! ## The expansion theorem -/

/-- Exchange of summation and torus integration for the kernel expansion: for
`f` complex differentiable on the closed polydisc and `z` in the open
polydisc,

`∑_{α} (∏ i, (z i - c i) ^ α i) • ∯ (∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w
  = (2πI)^n • f z`.-/
theorem hasSum_torusIntegral_pow_kernel_smul [CompleteSpace E]
    {f : (Fin n → ℂ) → E} {c z : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : DifferentiableOn ℂ f (closedPolydisc c R)) (hz : z ∈ polydisc c R) :
    HasSum
      (fun α : Fin n → ℕ => (∏ i, (z i - c i) ^ α i) •
        ∯ w in T(c, R), (∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w)
      ((2 * (Real.pi : ℂ) * Complex.I) ^ n • f z) := by
  have hR : ∀ i, 0 < R i := fun i =>
    dist_nonneg.trans_lt (mem_ball.1 (mem_polydisc.1 hz i))
  obtain ⟨M, hM⟩ :=
    (isCompact_closedPolydisc c R).exists_bound_of_continuousOn hf.continuousOn
  have hMt : ∀ θ : Fin n → ℝ, ‖f (torusMap c R θ)‖ ≤ M := fun θ =>
    hM _ (torusMap_mem_closedPolydisc (fun i => (hR i).le) θ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMt 0)
  have hzn : ∀ i, ‖z i - c i‖ < R i := fun i =>
    mem_ball_iff_norm.1 (mem_polydisc.1 hz i)
  -- integrability of every full integrand
  have hGint : ∀ α : Fin n → ℕ,
      TorusIntegrable (fun w =>
        ((∏ i, (z i - c i) ^ α i) * ∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w) c R :=
    fun α => torusIntegrable_pow_kernel_smul hR hf.continuousOn _ α
  have hFint : ∀ α : Fin n → ℕ,
      Integrable (fun θ : Fin n → ℝ =>
        (∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * Complex.I) •
          (((∏ i, (z i - c i) ^ α i) *
            ∏ i, ((torusMap c R θ i - c i) ^ (α i + 1))⁻¹) • f (torusMap c R θ)))
        (volume.restrict (Set.Icc (0 : Fin n → ℝ) fun _ => 2 * Real.pi)) :=
    fun α => (hGint α).function_integrable
  -- pointwise convergence of the integrands
  have hptwise : ∀ θ : Fin n → ℝ,
      HasSum
        (fun α : Fin n → ℕ =>
          (∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * Complex.I) •
            (((∏ i, (z i - c i) ^ α i) *
              ∏ i, ((torusMap c R θ i - c i) ^ (α i + 1))⁻¹) • f (torusMap c R θ)))
        ((∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * Complex.I) •
          ((∏ i, (torusMap c R θ i - z i)⁻¹) • f (torusMap c R θ))) := by
    intro θ
    have hlt : ∀ i, ‖z i - c i‖ < ‖torusMap c R θ i - c i‖ := fun i => by
      rw [norm_torusMap_apply_sub_center c (hR i).le]
      exact hzn i
    exact ((hasSum_cauchyKernel hlt).smul_const (f (torusMap c R θ))).const_smul _
  -- summability of the integrals of the norms
  have hqs : Summable fun α : Fin n → ℕ =>
      (2 * Real.pi) ^ n * M * ∏ i, (‖z i - c i‖ / R i) ^ α i :=
    (summable_prod_pow_of_lt_one
      (fun i => div_nonneg (norm_nonneg _) (hR i).le)
      fun i => (div_lt_one (hR i)).mpr (hzn i)).mul_left _
  have hFsum : Summable fun α : Fin n → ℕ =>
      ∫ θ, ‖(∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * Complex.I) •
          (((∏ i, (z i - c i) ^ α i) *
            ∏ i, ((torusMap c R θ i - c i) ^ (α i + 1))⁻¹) • f (torusMap c R θ))‖
        ∂(volume.restrict (Set.Icc (0 : Fin n → ℝ) fun _ => 2 * Real.pi)) := by
    have hIcc : (volume (Set.Icc (0 : Fin n → ℝ) fun _ => 2 * Real.pi)).toReal =
        (2 * Real.pi) ^ n := by
      rw [Real.volume_Icc_pi_toReal (a := (0 : Fin n → ℝ))
        (Pi.le_def.mpr fun _ => Real.two_pi_pos.le)]
      simp
    refine Summable.of_nonneg_of_le
      (fun α => integral_nonneg fun θ => norm_nonneg _) (fun α => ?_) hqs
    have hsplit : (∏ i, R i ^ (α i + 1)) = (∏ i, R i ^ α i) * ∏ i, R i := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => pow_succ _ _
    have hPR : (0 : ℝ) < ∏ i, R i := Finset.prod_pos fun i _ => hR i
    have hQ : (0 : ℝ) < ∏ i, R i ^ α i := Finset.prod_pos fun i _ => pow_pos (hR i) _
    have hpt : ∀ θ ∈ Set.Icc (0 : Fin n → ℝ) fun _ => 2 * Real.pi,
        ‖(∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * Complex.I) •
          (((∏ i, (z i - c i) ^ α i) *
            ∏ i, ((torusMap c R θ i - c i) ^ (α i + 1))⁻¹) • f (torusMap c R θ))‖ ≤
          M * ∏ i, (‖z i - c i‖ / R i) ^ α i := by
      intro θ _
      have hjac : ‖∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * Complex.I‖ =
          ∏ i, R i := by
        rw [Complex.norm_prod]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I,
          mul_one, mul_one, Complex.norm_of_nonneg (hR i).le]
      have hker : ‖(∏ i, (z i - c i) ^ α i) *
          ∏ i, ((torusMap c R θ i - c i) ^ (α i + 1))⁻¹‖ =
          (∏ i, ‖z i - c i‖ ^ α i) * (∏ i, R i ^ (α i + 1))⁻¹ := by
        rw [norm_mul, Complex.norm_prod, Complex.norm_prod]
        congr 1
        · exact Finset.prod_congr rfl fun i _ => norm_pow _ _
        · rw [← Finset.prod_inv_distrib]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [norm_inv, norm_pow, norm_torusMap_apply_sub_center c (hR i).le]
      have hA : (∏ i, (‖z i - c i‖ / R i) ^ α i) =
          (∏ i, ‖z i - c i‖ ^ α i) / ∏ i, R i ^ α i := by
        rw [← Finset.prod_div_distrib]
        exact Finset.prod_congr rfl fun i _ => div_pow _ _ _
      calc ‖(∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * Complex.I) •
            (((∏ i, (z i - c i) ^ α i) *
              ∏ i, ((torusMap c R θ i - c i) ^ (α i + 1))⁻¹) • f (torusMap c R θ))‖ =
          (∏ i, R i) * (((∏ i, ‖z i - c i‖ ^ α i) * (∏ i, R i ^ (α i + 1))⁻¹) *
            ‖f (torusMap c R θ)‖) := by
            rw [norm_smul, norm_smul, hjac, hker]
        _ ≤ (∏ i, R i) * (((∏ i, ‖z i - c i‖ ^ α i) * (∏ i, R i ^ (α i + 1))⁻¹) * M) := by
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hMt θ) ?_) hPR.le
            exact mul_nonneg (Finset.prod_nonneg fun i _ => pow_nonneg (norm_nonneg _) _)
              (inv_nonneg.mpr (Finset.prod_nonneg fun i _ => pow_nonneg (hR i).le _))
        _ = M * ∏ i, (‖z i - c i‖ / R i) ^ α i := by
            rw [hA, hsplit]
            field_simp
    calc (∫ θ, ‖(∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * Complex.I) •
          (((∏ i, (z i - c i) ^ α i) *
            ∏ i, ((torusMap c R θ i - c i) ^ (α i + 1))⁻¹) • f (torusMap c R θ))‖
          ∂(volume.restrict (Set.Icc (0 : Fin n → ℝ) fun _ => 2 * Real.pi))) ≤
        ∫ _ in Set.Icc (0 : Fin n → ℝ) fun _ => 2 * Real.pi,
          (M * ∏ i, (‖z i - c i‖ / R i) ^ α i) ∂volume := by
          refine setIntegral_mono_on ((hFint α).norm) ?_ measurableSet_Icc hpt
          exact integrableOn_const measure_Icc_lt_top.ne
      _ = (2 * Real.pi) ^ n * M * ∏ i, (‖z i - c i‖ / R i) ^ α i := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, hIcc]
          ring
  -- the exchange
  have hswap := MeasureTheory.hasSum_integral_of_summable_integral_norm hFint hFsum
  -- identify the total sum with the stage-1 Cauchy formula
  have hval : (∫ θ, (∑' α : Fin n → ℕ,
      (∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * Complex.I) •
        (((∏ i, (z i - c i) ^ α i) *
          ∏ i, ((torusMap c R θ i - c i) ^ (α i + 1))⁻¹) • f (torusMap c R θ)))
      ∂(volume.restrict (Set.Icc (0 : Fin n → ℝ) fun _ => 2 * Real.pi))) =
      (2 * (Real.pi : ℂ) * Complex.I) ^ n • f z := by
    have h1 : (fun θ : Fin n → ℝ => ∑' α : Fin n → ℕ,
        (∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * Complex.I) •
          (((∏ i, (z i - c i) ^ α i) *
            ∏ i, ((torusMap c R θ i - c i) ^ (α i + 1))⁻¹) • f (torusMap c R θ))) =
        fun θ : Fin n → ℝ =>
          (∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * Complex.I) •
            ((∏ i, (torusMap c R θ i - z i)⁻¹) • f (torusMap c R θ)) :=
      funext fun θ => (hptwise θ).tsum_eq
    rw [h1]
    have h2 : (∫ θ, ((∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * Complex.I) •
        ((∏ i, (torusMap c R θ i - z i)⁻¹) • f (torusMap c R θ)))
        ∂(volume.restrict (Set.Icc (0 : Fin n → ℝ) fun _ => 2 * Real.pi))) =
        ∯ w in T(c, R), (∏ i, (w i - z i)⁻¹) • f w := rfl
    rw [h2, torusIntegral_sub_inv_smul hf hz]
  rw [hval] at hswap
  -- identify each term
  have hterm : (fun α : Fin n → ℕ => ∫ θ,
      (∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * Complex.I) •
        (((∏ i, (z i - c i) ^ α i) *
          ∏ i, ((torusMap c R θ i - c i) ^ (α i + 1))⁻¹) • f (torusMap c R θ))
      ∂(volume.restrict (Set.Icc (0 : Fin n → ℝ) fun _ => 2 * Real.pi))) =
      fun α : Fin n → ℕ => (∏ i, (z i - c i) ^ α i) •
        ∯ w in T(c, R), (∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w := by
    funext α
    have h3 : (∫ θ, (∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) * Complex.I) •
        (((∏ i, (z i - c i) ^ α i) *
          ∏ i, ((torusMap c R θ i - c i) ^ (α i + 1))⁻¹) • f (torusMap c R θ))
        ∂(volume.restrict (Set.Icc (0 : Fin n → ℝ) fun _ => 2 * Real.pi))) =
        ∯ w in T(c, R), ((∏ i, (z i - c i) ^ α i) *
          ∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w := rfl
    rw [h3]
    have h4 : (fun w : Fin n → ℂ => ((∏ i, (z i - c i) ^ α i) *
        ∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w) =
        fun w : Fin n → ℂ => (∏ i, (z i - c i) ^ α i) •
          ((∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w) :=
      funext fun w => mul_smul _ _ _
    rw [h4]
    exact torusIntegral_smul _ _ _ _
  rw [hterm] at hswap
  exact hswap

/-- **The multivariable Cauchy power-series expansion.**  If
`f : (Fin n → ℂ) → E` is complex differentiable (jointly, in the Fréchet
sense) on the closed polydisc and `z` lies in the open polydisc, then

`∑_{α : Fin n → ℕ} (∏ i, (z i - c i) ^ α i) • cauchyCoeff f c R α = f z`,

an unconditionally convergent sum over the multi-index lattice, in every
dimension `n` and for every complete normed `ℂ`-vector space `E`.

The hypothesis is *joint* differentiability; no Osgood/Hartogs-type
weakening to separate differentiability is claimed here.-/
theorem hasSum_cauchyCoeff_smul [CompleteSpace E] {f : (Fin n → ℂ) → E}
    {c z : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : DifferentiableOn ℂ f (closedPolydisc c R)) (hz : z ∈ polydisc c R) :
    HasSum (fun α : Fin n → ℕ => (∏ i, (z i - c i) ^ α i) • cauchyCoeff f c R α)
      (f z) := by
  have H := (hasSum_torusIntegral_pow_kernel_smul hf hz).const_smul
    (((2 * (Real.pi : ℂ) * Complex.I) ^ n)⁻¹ : ℂ)
  rw [inv_smul_smul₀ (two_pi_I_pow_ne_zero n)] at H
  have hfun : (fun α : Fin n → ℕ => ((2 * (Real.pi : ℂ) * Complex.I) ^ n)⁻¹ •
      ((∏ i, (z i - c i) ^ α i) •
        ∯ w in T(c, R), (∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w)) =
      fun α : Fin n → ℕ => (∏ i, (z i - c i) ^ α i) • cauchyCoeff f c R α :=
    funext fun α => smul_comm _ _ _
  rw [hfun] at H
  exact H

/-! ## The formal multilinear series -/

/-- The continuous multilinear monomial map attached to a multi-index
`α : Fin n → ℕ` and a vector `e : E`: the `(∑ i, α i)`-multilinear map

`(v_1, …, v_m) ↦ (∏_j v_j (i_j)) • e`

where the index list `(i_j)` contains each `i : Fin n` exactly `α i` times
(via `finSigmaFinEquiv`).  On the diagonal it evaluates to
`(∏ i, y i ^ α i) • e`.-/
noncomputable def monomialCM (α : Fin n → ℕ) (e : E) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (∑ i, α i) => Fin n → ℂ) E :=
  (ContinuousMultilinearMap.mkPiRing ℂ (Fin (∑ i, α i)) e).compContinuousLinearMap
    fun j => ContinuousLinearMap.proj (finSigmaFinEquiv.symm j).1

theorem monomialCM_apply_diag (α : Fin n → ℕ) (e : E) (y : Fin n → ℂ) :
    (monomialCM α e fun _ => y) = (∏ i, y i ^ α i) • e := by
  rw [monomialCM, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiRing_apply]
  congr 1
  calc (∏ j : Fin (∑ i, α i),
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ)
          (finSigmaFinEquiv.symm j).1 y) =
      ∏ j : Fin (∑ i, α i), y (finSigmaFinEquiv.symm j).1 :=
        Finset.prod_congr rfl fun j _ => rfl
    _ = ∏ s : (i : Fin n) × Fin (α i), y (finSigmaFinEquiv.symm (finSigmaFinEquiv s)).1 :=
        (Equiv.prod_comp finSigmaFinEquiv
          fun j => y (finSigmaFinEquiv.symm j).1).symm
    _ = ∏ s : (i : Fin n) × Fin (α i), y s.1 := by
        simp only [Equiv.symm_apply_apply]
    _ = ∏ i, ∏ _k : Fin (α i), y i := Fintype.prod_sigma _
    _ = ∏ i, y i ^ α i := by
        exact Finset.prod_congr rfl fun i _ => by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem norm_monomialCM_le (α : Fin n → ℕ) (e : E) : ‖monomialCM α e‖ ≤ ‖e‖ := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [ContinuousMultilinearMap.norm_mkPiRing]
  have hproj : ∀ j : Fin (∑ i, α i),
      ‖(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ)
        (finSigmaFinEquiv.symm j).1)‖ ≤ 1 := fun j =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
      rw [ContinuousLinearMap.proj_apply, one_mul]
      exact norm_le_pi_norm x _
  calc ‖e‖ * ∏ j, ‖(ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ)
        (finSigmaFinEquiv.symm j).1)‖ ≤ ‖e‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (Finset.prod_le_one (fun j _ => norm_nonneg _) fun j _ => hproj j)
        (norm_nonneg e)
    _ = ‖e‖ := mul_one _

/-- The Cauchy power series of `f` on the closed polydisc, as a formal
multilinear series: the `m`-th term collects the monomials of total degree
`m`, i.e. the Cauchy coefficients over `Finset.Nat.antidiagonalTuple n m`.-/
noncomputable def polydiscSeries (f : (Fin n → ℂ) → E) (c : Fin n → ℂ)
    (R : Fin n → ℝ) : FormalMultilinearSeries ℂ (Fin n → ℂ) E := fun m =>
  ∑ a ∈ (Finset.Nat.antidiagonalTuple n m).attach,
    (monomialCM a.1 (cauchyCoeff f c R a.1)).domDomCongr
      (finCongr (Finset.Nat.mem_antidiagonalTuple.mp a.2))

theorem polydiscSeries_apply_diag (f : (Fin n → ℂ) → E) (c : Fin n → ℂ)
    (R : Fin n → ℝ) (m : ℕ) (y : Fin n → ℂ) :
    (polydiscSeries f c R m fun _ => y) =
      ∑ a ∈ (Finset.Nat.antidiagonalTuple n m).attach,
        (∏ i, y i ^ a.1 i) • cauchyCoeff f c R a.1 := by
  rw [polydiscSeries, sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  exact monomialCM_apply_diag _ _ _

/-- Fiberwise (fixed-total-degree) convergence: the degree-`m` term of
`polydiscSeries` evaluated on the diagonal is the finite sum of the monomial
terms of total degree `m`.-/
theorem hasSum_polydiscSeries_fiber (f : (Fin n → ℂ) → E) (c : Fin n → ℂ)
    (R : Fin n → ℝ) (m : ℕ) (y : Fin n → ℂ) :
    HasSum
      (fun x : {a : Fin n → ℕ // (∑ i, a i) = m} =>
        (∏ i, y i ^ x.1 i) • cauchyCoeff f c R x.1)
      (polydiscSeries f c R m fun _ => y) := by
  have h1 := hasSum_fintype
    (fun x : {x // x ∈ Finset.Nat.antidiagonalTuple n m} =>
      (∏ i, y i ^ x.1 i) • cauchyCoeff f c R x.1)
  rw [Finset.univ_eq_attach, ← polydiscSeries_apply_diag] at h1
  exact ((Equiv.subtypeEquivRight
    fun a : Fin n → ℕ => Finset.Nat.mem_antidiagonalTuple).hasSum_iff).mp h1

/-- Radius bound: the Cauchy power series converges on every ball of radius
`r < min R i`.-/
theorem le_radius_polydiscSeries {f : (Fin n → ℂ) → E} {c : Fin n → ℂ}
    {R : Fin n → ℝ} (hR : ∀ i, 0 < R i) {M : ℝ}
    (hM : ∀ θ : Fin n → ℝ, ‖f (torusMap c R θ)‖ ≤ M) {r : ℝ≥0}
    (hrR : ∀ i, (r : ℝ) < R i) :
    (r : ℝ≥0∞) ≤ (polydiscSeries f c R).radius := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hq0 : ∀ i, 0 ≤ (r : ℝ) / R i := fun i => div_nonneg r.coe_nonneg (hR i).le
  have hq1 : ∀ i, (r : ℝ) / R i < 1 := fun i => (div_lt_one (hR i)).mpr (hrR i)
  have hsum : Summable fun α : Fin n → ℕ => ∏ i, ((r : ℝ) / R i) ^ α i :=
    summable_prod_pow_of_lt_one hq0 hq1
  refine (polydiscSeries f c R).le_radius_of_bound
    (M * ∑' α : Fin n → ℕ, ∏ i, ((r : ℝ) / R i) ^ α i) fun m => ?_
  have h1 : ‖polydiscSeries f c R m‖ ≤
      ∑ a ∈ (Finset.Nat.antidiagonalTuple n m).attach, M / ∏ i, R i ^ a.1 i := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [ContinuousMultilinearMap.norm_domDomCongr]
    exact (norm_monomialCM_le _ _).trans (norm_cauchyCoeff_le hR hM a.1)
  calc ‖polydiscSeries f c R m‖ * (r : ℝ) ^ m ≤
      (∑ a ∈ (Finset.Nat.antidiagonalTuple n m).attach, M / ∏ i, R i ^ a.1 i) *
        (r : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg r.coe_nonneg m)
    _ = ∑ a ∈ (Finset.Nat.antidiagonalTuple n m).attach,
          M * ∏ i, ((r : ℝ) / R i) ^ a.1 i := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        have hα : (∑ i, a.1 i) = m := Finset.Nat.mem_antidiagonalTuple.mp a.2
        have hrm : (r : ℝ) ^ m = ∏ i, (r : ℝ) ^ a.1 i := by
          rw [Finset.prod_pow_eq_pow_sum, hα]
        rw [hrm, div_mul_eq_mul_div, mul_div_assoc]
        congr 1
        rw [← Finset.prod_div_distrib]
        exact Finset.prod_congr rfl fun i _ => (div_pow _ _ _).symm
    _ = M * ∑ a ∈ (Finset.Nat.antidiagonalTuple n m).attach,
          ∏ i, ((r : ℝ) / R i) ^ a.1 i := by rw [Finset.mul_sum]
    _ ≤ M * ∑' α : Fin n → ℕ, ∏ i, ((r : ℝ) / R i) ^ α i := by
        refine mul_le_mul_of_nonneg_left ?_ hM0
        rw [Finset.sum_attach (Finset.Nat.antidiagonalTuple n m)
          fun α => ∏ i, ((r : ℝ) / R i) ^ α i]
        exact hsum.sum_le_tsum _ fun α _ =>
          Finset.prod_nonneg fun i _ => pow_nonneg (hq0 i) _

/-- **The Cauchy power series converges to `f` on balls.**  If `f` is complex
differentiable on the closed polydisc `closedPolydisc c R` and `0 < r < R i`
for every `i`, then `f` has `polydiscSeries f c R` as a power series on the
ball of radius `r` around `c` (a sup-norm ball in `Fin n → ℂ`, i.e. the
equal-radii polydisc).-/
theorem hasFPowerSeriesOnBall_polydiscSeries [CompleteSpace E]
    {f : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : DifferentiableOn ℂ f (closedPolydisc c R)) {r : ℝ≥0} (hr : 0 < r)
    (hrR : ∀ i, (r : ℝ) < R i) :
    HasFPowerSeriesOnBall f (polydiscSeries f c R) c r := by
  have hR : ∀ i, 0 < R i := fun i => lt_of_le_of_lt r.coe_nonneg (hrR i)
  obtain ⟨M, hM⟩ :=
    (isCompact_closedPolydisc c R).exists_bound_of_continuousOn hf.continuousOn
  have hMt : ∀ θ : Fin n → ℝ, ‖f (torusMap c R θ)‖ ≤ M := fun θ =>
    hM _ (torusMap_mem_closedPolydisc (fun i => (hR i).le) θ)
  refine ⟨le_radius_polydiscSeries hR hMt hrR, ENNReal.coe_pos.mpr hr, ?_⟩
  intro y hy
  have hy' : ∀ i, ‖y i‖ < R i := by
    intro i
    have h1 : ‖y‖ₑ < (r : ℝ≥0∞) := by
      rwa [Metric.mem_eball, edist_zero_right] at hy
    have h2 : ‖y‖ < (r : ℝ) := by
      have := enorm_lt_coe.mp h1
      exact_mod_cast this
    exact lt_trans (lt_of_le_of_lt (norm_le_pi_norm y i) h2) (hrR i)
  have hcy : c + y ∈ polydisc c R := mem_polydisc.2 fun i => by
    rw [mem_ball_iff_norm]
    simpa using hy' i
  have H := hasSum_cauchyCoeff_smul hf hcy
  have hyc : (fun α : Fin n → ℕ =>
      (∏ i, ((c + y) i - c i) ^ α i) • cauchyCoeff f c R α) =
      fun α : Fin n → ℕ => (∏ i, y i ^ α i) • cauchyCoeff f c R α := by
    funext α
    congr 1
    exact Finset.prod_congr rfl fun i _ => by simp
  rw [hyc] at H
  exact ((Equiv.sigmaFiberEquiv fun α : Fin n → ℕ => ∑ i, α i).hasSum_iff.mpr H).sigma
    fun m => hasSum_polydiscSeries_fiber f c R m y

/-- A function complex differentiable on a closed polydisc with positive
radii is (jointly) analytic at the center.-/
theorem analyticAt_of_differentiableOn_closedPolydisc [CompleteSpace E]
    {f : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : DifferentiableOn ℂ f (closedPolydisc c R)) (hR : ∀ i, 0 < R i) :
    AnalyticAt ℂ f c := by
  obtain ⟨ε, hε0, hεR⟩ := Pi.exists_forall_pos_add_lt (x := fun _ : Fin n => (0 : ℝ))
    (y := R) hR
  have hεR' : ∀ i, ε < R i := fun i => by simpa using hεR i
  exact (hasFPowerSeriesOnBall_polydiscSeries hf (r := ε.toNNReal)
    (Real.toNNReal_pos.mpr hε0)
    fun i => by rw [Real.coe_toNNReal ε hε0.le]; exact hεR' i).analyticAt

/-- A function complex differentiable on a closed polydisc is (jointly)
analytic at every point of the open polydisc.-/
theorem analyticAt_of_mem_polydisc [CompleteSpace E] {f : (Fin n → ℂ) → E}
    {c z : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : DifferentiableOn ℂ f (closedPolydisc c R)) (hz : z ∈ polydisc c R) :
    AnalyticAt ℂ f z := by
  have hsub : closedPolydisc z (fun i => R i - dist (z i) (c i)) ⊆
      closedPolydisc c R := by
    intro w hw
    refine mem_closedPolydisc.2 fun i => ?_
    have h1 : dist (w i) (z i) ≤ R i - dist (z i) (c i) :=
      mem_closedBall.1 (mem_closedPolydisc.1 hw i)
    have h2 := dist_triangle (w i) (z i) (c i)
    exact mem_closedBall.2 (by linarith)
  exact analyticAt_of_differentiableOn_closedPolydisc (hf.mono hsub)
    fun i => sub_pos.2 (mem_ball.1 (mem_polydisc.1 hz i))

/-- A function complex differentiable on a closed polydisc is (jointly)
analytic on a neighborhood of each point of the open polydisc.-/
theorem analyticOnNhd_polydisc [CompleteSpace E] {f : (Fin n → ℂ) → E}
    {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hf : DifferentiableOn ℂ f (closedPolydisc c R)) :
    AnalyticOnNhd ℂ f (polydisc c R) := fun _ hz =>
  analyticAt_of_mem_polydisc hf hz

end PolydiscCauchy
end HodgePilot
