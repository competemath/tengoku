import Tengoku.Seed.MeasureTheory.Integral.TorusIntegral
import Tengoku.Seed.MeasureTheory.Function.LocallyIntegrable
import Tengoku.Seed.Analysis.Complex.CauchyIntegral
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Analysis.Complex.Norm
import Tengoku.Seed.Analysis.Complex.Trigonometric
import Tengoku.Seed.Analysis.SpecialFunctions.Exp
import Tengoku.Seed.Analysis.Calculus.FDeriv.Prod
import Tengoku.Seed.Analysis.Calculus.FDeriv.Comp
import Tengoku.Seed.Analysis.Calculus.FDeriv.Add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Cauchy integral formula on closed polydiscs in `ℂⁿ`

Stage 1 of the several-complex-variables campaign (route P1 of
`wall1_poincare_design_memo.md` §4.4): the **polydisc Cauchy integral
formula** in torus-integral (distinguished-boundary) form.  If
`f : (Fin n → ℂ) → E` is complex differentiable (in the joint, Fréchet
sense) on the closed polydisc `closedPolydisc c R`, and `z` lies in the
open polydisc, then

`∯ w in T(c, R), (∏ i, (w i - z i)⁻¹) • f w = (2 π I) ^ n • f z`,

where `∯ w in T(c, R)` is Mathlib's `torusIntegral` over the
distinguished boundary `{w | ∀ i, |w i - c i| = R i}`.  The proof
iterates the one-variable Cauchy integral formula
(`DifferentiableOn.circleIntegral_sub_inv_smul`) through the
dimension recurrence `torusIntegral_succAbove`/`torusIntegral_succ`,
exactly as priced in the design memo (the "pre-paid `TorusIntegral`
skeleton").  The formula holds for `f` valued in any complete normed
`ℂ`-vector space, in every dimension `n` (for `n = 0` it degenerates to
`f c = f c`; for `n = 1` it is the classical circle formula).

## Main declarations

* `HodgePilot.PolydiscCauchy.polydisc`, `closedPolydisc`: open/closed
  polydiscs in `Fin n → ℂ` as `Set.pi` of discs.
* `HodgePilot.PolydiscCauchy.torusIntegral_sub_inv_smul`: the Cauchy
  integral formula on a closed polydisc, stated above.
* `HodgePilot.PolydiscCauchy.inv_smul_torusIntegral_sub_inv`: the
  normalized reproducing form `((2πI)^n)⁻¹ • ∯ … = f z`.
* Supporting layer: `continuous_torusMap`,
  `norm_torusMap_apply_sub_center`, `torusMap_mem_closedPolydisc`,
  `torusMap_sub_ne_zero`, `cons_mem_closedPolydisc`,
  `torusIntegrable_kernel_smul`.

## Scope discipline

This module contains **integral-formula content only** (stage 1 of the
memo's staged route).  It does **not** provide: the power-series
expansion of the Cauchy kernel, full-polydisc joint power series,
Osgood's lemma, "separately/Fréchet differentiable ⇒ jointly analytic"
in several variables, Cauchy inequalities, or any statement toward a
several-variables holomorphic Poincaré lemma.  Those are later stages
of the campaign and are not claimed anywhere here.  No comparison-type
statement of any kind is made.
-/

open Metric Set MeasureTheory

namespace HodgePilot
namespace PolydiscCauchy

/-! ## Polydiscs -/

/-- The open polydisc in `Fin n → ℂ` with center `c` and (componentwise)
radius `R`: the set of `z` with `‖z i - c i‖ < R i` for every `i`.-/
def polydisc {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) : Set (Fin n → ℂ) :=
  Set.pi Set.univ fun i => ball (c i) (R i)

/-- The closed polydisc in `Fin n → ℂ` with center `c` and (componentwise)
radius `R`: the set of `z` with `‖z i - c i‖ ≤ R i` for every `i`.-/
def closedPolydisc {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) : Set (Fin n → ℂ) :=
  Set.pi Set.univ fun i => closedBall (c i) (R i)

@[simp]
theorem mem_polydisc {n : ℕ} {c z : Fin n → ℂ} {R : Fin n → ℝ} :
    z ∈ polydisc c R ↔ ∀ i, z i ∈ ball (c i) (R i) :=
  Set.mem_univ_pi

@[simp]
theorem mem_closedPolydisc {n : ℕ} {c z : Fin n → ℂ} {R : Fin n → ℝ} :
    z ∈ closedPolydisc c R ↔ ∀ i, z i ∈ closedBall (c i) (R i) :=
  Set.mem_univ_pi

theorem polydisc_subset_closedPolydisc {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) :
    polydisc c R ⊆ closedPolydisc c R := fun _ hz =>
  mem_closedPolydisc.2 fun i => ball_subset_closedBall (mem_polydisc.1 hz i)

/-- Prepending a point of the closed disc in the `0`-th coordinate to a point
of the tail closed polydisc lands in the full closed polydisc.-/
theorem cons_mem_closedPolydisc {n : ℕ} {c : Fin (n + 1) → ℂ} {R : Fin (n + 1) → ℝ}
    {x : ℂ} {y : Fin n → ℂ} (hx : x ∈ closedBall (c 0) (R 0))
    (hy : y ∈ closedPolydisc (c ∘ Fin.succ) (R ∘ Fin.succ)) :
    Fin.cons x y ∈ closedPolydisc c R := by
  have hy' : ∀ j : Fin n, y j ∈ closedBall (c j.succ) (R j.succ) := mem_closedPolydisc.1 hy
  refine mem_closedPolydisc.2 ?_
  rw [Fin.forall_fin_succ]
  refine ⟨?_, fun j => ?_⟩
  · simpa using hx
  · simpa using hy' j

/-! ## The torus map and the Cauchy kernel -/

/-- The torus parametrization `torusMap c R` is continuous.-/
theorem continuous_torusMap {n : ℕ} (c : Fin n → ℂ) (R : Fin n → ℝ) :
    Continuous (torusMap c R) := by
  refine continuous_pi fun i => ?_
  have h : (fun θ : Fin n → ℝ => torusMap c R θ i)
      = fun θ : Fin n → ℝ => c i + (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) := rfl
  rw [h]
  exact continuous_const.add (continuous_const.mul (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_apply i)).mul continuous_const)))

/-- Each coordinate of `torusMap c R θ` lies at distance exactly `R i` from the
center (for `0 ≤ R i`).-/
theorem norm_torusMap_apply_sub_center {n : ℕ} (c : Fin n → ℂ) {R : Fin n → ℝ}
    {i : Fin n} (hR : 0 ≤ R i) (θ : Fin n → ℝ) :
    ‖torusMap c R θ i - c i‖ = R i := by
  have h : torusMap c R θ i - c i = (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) := by
    have h0 : torusMap c R θ i = c i + (R i : ℂ) * Complex.exp ((θ i : ℂ) * Complex.I) := rfl
    rw [h0, add_sub_cancel_left]
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg hR]

/-- The distinguished boundary (torus) is contained in the closed polydisc.-/
theorem torusMap_mem_closedPolydisc {n : ℕ} {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hR : ∀ i, 0 ≤ R i) (θ : Fin n → ℝ) :
    torusMap c R θ ∈ closedPolydisc c R :=
  mem_closedPolydisc.2 fun i =>
    mem_closedBall_iff_norm.2 (le_of_eq (norm_torusMap_apply_sub_center c (hR i) θ))

/-- The Cauchy kernel does not vanish on the distinguished boundary: for `z`
in the open polydisc, `torusMap c R θ i ≠ z i` in every coordinate.-/
theorem torusMap_sub_ne_zero {n : ℕ} {c z : Fin n → ℂ} {R : Fin n → ℝ}
    (hz : z ∈ polydisc c R) (θ : Fin n → ℝ) (i : Fin n) :
    torusMap c R θ i - z i ≠ 0 := by
  have hzi : ‖z i - c i‖ < R i := mem_ball_iff_norm.1 (mem_polydisc.1 hz i)
  have hRi : 0 ≤ R i := (norm_nonneg _).trans hzi.le
  intro h
  rw [sub_eq_zero] at h
  have h1 : ‖z i - c i‖ = R i := by
    rw [← h]
    exact norm_torusMap_apply_sub_center c hRi θ
  exact hzi.ne h1

/-- For `z` in the open polydisc and `f` continuous on the closed polydisc, the
Cauchy-kernel-weighted integrand `w ↦ (∏ i, (w i - z i)⁻¹) • f w` is torus
integrable.-/
theorem torusIntegrable_kernel_smul {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : (Fin n → ℂ) → E} {c z : Fin n → ℂ} {R : Fin n → ℝ}
    (hz : z ∈ polydisc c R) (hf : ContinuousOn f (closedPolydisc c R)) :
    TorusIntegrable (fun w => (∏ i, (w i - z i)⁻¹) • f w) c R := by
  have hR : ∀ i, 0 ≤ R i := fun i =>
    dist_nonneg.trans (mem_ball.1 (mem_polydisc.1 hz i)).le
  have hker : Continuous fun θ : Fin n → ℝ => ∏ i, (torusMap c R θ i - z i)⁻¹ := by
    refine continuous_finsetProd _ fun i _ => ?_
    refine Continuous.inv₀ ?_ fun θ => torusMap_sub_ne_zero hz θ i
    exact ((continuous_apply i).comp (continuous_torusMap c R)).sub continuous_const
  have hfc : ContinuousOn (fun θ : Fin n → ℝ => f (torusMap c R θ))
      (Set.Icc (0 : Fin n → ℝ) fun _ => 2 * Real.pi) :=
    hf.comp (continuous_torusMap c R).continuousOn
      fun θ _ => torusMap_mem_closedPolydisc hR θ
  exact (hker.continuousOn.smul hfc).integrableOn_Icc

/-! ## The Cauchy integral formula on a closed polydisc -/

/-- **Cauchy integral formula on a closed polydisc** (torus-integral form).
If `f : (Fin n → ℂ) → E` is complex differentiable (jointly, in the Fréchet
sense over `ℂ`) on the closed polydisc with center `c` and radii `R`, and `z`
lies in the open polydisc, then

`∯ w in T(c, R), (∏ i, (w i - z i)⁻¹) • f w = (2 * π * I) ^ n • f z`.

The integral is over the distinguished boundary
`{w | ∀ i, ‖w i - c i‖ = R i}` (an `n`-torus), not over the full topological
boundary of the polydisc.  Proof: induction on `n`, splitting off the `0`-th
coordinate by `torusIntegral_succ` and applying the one-variable Cauchy
integral formula in that coordinate.

This is integral-formula content only: no power-series expansion of the
kernel and no analyticity consequence in several variables is derived or
claimed here.-/
theorem torusIntegral_sub_inv_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] :
    ∀ {n : ℕ} {f : (Fin n → ℂ) → E} {c z : Fin n → ℂ} {R : Fin n → ℝ},
      DifferentiableOn ℂ f (closedPolydisc c R) → z ∈ polydisc c R →
      (∯ w in T(c, R), (∏ i, (w i - z i)⁻¹) • f w)
        = (2 * (Real.pi : ℂ) * Complex.I) ^ n • f z := by
  intro n
  induction n with
  | zero =>
    intro f c z R _ _
    have hzc : z = c := Subsingleton.elim z c
    subst hzc
    simp only [Fin.prod_univ_zero, one_smul, pow_zero, torusIntegral_dim0]
  | succ n ih =>
    intro f c z R hf hz
    have hzb : ∀ i, z i ∈ ball (c i) (R i) := mem_polydisc.1 hz
    have hR0 : 0 < R 0 := dist_nonneg.trans_lt (mem_ball.1 (hzb 0))
    have hti : TorusIntegrable (fun w => (∏ i, (w i - z i)⁻¹) • f w) c R :=
      torusIntegrable_kernel_smul hz hf.continuousOn
    have hztail : (z ∘ Fin.succ) ∈ polydisc (c ∘ Fin.succ) (R ∘ Fin.succ) :=
      mem_polydisc.2 fun j => hzb j.succ
    -- On the circle `|x - c 0| = R 0`, the inner `n`-torus integral is
    -- computed by the induction hypothesis.
    have hcong : Set.EqOn
        (fun x : ℂ => ∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) • f (Fin.cons x y))
        (fun x : ℂ => (x - z 0)⁻¹ •
          ((2 * (Real.pi : ℂ) * Complex.I) ^ n • f (Fin.cons x (z ∘ Fin.succ))))
        (sphere (c 0) (R 0)) := by
      intro x hx
      have hxmem : x ∈ closedBall (c 0) (R 0) := sphere_subset_closedBall hx
      have hconsR : Differentiable ℂ (fun y : Fin n → ℂ => (Fin.cons x y : Fin (n + 1) → ℂ)) :=
        fun y => DifferentiableAt.finCons (F' := fun _ => ℂ)
          (differentiableAt_const x) differentiableAt_id
      have hfx : DifferentiableOn ℂ (fun y : Fin n → ℂ => f (Fin.cons x y))
          (closedPolydisc (c ∘ Fin.succ) (R ∘ Fin.succ)) :=
        hf.fun_comp hconsR.differentiableOn fun y hy => cons_mem_closedPolydisc hxmem hy
      have hsplit : (fun y : Fin n → ℂ =>
            (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) • f (Fin.cons x y))
          = fun y : Fin n → ℂ => (x - z 0)⁻¹ •
              ((∏ j, (y j - (z ∘ Fin.succ) j)⁻¹) • f (Fin.cons x y)) := by
        funext y
        rw [Fin.prod_univ_succ, mul_smul]
        simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
      calc (∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ),
              (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) • f (Fin.cons x y))
          = ∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ), (x - z 0)⁻¹ •
              ((∏ j, (y j - (z ∘ Fin.succ) j)⁻¹) • f (Fin.cons x y)) := by rw [hsplit]
        _ = (x - z 0)⁻¹ • ∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ),
              (∏ j, (y j - (z ∘ Fin.succ) j)⁻¹) • f (Fin.cons x y) :=
            torusIntegral_smul ((x - z 0)⁻¹)
              (fun y => (∏ j, (y j - (z ∘ Fin.succ) j)⁻¹) • f (Fin.cons x y))
              (c ∘ Fin.succ) (R ∘ Fin.succ)
        _ = (x - z 0)⁻¹ •
              ((2 * (Real.pi : ℂ) * Complex.I) ^ n • f (Fin.cons x (z ∘ Fin.succ))) :=
            congrArg (fun t => (x - z 0)⁻¹ • t) (ih hfx hztail)
    -- The slice through the tail point is differentiable on the closed disc.
    have hconsL : Differentiable ℂ
        (fun t : ℂ => (Fin.cons t (z ∘ Fin.succ) : Fin (n + 1) → ℂ)) :=
      fun t => DifferentiableAt.finCons (F' := fun _ => ℂ)
        differentiableAt_id (differentiableAt_const _)
    have hslice : DifferentiableOn ℂ
        (fun x : ℂ => (2 * (Real.pi : ℂ) * Complex.I) ^ n • f (Fin.cons x (z ∘ Fin.succ)))
        (closedBall (c 0) (R 0)) := by
      refine DifferentiableOn.fun_const_smul ?_ _
      exact hf.fun_comp hconsL.differentiableOn
        fun x hx => cons_mem_closedPolydisc hx (polydisc_subset_closedPolydisc _ _ hztail)
    calc (∯ w in T(c, R), (∏ i, (w i - z i)⁻¹) • f w)
        = ∮ x in C(c 0, R 0), ∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ),
            (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) • f (Fin.cons x y) := torusIntegral_succ hti
      _ = ∮ x in C(c 0, R 0), (x - z 0)⁻¹ •
            ((2 * (Real.pi : ℂ) * Complex.I) ^ n • f (Fin.cons x (z ∘ Fin.succ))) :=
          circleIntegral.integral_congr hR0.le hcong
      _ = (2 * (Real.pi : ℂ) * Complex.I) •
            ((2 * (Real.pi : ℂ) * Complex.I) ^ n • f (Fin.cons (z 0) (z ∘ Fin.succ))) :=
          hslice.circleIntegral_sub_inv_smul (hzb 0)
      _ = (2 * (Real.pi : ℂ) * Complex.I) ^ (n + 1) • f z := by
          have hzz : Fin.cons (z 0) (z ∘ Fin.succ) = z := Fin.cons_self_tail z
          rw [smul_smul,
            mul_comm (2 * (Real.pi : ℂ) * Complex.I) ((2 * (Real.pi : ℂ) * Complex.I) ^ n),
            ← pow_succ, hzz]

/-! ## Corollaries -/

/-- The Cauchy normalization constant `(2πI)^n` is nonzero.-/
theorem two_pi_I_pow_ne_zero (n : ℕ) : (2 * (Real.pi : ℂ) * Complex.I) ^ n ≠ 0 :=
  pow_ne_zero n (mul_ne_zero (mul_ne_zero two_ne_zero
    (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) Complex.I_ne_zero)

end PolydiscCauchy
end HodgePilot
