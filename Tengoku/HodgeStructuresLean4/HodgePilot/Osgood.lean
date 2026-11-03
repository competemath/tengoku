import Tengoku.HodgeStructuresLean4.HodgePilot.PolydiscCauchy2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Osgood's lemma on polydiscs in `ℂⁿ`

Stage 3 of the several-complex-variables campaign: **Osgood's lemma**.  A
function `f : (Fin n → ℂ) → E` that is *continuous* and *separately* complex
differentiable (in each variable, the others held fixed) is *jointly analytic*.

The route is the classical one, run entirely on the house polydisc Cauchy
layer:

1. The polydisc Cauchy integral formula
   (`PolydiscCauchy.torusIntegral_sub_inv_smul`) is re-proved under the Osgood
   hypotheses (`torusIntegral_sub_inv_smul_of_separately_differentiableOn`):
   the same induction on dimension applies the one-variable Cauchy integral
   formula coordinate-by-coordinate, and each application needs only the
   corresponding *separate* differentiability; continuity supplies torus
   integrability of every integrand.
2. The stage-2 expansion engine (kernel geometric series, exchange of sum and
   torus integral, `polydiscSeries`) consumes joint differentiability at
   exactly two joints — continuity on the closed polydisc and the Cauchy
   integral formula itself — so it is re-keyed here on those two hypotheses
   (`…_of_cauchy` declarations) with the proofs of
   `HodgePilot.PolydiscCauchy2` otherwise unchanged.
3. Combining 1 and 2: joint analyticity at the center of any closed polydisc
   on which `f` is continuous and separately differentiable
   (`analyticAt_center_of_separately_differentiableOn`), hence, by locality,
   **Osgood's lemma** on an arbitrary open set (`osgood`): continuous plus
   separately differentiable on an open `U` implies `AnalyticOnNhd ℂ f U`.

## Main declarations

* `HodgePilot.Osgood.torusIntegral_sub_inv_smul_of_separately_differentiableOn`:
  the polydisc Cauchy integral formula under continuity plus separate
  differentiability (no joint differentiability hypothesis).
* `HodgePilot.Osgood.hasSum_cauchyCoeff_smul_of_separately_differentiableOn`:
  the monomial Cauchy expansion of such an `f` at every point of the open
  polydisc.
* `HodgePilot.Osgood.hasFPowerSeriesOnBall_of_separately_differentiableOn`:
  the regrouped power series (`PolydiscCauchy.polydiscSeries`) converges to
  `f` on sup-norm balls.
* `HodgePilot.Osgood.analyticAt_center_of_separately_differentiableOn`: joint
  analyticity at the center of the closed polydisc.
* `HodgePilot.Osgood.osgood`: **Osgood's lemma** — `f` continuous on an open
  `U ⊆ (Fin n → ℂ)` and separately complex differentiable at every point of
  `U` is jointly analytic on `U` (`AnalyticOnNhd`).
* `HodgePilot.Osgood.osgood_polydisc`: the same conclusion on the open
  polydisc from hypotheses on a closed polydisc.

## Scope discipline

The continuity hypothesis is essential to this module's method and is
**assumed everywhere, never removed**: Hartogs' theorem (separate
analyticity alone implies joint analyticity, without assuming continuity) is
**not** proved, approached, or claimed anywhere in this development.  All
statements are about functions on subsets of `Fin n → ℂ` with values in a
complete normed `ℂ`-vector space; no statement beyond that scope is made.
-/

open Metric Set MeasureTheory

open scoped NNReal ENNReal

namespace HodgePilot
namespace Osgood

open PolydiscCauchy

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-! ## Slice bookkeeping on polydiscs -/

/-- The open polydisc is open.
@isnad1 id=isopen.0h3v.s5.b67a32fdcf6d from=translated src=- shape=155195a9 vocab=9ffaae1f
-/
theorem isOpen_polydisc (c : Fin n → ℂ) (R : Fin n → ℝ) :
    IsOpen (polydisc c R) :=
  isOpen_set_pi Set.finite_univ fun _ _ => isOpen_ball

/-- Updating one coordinate of a point of the closed polydisc by a point of
the corresponding closed disc stays in the closed polydisc.
@isnad1 id=mem.2h6v.s6.dc1740bd4fe3 from=translated src=- shape=5e811342 vocab=bda0a514
-/
theorem update_mem_closedPolydisc {c w : Fin n → ℂ} {R : Fin n → ℝ}
    (hw : w ∈ closedPolydisc c R) {i : Fin n} {t : ℂ}
    (ht : t ∈ closedBall (c i) (R i)) :
    Function.update w i t ∈ closedPolydisc c R := by
  refine mem_closedPolydisc.2 fun j => ?_
  rcases eq_or_ne j i with rfl | hne
  · simpa using ht
  · rw [Function.update_of_ne hne]
    exact mem_closedPolydisc.1 hw j

/-- Pointwise separate complex differentiability on a set `U` restricts, on
any closed polydisc contained in `U`, to the slicewise `DifferentiableOn`
form consumed by the polydisc Cauchy machinery.
@isnad1 id=differen.3h8v.s8.4d667e5fb6a0 from=translated src=- shape=9b4b7fbf vocab=8b0d3d16
-/
theorem separately_differentiableOn_of_differentiableAt {f : (Fin n → ℂ) → E}
    {U : Set (Fin n → ℂ)}
    (hsep : ∀ (i : Fin n), ∀ w ∈ U,
      DifferentiableAt ℂ (fun t => f (Function.update w i t)) (w i))
    {c : Fin n → ℂ} {R : Fin n → ℝ} (hUR : closedPolydisc c R ⊆ U) :
    ∀ (i : Fin n), ∀ w ∈ closedPolydisc c R,
      DifferentiableOn ℂ (fun t => f (Function.update w i t))
        (closedBall (c i) (R i)) := by
  intro i w hw t ht
  have h := hsep i (Function.update w i t) (hUR (update_mem_closedPolydisc hw ht))
  rw [Function.update_self] at h
  have heq : (fun s => f (Function.update (Function.update w i t) i s))
      = fun s => f (Function.update w i s) :=
    funext fun s => by rw [Function.update_idem]
  rw [heq] at h
  exact h.differentiableWithinAt

/-! ## The Cauchy integral formula under Osgood hypotheses -/

/-- **Cauchy integral formula on a closed polydisc under Osgood hypotheses**
(torus-integral form).  If `f : (Fin n → ℂ) → E` is *continuous* on the
closed polydisc and *separately* complex differentiable there — through every
point `w` of the closed polydisc and in every coordinate `i`, the
one-variable slice `t ↦ f (Function.update w i t)` is differentiable on the
closed disc `closedBall (c i) (R i)` — and `z` lies in the open polydisc,
then

`∯ w in T(c, R), (∏ i, (w i - z i)⁻¹) • f w = (2 * π * I) ^ n • f z`.

No joint differentiability is assumed.  Proof: the induction of
`PolydiscCauchy.torusIntegral_sub_inv_smul`, with the one-variable Cauchy
integral formula fed by the separate hypothesis in the active coordinate and
torus integrability supplied by continuity.
@isnad1 id=eq.3h6v.s8.36e9ccd62765 from=translated src=- shape=4bc54f69 vocab=d749b822
-/
theorem torusIntegral_sub_inv_smul_of_separately_differentiableOn
    [CompleteSpace E] :
    ∀ {n : ℕ} {f : (Fin n → ℂ) → E} {c z : Fin n → ℂ} {R : Fin n → ℝ},
      ContinuousOn f (closedPolydisc c R) →
      (∀ (i : Fin n), ∀ w ∈ closedPolydisc c R,
        DifferentiableOn ℂ (fun t => f (Function.update w i t))
          (closedBall (c i) (R i))) →
      z ∈ polydisc c R →
      (∯ w in T(c, R), (∏ i, (w i - z i)⁻¹) • f w)
        = (2 * (Real.pi : ℂ) * Complex.I) ^ n • f z := by
  intro n
  induction n with
  | zero =>
    intro f c z R _ _ _
    have hzc : z = c := Subsingleton.elim z c
    subst hzc
    simp only [Fin.prod_univ_zero, one_smul, pow_zero, torusIntegral_dim0]
  | succ n ih =>
    intro f c z R hcont hsep hz
    have hzb : ∀ i, z i ∈ ball (c i) (R i) := mem_polydisc.1 hz
    have hR0 : 0 < R 0 := dist_nonneg.trans_lt (mem_ball.1 (hzb 0))
    have hti : TorusIntegrable (fun w => (∏ i, (w i - z i)⁻¹) • f w) c R :=
      torusIntegrable_kernel_smul hz hcont
    have hztail : (z ∘ Fin.succ) ∈ polydisc (c ∘ Fin.succ) (R ∘ Fin.succ) :=
      mem_polydisc.2 fun j => hzb j.succ
    -- On the circle `|x - c 0| = R 0`, the inner `n`-torus integral is
    -- computed by the induction hypothesis applied to the slice, whose Osgood
    -- hypotheses restrict from those of `f`.
    have hcong : Set.EqOn
        (fun x : ℂ => ∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ),
          (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) • f (Fin.cons x y))
        (fun x : ℂ => (x - z 0)⁻¹ •
          ((2 * (Real.pi : ℂ) * Complex.I) ^ n • f (Fin.cons x (z ∘ Fin.succ))))
        (sphere (c 0) (R 0)) := by
      intro x hx
      have hxmem : x ∈ closedBall (c 0) (R 0) := sphere_subset_closedBall hx
      have hconsC : Continuous fun y : Fin n → ℂ =>
          (Fin.cons x y : Fin (n + 1) → ℂ) :=
        continuous_const.finCons continuous_id
      have hcontx : ContinuousOn (fun y : Fin n → ℂ => f (Fin.cons x y))
          (closedPolydisc (c ∘ Fin.succ) (R ∘ Fin.succ)) :=
        hcont.comp hconsC.continuousOn fun y hy => cons_mem_closedPolydisc hxmem hy
      have hsepx : ∀ (j : Fin n), ∀ w ∈ closedPolydisc (c ∘ Fin.succ) (R ∘ Fin.succ),
          DifferentiableOn ℂ
            (fun t => f (Fin.cons x (Function.update w j t)))
            (closedBall ((c ∘ Fin.succ) j) ((R ∘ Fin.succ) j)) := by
        intro j w hw
        have h := hsep j.succ (Fin.cons x w) (cons_mem_closedPolydisc hxmem hw)
        have heq : (fun t => f (Function.update (Fin.cons x w) j.succ t))
            = fun t => f (Fin.cons x (Function.update w j t)) :=
          funext fun t => by rw [Fin.cons_update]
        rw [heq] at h
        exact h
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
            congrArg (fun t => (x - z 0)⁻¹ • t) (ih hcontx hsepx hztail)
    -- The coordinate-0 slice through the tail point is differentiable on the
    -- closed disc, directly from the separate hypothesis.
    have hw0 : (Fin.cons (c 0) (z ∘ Fin.succ) : Fin (n + 1) → ℂ) ∈ closedPolydisc c R :=
      cons_mem_closedPolydisc (mem_closedBall_self hR0.le)
        (polydisc_subset_closedPolydisc _ _ hztail)
    have h0 := hsep 0 _ hw0
    have heq0 : (fun t : ℂ => f (Function.update (Fin.cons (c 0) (z ∘ Fin.succ)) 0 t))
        = fun t : ℂ => f (Fin.cons t (z ∘ Fin.succ)) :=
      funext fun t => by rw [Fin.update_cons_zero]
    rw [heq0] at h0
    have hslice : DifferentiableOn ℂ
        (fun x : ℂ => (2 * (Real.pi : ℂ) * Complex.I) ^ n • f (Fin.cons x (z ∘ Fin.succ)))
        (closedBall (c 0) (R 0)) :=
      DifferentiableOn.fun_const_smul h0 _
    calc (∯ w in T(c, R), (∏ i, (w i - z i)⁻¹) • f w)
        = ∮ x in C(c 0, R 0), ∯ y in T(c ∘ Fin.succ, R ∘ Fin.succ),
            (∏ i, ((Fin.cons x y : Fin (n + 1) → ℂ) i - z i)⁻¹) • f (Fin.cons x y) :=
          torusIntegral_succ hti
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

/-! ## The stage-2 expansion engine, re-keyed on the Cauchy formula

The three declarations below are the stage-2 chain of
`HodgePilot.PolydiscCauchy2` with the joint-differentiability hypothesis
replaced by its two actual uses: continuity on the closed polydisc and the
Cauchy integral formula.  The proofs are those of
`hasSum_torusIntegral_pow_kernel_smul`, `hasSum_cauchyCoeff_smul`, and
`hasFPowerSeriesOnBall_polydiscSeries`, unchanged except at the joints. -/

/-- Exchange of summation and torus integration for the kernel expansion,
from continuity plus the Cauchy integral formula at `z`.
@isnad1 id=hassum.3h6v.s9.f5e91eb8be5f from=translated src=- shape=b9d03260 vocab=3f91a854
-/
theorem hasSum_torusIntegral_pow_kernel_smul_of_cauchy [CompleteSpace E]
    {f : (Fin n → ℂ) → E} {c z : Fin n → ℂ} {R : Fin n → ℝ}
    (hcont : ContinuousOn f (closedPolydisc c R)) (hz : z ∈ polydisc c R)
    (hcauchy : (∯ w in T(c, R), (∏ i, (w i - z i)⁻¹) • f w)
      = (2 * (Real.pi : ℂ) * Complex.I) ^ n • f z) :
    HasSum
      (fun α : Fin n → ℕ => (∏ i, (z i - c i) ^ α i) •
        ∯ w in T(c, R), (∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w)
      ((2 * (Real.pi : ℂ) * Complex.I) ^ n • f z) := by
  have hR : ∀ i, 0 < R i := fun i =>
    dist_nonneg.trans_lt (mem_ball.1 (mem_polydisc.1 hz i))
  obtain ⟨M, hM⟩ :=
    (isCompact_closedPolydisc c R).exists_bound_of_continuousOn hcont
  have hMt : ∀ θ : Fin n → ℝ, ‖f (torusMap c R θ)‖ ≤ M := fun θ =>
    hM _ (torusMap_mem_closedPolydisc (fun i => (hR i).le) θ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMt 0)
  have hzn : ∀ i, ‖z i - c i‖ < R i := fun i =>
    mem_ball_iff_norm.1 (mem_polydisc.1 hz i)
  -- integrability of every full integrand
  have hGint : ∀ α : Fin n → ℕ,
      TorusIntegrable (fun w =>
        ((∏ i, (z i - c i) ^ α i) * ∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w) c R :=
    fun α => torusIntegrable_pow_kernel_smul hR hcont _ α
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
  -- identify the total sum with the Cauchy formula hypothesis
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
    rw [h2, hcauchy]
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

/-- The monomial Cauchy expansion at `z`, from continuity plus the Cauchy
integral formula at `z`.
@isnad1 id=hassum.3h6v.s8.bc7dee838f50 from=translated src=- shape=0ed7a7b6 vocab=2b11ca9d
-/
theorem hasSum_cauchyCoeff_smul_of_cauchy [CompleteSpace E]
    {f : (Fin n → ℂ) → E} {c z : Fin n → ℂ} {R : Fin n → ℝ}
    (hcont : ContinuousOn f (closedPolydisc c R)) (hz : z ∈ polydisc c R)
    (hcauchy : (∯ w in T(c, R), (∏ i, (w i - z i)⁻¹) • f w)
      = (2 * (Real.pi : ℂ) * Complex.I) ^ n • f z) :
    HasSum (fun α : Fin n → ℕ => (∏ i, (z i - c i) ^ α i) • cauchyCoeff f c R α)
      (f z) := by
  have H := (hasSum_torusIntegral_pow_kernel_smul_of_cauchy hcont hz hcauchy).const_smul
    (((2 * (Real.pi : ℂ) * Complex.I) ^ n)⁻¹ : ℂ)
  rw [inv_smul_smul₀ (two_pi_I_pow_ne_zero n)] at H
  have hfun : (fun α : Fin n → ℕ => ((2 * (Real.pi : ℂ) * Complex.I) ^ n)⁻¹ •
      ((∏ i, (z i - c i) ^ α i) •
        ∯ w in T(c, R), (∏ i, ((w i - c i) ^ (α i + 1))⁻¹) • f w)) =
      fun α : Fin n → ℕ => (∏ i, (z i - c i) ^ α i) • cauchyCoeff f c R α :=
    funext fun α => smul_comm _ _ _
  rw [hfun] at H
  exact H

/-- The Cauchy power series converges to `f` on balls, from continuity plus
the Cauchy integral formula at every point of the open polydisc.
@isnad1 id=hasfpowe.4h6v.s8.ba87ce0932c8 from=translated src=- shape=8248e9da vocab=92333022
-/
theorem hasFPowerSeriesOnBall_polydiscSeries_of_cauchy [CompleteSpace E]
    {f : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hcont : ContinuousOn f (closedPolydisc c R))
    (hcauchy : ∀ z ∈ polydisc c R,
      (∯ w in T(c, R), (∏ i, (w i - z i)⁻¹) • f w)
        = (2 * (Real.pi : ℂ) * Complex.I) ^ n • f z)
    {r : ℝ≥0} (hr : 0 < r) (hrR : ∀ i, (r : ℝ) < R i) :
    HasFPowerSeriesOnBall f (polydiscSeries f c R) c r := by
  have hR : ∀ i, 0 < R i := fun i => lt_of_le_of_lt r.coe_nonneg (hrR i)
  obtain ⟨M, hM⟩ :=
    (isCompact_closedPolydisc c R).exists_bound_of_continuousOn hcont
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
  have H := hasSum_cauchyCoeff_smul_of_cauchy hcont hcy (hcauchy _ hcy)
  have hyc : (fun α : Fin n → ℕ =>
      (∏ i, ((c + y) i - c i) ^ α i) • cauchyCoeff f c R α) =
      fun α : Fin n → ℕ => (∏ i, y i ^ α i) • cauchyCoeff f c R α := by
    funext α
    congr 1
    exact Finset.prod_congr rfl fun i _ => by simp
  rw [hyc] at H
  exact ((Equiv.sigmaFiberEquiv fun α : Fin n → ℕ => ∑ i, α i).hasSum_iff.mpr H).sigma
    fun m => hasSum_polydiscSeries_fiber f c R m y

/-! ## Osgood's lemma -/

/-- The Cauchy power series converges to `f` on sup-norm balls under Osgood
hypotheses: continuity plus separate complex differentiability on the closed
polydisc.
@isnad1 id=hasfpowe.4h6v.s8.c324f1a7ffc5 from=translated src=- shape=841c579c vocab=1d4c3f3d
-/
theorem hasFPowerSeriesOnBall_of_separately_differentiableOn [CompleteSpace E]
    {f : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hcont : ContinuousOn f (closedPolydisc c R))
    (hsep : ∀ (i : Fin n), ∀ w ∈ closedPolydisc c R,
      DifferentiableOn ℂ (fun t => f (Function.update w i t))
        (closedBall (c i) (R i)))
    {r : ℝ≥0} (hr : 0 < r) (hrR : ∀ i, (r : ℝ) < R i) :
    HasFPowerSeriesOnBall f (polydiscSeries f c R) c r :=
  hasFPowerSeriesOnBall_polydiscSeries_of_cauchy hcont
    (fun _ hz =>
      torusIntegral_sub_inv_smul_of_separately_differentiableOn hcont hsep hz)
    hr hrR

/-- A function continuous and separately complex differentiable on a closed
polydisc with positive radii is jointly analytic at the center.
@isnad1 id=analytic.3h5v.s8.b9c7d885ddc2 from=translated src=- shape=ecdaa157 vocab=37b388af
-/
theorem analyticAt_center_of_separately_differentiableOn [CompleteSpace E]
    {f : (Fin n → ℂ) → E} {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hcont : ContinuousOn f (closedPolydisc c R))
    (hsep : ∀ (i : Fin n), ∀ w ∈ closedPolydisc c R,
      DifferentiableOn ℂ (fun t => f (Function.update w i t))
        (closedBall (c i) (R i)))
    (hR : ∀ i, 0 < R i) :
    AnalyticAt ℂ f c := by
  obtain ⟨ε, hε0, hεR⟩ := Pi.exists_forall_pos_add_lt (x := fun _ : Fin n => (0 : ℝ))
    (y := R) hR
  have hεR' : ∀ i, ε < R i := fun i => by simpa using hεR i
  exact (hasFPowerSeriesOnBall_of_separately_differentiableOn hcont hsep
    (r := ε.toNNReal) (Real.toNNReal_pos.mpr hε0)
    fun i => by rw [Real.coe_toNNReal ε hε0.le]; exact hεR' i).analyticAt

/-- **Osgood's lemma.**  Let `U ⊆ (Fin n → ℂ)` be open and let
`f : (Fin n → ℂ) → E` (values in a complete normed `ℂ`-vector space) be
continuous on `U` and separately complex differentiable on `U`: through every
point `w ∈ U`, in every coordinate `i`, the one-variable function
`t ↦ f (Function.update w i t)` is complex differentiable at `w i`.  Then `f`
is jointly analytic on `U` (`AnalyticOnNhd ℂ f U`).

The continuity hypothesis is an assumption, not a conclusion: no Hartogs-type
removal of continuity is proved or claimed anywhere in this development.
@isnad1 id=analytic.3h4v.s8.46d2959aad99 from=translated src=- shape=977ef747 vocab=808271af
-/
theorem osgood [CompleteSpace E] {f : (Fin n → ℂ) → E} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hcont : ContinuousOn f U)
    (hsep : ∀ (i : Fin n), ∀ w ∈ U,
      DifferentiableAt ℂ (fun t => f (Function.update w i t)) (w i)) :
    AnalyticOnNhd ℂ f U := by
  intro z hz
  obtain ⟨ε, hε0, hεU⟩ := Metric.isOpen_iff.1 hU z hz
  have hr0 : 0 < ε / 2 := half_pos hε0
  have hsub : closedPolydisc z (fun _ => ε / 2) ⊆ U := by
    intro w hw
    refine hεU (Metric.closedBall_subset_ball (half_lt_self hε0) ?_)
    rw [closedBall_pi _ hr0.le]
    exact hw
  exact analyticAt_center_of_separately_differentiableOn (hcont.mono hsub)
    (separately_differentiableOn_of_differentiableAt hsep hsub) fun _ => hr0

/-- Osgood's lemma, polydisc form: a function continuous and separately
complex differentiable on a closed polydisc is jointly analytic on the open
polydisc.
@isnad1 id=analytic.2h5v.s8.cebcda04c373 from=translated src=- shape=ac9056fc vocab=2285dff5
-/
theorem osgood_polydisc [CompleteSpace E] {f : (Fin n → ℂ) → E}
    {c : Fin n → ℂ} {R : Fin n → ℝ}
    (hcont : ContinuousOn f (closedPolydisc c R))
    (hsep : ∀ (i : Fin n), ∀ w ∈ closedPolydisc c R,
      DifferentiableOn ℂ (fun t => f (Function.update w i t))
        (closedBall (c i) (R i))) :
    AnalyticOnNhd ℂ f (polydisc c R) := by
  refine osgood (isOpen_polydisc c R)
    (hcont.mono (polydisc_subset_closedPolydisc c R)) ?_
  intro i w hw
  exact (hsep i w (polydisc_subset_closedPolydisc c R hw) (w i)
      (ball_subset_closedBall (mem_polydisc.1 hw i))).differentiableAt
    (closedBall_mem_nhds_of_mem (mem_polydisc.1 hw i))

end Osgood
end HodgePilot
