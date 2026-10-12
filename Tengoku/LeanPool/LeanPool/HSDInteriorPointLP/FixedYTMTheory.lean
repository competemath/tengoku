/-
Copyright (c) 2026 Makoto Yamashita. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Makoto Yamashita
-/
module

public import Tengoku.LeanPool.LeanPool.HSDInteriorPointLP.LocalNeighborhoodEstimates
public import Tengoku

/-!
# Fixed YTM convergence ingredients

This file is the fixed part obtained after merging the old `v126` and `v127`
interface.  It exposes the Newton direction, the fixed predictor step, the local
predictor/corrector guarantees, and the contraction/log-bound lemmas used by the
algorithm-level proof.

It deliberately does not contain a user-supplied sequence `w : Nat → HSState n`.
That older interface was removed because the generated-algorithm interface in
`GeneratedConvergence.lean` constructs the iterates recursively and makes the
algorithm dependency clearer.
-/

@[expose] public section
noncomputable section

open scoped BigOperators

namespace HSDInteriorPointLP

/-!
## Lean tactic reading guide for this file

The mathematical content below is the YTM local analysis.  The short Lean tactics
used in the proofs have the following roles.

* `intro h` turns a goal of the form `P → Q` into the new assumption `h : P`
  and the remaining goal `Q`.  For `∀ x, ...`, it introduces the quantified
  variable.
* `have h : P := by ...` proves an intermediate mathematical fact and gives it
  the name `h` for later use.
* `rcases h with ⟨h1, h2, ...⟩` decomposes a conjunction or existential proof.
  It corresponds to unpacking the components of a theorem such as
  `0 < α ∧ α ≤ 1 ∧ ...`.
* `simp only [...]` rewrites only by the listed definitions and lemmas.  This is
  safer than unrestricted `simp`, because a later change in the imported library
  is less likely to change the proof.
* `simpa [defs] using h` means: simplify the current goal and the type of `h`
  using `defs`, then use `h`.  Most occurrences here only unfold names such as
  `ytmPredictorAlpha` or remove a harmless `1 - 0`.
* `ring` proves polynomial identities over real numbers, for example rearranging
  `(1 - a * (1 - 0))` into `1 - a`.
* `linarith` proves linear inequalities from the hypotheses.  It is used only
  when the remaining goal is linear in the real variables.
* `nlinarith` is the nonlinear version, used when products such as
  `hdim n * ε` or squares appear.
* `field_simp [h₁, h₂]` clears denominators using the supplied nonzero proofs;
  this is used only for algebraic cancellation in positive denominators.
-/

/-! ## Predictor scaled-direction algebra for the remaining v106 obligation -/

/-- Step 1, vector part: the predictor complementarity equation in quotient form. -/
theorem predictor_component_quotient_sum_eq_neg_one {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hinterior : Interior w)
    (hdir : HSDStepDirection w d 0) (i : Fin n) :
    d.dx i / w.x i + d.ds i / w.s i = -1 := by
  rcases hinterior with ⟨hxpos, htpos, hspos, hkpos⟩
  have hxne : w.x i ≠ 0 := ne_of_gt (hxpos i)
  have hsne : w.s i ≠ 0 := ne_of_gt (hspos i)
  have hlin : w.x i * d.ds i + w.s i * d.dx i = -(w.x i * w.s i) := by
    have hc := hdir.compl.component_eq i
    simpa using hc
  field_simp [hxne, hsne]
  nlinarith [hlin]

/-- Step 1, scalar part: the predictor scalar complementarity equation in quotient form. -/
theorem predictor_scalar_quotient_sum_eq_neg_one {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hinterior : Interior w)
    (hdir : HSDStepDirection w d 0) :
    d.dtau / w.tau + d.dkappa / w.kappa = -1 := by
  rcases hinterior with ⟨hxpos, htpos, hspos, hkpos⟩
  have htne : w.tau ≠ 0 := ne_of_gt htpos
  have hkne : w.kappa ≠ 0 := ne_of_gt hkpos
  have hlin : w.tau * d.dkappa + w.kappa * d.dtau = -(w.tau * w.kappa) := by
    have hc := hdir.compl.scalar_eq
    simpa using hc
  field_simp [htne, hkne]
  nlinarith [hlin]

/-- Step 2: skew orthogonality rewritten in quotient variables. -/
theorem predictor_quotient_weighted_cross_zero {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hinterior : Interior w)
    (hdir : HSDStepDirection w d 0) :
    (∑ i : Fin n,
        (w.x i * w.s i) * (d.dx i / w.x i) * (d.ds i / w.s i)) +
      (w.tau * w.kappa) * (d.dtau / w.tau) * (d.dkappa / w.kappa) = 0 := by
  rcases hinterior with ⟨hxpos, htpos, hspos, hkpos⟩
  have hvec :
      (∑ i : Fin n,
          (w.x i * w.s i) * (d.dx i / w.x i) * (d.ds i / w.s i)) =
        ∑ i : Fin n, d.dx i * d.ds i := by
    apply Finset.sum_congr rfl
    intro i _
    have hxne : w.x i ≠ 0 := ne_of_gt (hxpos i)
    have hsne : w.s i ≠ 0 := ne_of_gt (hspos i)
    field_simp [hxne, hsne]
  have hscalar :
      (w.tau * w.kappa) * (d.dtau / w.tau) * (d.dkappa / w.kappa) =
        d.dtau * d.dkappa := by
    have htne : w.tau ≠ 0 := ne_of_gt htpos
    have hkne : w.kappa ≠ 0 := ne_of_gt hkpos
    field_simp [htne, hkne]
  have hzero : (∑ i : Fin n, d.dx i * d.ds i) + d.dtau * d.dkappa = 0 := by
    simpa [hdot, dot] using hdir.skew.cross_zero
  simp_all

/-- Step 3: the total complementarity product is `hdim n * mu w`. -/
theorem complementarity_total_eq_hdim_mul_mu {n : Nat} (w : HSState n) :
    (∑ i : Fin n, w.x i * w.s i) + w.tau * w.kappa = hdim n * mu w := by
  have hdim_ne : hdim n ≠ 0 := ne_of_gt (hdim_pos n)
  unfold mu gap hdot dot
  field_simp [hdim_ne]

/-- Algebraic identity from `u + v = -1`: it is used componentwise in Step 4. -/
theorem square_sum_eq_one_sub_two_mul_of_sum_eq_neg_one
    {u v : ℝ} (h : u + v = -1) :
    u ^ 2 + v ^ 2 = 1 - 2 * (u * v) := by
  calc
    u ^ 2 + v ^ 2 = (u + v) ^ 2 - 2 * (u * v) := by ring
    _ = 1 - 2 * (u * v) := by
      simp_all

/-- Step 4: weighted norm identity for predictor quotient variables. -/
theorem predictor_weighted_relative_norm_identity {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hdir : HSDStepDirection w d 0) :
    (∑ i : Fin n,
        (w.x i * w.s i) *
          ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2)) +
      (w.tau * w.kappa) *
        ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2) =
      hdim n * mu w := by
  let crossVec : Fin n → ℝ := fun i =>
    (w.x i * w.s i) * (d.dx i / w.x i) * (d.ds i / w.s i)
  let crossScalar : ℝ :=
    (w.tau * w.kappa) * (d.dtau / w.tau) * (d.dkappa / w.kappa)
  have hvec_rewrite :
      (∑ i : Fin n,
          (w.x i * w.s i) *
            ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2)) =
        (∑ i : Fin n, w.x i * w.s i) - 2 * (∑ i : Fin n, crossVec i) := by
    calc
      (∑ i : Fin n,
          (w.x i * w.s i) *
            ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2))
          = ∑ i : Fin n, (w.x i * w.s i) * (1 - 2 *
              ((d.dx i / w.x i) * (d.ds i / w.s i))) := by
              apply Finset.sum_congr rfl
              intro i _
              have hsum := predictor_component_quotient_sum_eq_neg_one
                w d hneigh.1 hdir i
              rw [square_sum_eq_one_sub_two_mul_of_sum_eq_neg_one hsum]
      _ = ∑ i : Fin n, ((w.x i * w.s i) - 2 * crossVec i) := by
              apply Finset.sum_congr rfl
              intro i _
              dsimp [crossVec]
              ring
      _ = (∑ i : Fin n, w.x i * w.s i) - 2 * (∑ i : Fin n, crossVec i) := by
              rw [Finset.sum_sub_distrib]
              rw [← Finset.mul_sum]
  have hscalar_rewrite :
      (w.tau * w.kappa) *
          ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2) =
        w.tau * w.kappa - 2 * crossScalar := by
    have hsum := predictor_scalar_quotient_sum_eq_neg_one w d hneigh.1 hdir
    rw [square_sum_eq_one_sub_two_mul_of_sum_eq_neg_one hsum]
    dsimp [crossScalar]
    ring
  have hcross : (∑ i : Fin n, crossVec i) + crossScalar = 0 := by
    dsimp [crossVec, crossScalar]
    exact predictor_quotient_weighted_cross_zero w d hneigh.1 hdir
  have htotal := complementarity_total_eq_hdim_mul_mu w
  calc
    (∑ i : Fin n,
        (w.x i * w.s i) *
          ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2)) +
      (w.tau * w.kappa) *
        ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2)
        = ((∑ i : Fin n, w.x i * w.s i) - 2 * (∑ i : Fin n, crossVec i)) +
            (w.tau * w.kappa - 2 * crossScalar) := by
            rw [hvec_rewrite, hscalar_rewrite]
    _ = ((∑ i : Fin n, w.x i * w.s i) + w.tau * w.kappa) -
          2 * ((∑ i : Fin n, crossVec i) + crossScalar) := by ring
    _ = hdim n * mu w := by
          simp_all

/-- Step 5, vector part: tight-neighborhood lower bound `3μ/4 ≤ xᵢsᵢ`. -/
theorem neighborhood_component_product_lower_tight {n : Nat}
    (w : HSState n) (hneigh : HSDNeighborhood ytmBetaTight w) (i : Fin n) :
    (3 / 4 : ℝ) * mu w ≤ w.x i * w.s i := by
  have hlower := product_lower_of_deviation_sq
    (mul_nonneg hneigh.2.1.le (mu_pos_of_neighborhood ytmBetaTight w hneigh).le)
    (neighborhood_component_dev_sq_le_bound ytmBetaTight w hneigh i)
  norm_num only [ytmBetaTight, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] at hlower
  exact hlower

/-- Step 5, scalar part: tight-neighborhood lower bound `3μ/4 ≤ τκ`. -/
theorem neighborhood_scalar_product_lower_tight {n : Nat}
    (w : HSState n) (hneigh : HSDNeighborhood ytmBetaTight w) :
    (3 / 4 : ℝ) * mu w ≤ w.tau * w.kappa := by
  have hlower := product_lower_of_deviation_sq
    (mul_nonneg hneigh.2.1.le (mu_pos_of_neighborhood ytmBetaTight w hneigh).le)
    (neighborhood_scalar_dev_sq_le_bound ytmBetaTight w hneigh)
  norm_num only [ytmBetaTight, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] at hlower
  exact hlower

/-- Cancel the positive duality measure once for either quotient-square estimate. -/
theorem quotient_square_bounds_of_weighted_bound {μ z D u v : ℝ}
    (hμ : 0 < μ) (hz : (3 / 4 : ℝ) * μ ≤ z)
    (hweighted : z * (u ^ 2 + v ^ 2) ≤ D * μ) :
    u ^ 2 ≤ (4 / 3 : ℝ) * D ∧ v ^ 2 ≤ (4 / 3 : ℝ) * D := by
  have hscaled := (mul_le_mul_of_nonneg_right hz
    (add_nonneg (sq_nonneg u) (sq_nonneg v))).trans hweighted
  have hcancel : (3 / 4 : ℝ) * (u ^ 2 + v ^ 2) ≤ D := by
    apply (mul_le_mul_iff_left₀ hμ).mp
    calc
      (3 / 4 : ℝ) * (u ^ 2 + v ^ 2) * μ =
          ((3 / 4 : ℝ) * μ) * (u ^ 2 + v ^ 2) := by ring
      _ ≤ D * μ := hscaled
  constructor <;> linarith only [hcancel, sq_nonneg u, sq_nonneg v]

/-- Step 6, vector part: the weighted identity gives componentwise quotient-square bounds. -/
theorem predictor_component_quotient_square_bounds {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hdir : HSDStepDirection w d 0) (i : Fin n) :
    (d.dx i / w.x i) ^ 2 ≤ (4 / 3 : ℝ) * hdim n ∧
      (d.ds i / w.s i) ^ 2 ≤ (4 / 3 : ℝ) * hdim n := by
  rcases hneigh.1 with ⟨hxpos, htpos, hspos, hkpos⟩
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaTight w hneigh
  have hweighted := predictor_weighted_relative_norm_identity w d hneigh hdir
  let termVec : Fin n → ℝ := fun j =>
    (w.x j * w.s j) *
      ((d.dx j / w.x j) ^ 2 + (d.ds j / w.s j) ^ 2)
  let termScalar : ℝ :=
    (w.tau * w.kappa) *
      ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2)
  have hterm_nonneg : ∀ j : Fin n, 0 ≤ termVec j := by
    intro j
    dsimp [termVec]
    exact mul_nonneg
      (mul_nonneg (le_of_lt (hxpos j)) (le_of_lt (hspos j)))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hscalar_nonneg : 0 ≤ termScalar := by
    dsimp [termScalar]
    exact mul_nonneg
      (mul_nonneg (le_of_lt htpos) (le_of_lt hkpos))
      (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hsingle : termVec i ≤ ∑ j : Fin n, termVec j := by
    exact Finset.single_le_sum (fun j _ => hterm_nonneg j) (by simp)
  have hterm_le_total : termVec i ≤ hdim n * mu w := by
    calc
      termVec i ≤ (∑ j : Fin n, termVec j) + termScalar :=
        hsingle.trans (le_add_of_nonneg_right hscalar_nonneg)
      _ = hdim n * mu w := by
          dsimp [termVec, termScalar]
          exact hweighted
  exact quotient_square_bounds_of_weighted_bound hmu
    (neighborhood_component_product_lower_tight w hneigh i) hterm_le_total

/-- Step 6, scalar part: quotient-square bounds for `τ` and `κ`. -/
theorem predictor_scalar_quotient_square_bounds {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hdir : HSDStepDirection w d 0) :
    (d.dtau / w.tau) ^ 2 ≤ (4 / 3 : ℝ) * hdim n ∧
      (d.dkappa / w.kappa) ^ 2 ≤ (4 / 3 : ℝ) * hdim n := by
  rcases hneigh.1 with ⟨hxpos, htpos, hspos, hkpos⟩
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaTight w hneigh
  have hweighted := predictor_weighted_relative_norm_identity w d hneigh hdir
  let termVec : Fin n → ℝ := fun j =>
    (w.x j * w.s j) *
      ((d.dx j / w.x j) ^ 2 + (d.ds j / w.s j) ^ 2)
  let termScalar : ℝ :=
    (w.tau * w.kappa) *
      ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2)
  have hvec_nonneg : 0 ≤ ∑ j : Fin n, termVec j := by
    exact Finset.sum_nonneg (fun j _ => by
      dsimp [termVec]
      exact mul_nonneg
        (mul_nonneg (le_of_lt (hxpos j)) (le_of_lt (hspos j)))
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hscalar_le_total : termScalar ≤ hdim n * mu w := by
    calc
      termScalar ≤ (∑ j : Fin n, termVec j) + termScalar :=
        le_add_of_nonneg_left hvec_nonneg
      _ = hdim n * mu w := by
          dsimp [termVec, termScalar]
          exact hweighted
  exact quotient_square_bounds_of_weighted_bound hmu
    (neighborhood_scalar_product_lower_tight w hneigh) hscalar_le_total

/-- A convenient stronger numerical bound for the fixed YTM constant. -/
theorem ytmStepConstant_le_half : ytmStepConstant ≤ (1 / 2 : ℝ) := by
  unfold ytmStepConstant
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt (8 : ℝ) := by
    simp_all
  have hden_pos : 0 < (8 : ℝ) ^ 2 * Real.sqrt (8 : ℝ) := by
    positivity
  rw [div_le_iff₀ hden_pos]
  nlinarith [hsqrt_ge_one]

/-- The fixed alpha cancels the homogenized dimension after squaring. -/
theorem predictor_fixed_alpha_sq_mul_hdim (n : Nat) :
    (predictorFixedAlpha n) ^ 2 * hdim n = ytmStepConstant ^ 2 := by
  unfold predictorFixedAlpha
  have hsqrt_ne : Real.sqrt (hdim n) ≠ 0 := ne_of_gt (sqrt_hdim_pos n)
  have hsqrt_sq : (Real.sqrt (hdim n)) ^ 2 = hdim n := by
    exact Real.sq_sqrt (le_of_lt (hdim_pos n))
  field_simp [hsqrt_ne]
  rw [hsqrt_sq]

/-- Step 7: fixed-alpha constant evaluation used by the scaled bounds. -/
theorem predictor_fixed_alpha_sq_four_thirds_hdim_lt_one (n : Nat) :
    (predictorFixedAlpha n) ^ 2 * ((4 / 3 : ℝ) * hdim n) < 1 := by
  have hcancel := predictor_fixed_alpha_sq_mul_hdim n
  have hc_nonneg : 0 ≤ ytmStepConstant := le_of_lt ytmStepConstant_pos
  have hc_le : ytmStepConstant ≤ (1 / 2 : ℝ) := ytmStepConstant_le_half
  have hc_sq : ytmStepConstant ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith
  calc
    (predictorFixedAlpha n) ^ 2 * ((4 / 3 : ℝ) * hdim n)
        = (4 / 3 : ℝ) * ((predictorFixedAlpha n) ^ 2 * hdim n) := by ring
    _ = (4 / 3 : ℝ) * ytmStepConstant ^ 2 := by rw [hcancel]
    _ ≤ (4 / 3 : ℝ) * ((1 / 2 : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hc_sq (by norm_num)
    _ < 1 := by norm_num

/-- Step 8: square bound plus fixed-alpha constant bound gives an absolute bound. -/
theorem abs_alpha_mul_lt_one_of_square_bound
    (α u B : ℝ) (hu : u ^ 2 ≤ B) (hαB : α ^ 2 * B < 1) :
    |α * u| < 1 := by
  have hsq_le : (α * u) ^ 2 ≤ α ^ 2 * B := by
    calc
      (α * u) ^ 2 = α ^ 2 * u ^ 2 := by ring
      _ ≤ α ^ 2 * B := by
          exact mul_le_mul_of_nonneg_left hu (sq_nonneg α)
  have hsq_lt : (α * u) ^ 2 < 1 := lt_of_le_of_lt hsq_le hαB
  simp_all

/-! ## Predictor center-bound estimates for Steps 9--12 -/

/-- Elementary estimate `|uv| ≤ (u² + v²)/2`. -/
theorem abs_mul_le_half_sq_add_sq (u v : ℝ) :
    |u * v| ≤ (u ^ 2 + v ^ 2) / 2 := by
  rw [abs_mul]
  have hsq : 0 ≤ (|u| - |v|) ^ 2 := sq_nonneg _
  have hu_sq : |u| ^ 2 = u ^ 2 := sq_abs u
  have hv_sq : |v| ^ 2 = v ^ 2 := sq_abs v
  nlinarith [hsq, hu_sq, hv_sq]

/-- Step 9, ℓ₁ version: the sum of absolute second-order predictor products is
bounded by half of the weighted relative norm. -/
theorem predictor_second_order_l1_bound {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hdir : HSDStepDirection w d 0) :
    (∑ i : Fin n, |d.dx i * d.ds i|) + |d.dtau * d.dkappa| ≤
      hdim n * mu w / 2 := by
  rcases hneigh.1 with ⟨hxpos, htpos, hspos, hkpos⟩
  have hweighted := predictor_weighted_relative_norm_identity w d hneigh hdir
  have hvec :
      (∑ i : Fin n, |d.dx i * d.ds i|) ≤
        ∑ i : Fin n,
          ((w.x i * w.s i) *
            ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2)) / 2 := by
    exact Finset.sum_le_sum (fun i _ => by
      have hxne : w.x i ≠ 0 := ne_of_gt (hxpos i)
      have hsne : w.s i ≠ 0 := ne_of_gt (hspos i)
      have hprod_pos : 0 < w.x i * w.s i := mul_pos (hxpos i) (hspos i)
      have hrepr :
          (w.x i * w.s i) * (d.dx i / w.x i) * (d.ds i / w.s i) =
            d.dx i * d.ds i := by
        field_simp [hxne, hsne]
      calc
        |d.dx i * d.ds i|
            = |(w.x i * w.s i) * ((d.dx i / w.x i) * (d.ds i / w.s i))| := by
                rw [← hrepr]
                ring_nf
        _ = (w.x i * w.s i) * |(d.dx i / w.x i) * (d.ds i / w.s i)| := by
                rw [abs_mul, abs_of_pos hprod_pos]
        _ ≤ (w.x i * w.s i) *
              (((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2) / 2) := by
                exact mul_le_mul_of_nonneg_left
                  (abs_mul_le_half_sq_add_sq (d.dx i / w.x i) (d.ds i / w.s i))
                  (le_of_lt hprod_pos)
        _ = ((w.x i * w.s i) *
              ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2)) / 2 := by
                ring)
  have hscalar :
      |d.dtau * d.dkappa| ≤
        ((w.tau * w.kappa) *
          ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2)) / 2 := by
    have htne : w.tau ≠ 0 := ne_of_gt htpos
    have hkne : w.kappa ≠ 0 := ne_of_gt hkpos
    have hprod_pos : 0 < w.tau * w.kappa := mul_pos htpos hkpos
    have hrepr :
        (w.tau * w.kappa) * (d.dtau / w.tau) * (d.dkappa / w.kappa) =
          d.dtau * d.dkappa := by
      field_simp [htne, hkne]
    calc
      |d.dtau * d.dkappa|
          = |(w.tau * w.kappa) * ((d.dtau / w.tau) * (d.dkappa / w.kappa))| := by
              rw [← hrepr]
              ring_nf
      _ = (w.tau * w.kappa) * |(d.dtau / w.tau) * (d.dkappa / w.kappa)| := by
              rw [abs_mul, abs_of_pos hprod_pos]
      _ ≤ (w.tau * w.kappa) *
            (((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2) / 2) := by
              exact mul_le_mul_of_nonneg_left
                (abs_mul_le_half_sq_add_sq (d.dtau / w.tau) (d.dkappa / w.kappa))
                (le_of_lt hprod_pos)
      _ = ((w.tau * w.kappa) *
            ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2)) / 2 := by
              ring
  calc
    (∑ i : Fin n, |d.dx i * d.ds i|) + |d.dtau * d.dkappa|
        ≤ (∑ i : Fin n,
            ((w.x i * w.s i) *
              ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2)) / 2) +
          ((w.tau * w.kappa) *
            ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2)) / 2 := by
            exact add_le_add hvec hscalar
    _ = ((∑ i : Fin n,
            (w.x i * w.s i) *
              ((d.dx i / w.x i) ^ 2 + (d.ds i / w.s i) ^ 2) ) +
          (w.tau * w.kappa) *
            ((d.dtau / w.tau) ^ 2 + (d.dkappa / w.kappa) ^ 2)) / 2 := by
            rw [← Finset.sum_div]
            ring
    _ = hdim n * mu w / 2 := by
            rw [hweighted]

/-- Step 9: second-order predictor products have the required square-sum bound. -/
theorem predictor_second_order_square_sum_bound {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hdir : HSDStepDirection w d 0) :
    (∑ i : Fin n, (d.dx i * d.ds i) ^ 2) +
      (d.dtau * d.dkappa) ^ 2 ≤ (hdim n * mu w / 2) ^ 2 := by
  have hl1 := predictor_second_order_l1_bound w d hneigh hdir
  have hsquares := sum_sq_add_sq_le_l1_sq
    (fun i : Fin n => d.dx i * d.ds i) (d.dtau * d.dkappa)
  have hmu : 0 < mu w := mu_pos_of_neighborhood ytmBetaTight w hneigh
  have hL_nonneg :
      0 ≤ (∑ i : Fin n, |d.dx i * d.ds i|) + |d.dtau * d.dkappa| := by
    exact add_nonneg
      (Finset.sum_nonneg (fun i _ => abs_nonneg (d.dx i * d.ds i)))
      (abs_nonneg (d.dtau * d.dkappa))
  have hQ_nonneg : 0 ≤ hdim n * mu w / 2 := by
    nlinarith [hdim_pos n, hmu]
  have hsq_l1 :
      ((∑ i : Fin n, |d.dx i * d.ds i|) + |d.dtau * d.dkappa|) ^ 2 ≤
        (hdim n * mu w / 2) ^ 2 := by
    nlinarith
  exact le_trans hsquares hsq_l1

/-- The old centrality residual, in the sign convention used by the predictor residual,
is bounded by the tight neighborhood radius. -/
theorem predictor_old_residual_square_sum_bound {n : Nat}
    (w : HSState n) (hneigh : HSDNeighborhood ytmBetaTight w) :
    (∑ i : Fin n, (w.x i * w.s i - mu w) ^ 2) +
      (w.tau * w.kappa - mu w) ^ 2 ≤ (ytmBetaTight * mu w) ^ 2 := by
  have hcenter := neighborhood_centerSq_le ytmBetaTight w hneigh
  unfold centerSq at hcenter
  exact hcenter

/-- Pointwise two-term square inequality used as a square-sum version of the triangle
estimate for Step 10. -/
theorem sq_add_le_two_sq_add_two_sq (x y : ℝ) :
    (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  have hsq : 0 ≤ (x - y) ^ 2 := sq_nonneg _
  nlinarith

/-- Step 10/11: applying the two-term square estimate componentwise to the predictor
residual split.  This is a slightly stronger bookkeeping form than introducing a
separate Euclidean norm object. -/
theorem predictor_residual_split_square_sum_bound {n : Nat}
    (a b : ℝ) (r q : Fin n → ℝ) (ρ η : ℝ) :
    (∑ i : Fin n, (a * r i + b * q i) ^ 2) + (a * ρ + b * η) ^ 2 ≤
      2 * a ^ 2 * ((∑ i : Fin n, (r i) ^ 2) + ρ ^ 2) +
      2 * b ^ 2 * ((∑ i : Fin n, (q i) ^ 2) + η ^ 2) := by
  have hvec :
      (∑ i : Fin n, (a * r i + b * q i) ^ 2) ≤
        ∑ i : Fin n, (2 * (a * r i) ^ 2 + 2 * (b * q i) ^ 2) := by
    exact Finset.sum_le_sum (fun i _ => sq_add_le_two_sq_add_two_sq (a * r i) (b * q i))
  have hscalar :
      (a * ρ + b * η) ^ 2 ≤ 2 * (a * ρ) ^ 2 + 2 * (b * η) ^ 2 :=
    sq_add_le_two_sq_add_two_sq (a * ρ) (b * η)
  calc
    (∑ i : Fin n, (a * r i + b * q i) ^ 2) + (a * ρ + b * η) ^ 2
        ≤ (∑ i : Fin n, (2 * (a * r i) ^ 2 + 2 * (b * q i) ^ 2)) +
            (2 * (a * ρ) ^ 2 + 2 * (b * η) ^ 2) := by
            exact add_le_add hvec hscalar
    _ = 2 * a ^ 2 * ((∑ i : Fin n, (r i) ^ 2) + ρ ^ 2) +
        2 * b ^ 2 * ((∑ i : Fin n, (q i) ^ 2) + η ^ 2) := by
            calc
              (∑ i : Fin n, (2 * (a * r i) ^ 2 + 2 * (b * q i) ^ 2)) +
                  (2 * (a * ρ) ^ 2 + 2 * (b * η) ^ 2)
                  = ((∑ i : Fin n, 2 * a ^ 2 * (r i) ^ 2) +
                      (∑ i : Fin n, 2 * b ^ 2 * (q i) ^ 2)) +
                    (2 * a ^ 2 * ρ ^ 2 + 2 * b ^ 2 * η ^ 2) := by
                      rw [Finset.sum_add_distrib]
                      congr 2
                      · apply Finset.sum_congr rfl
                        intro i _
                        simp only [mul_pow]
                        ring
                      · apply Finset.sum_congr rfl
                        intro i _
                        simp only [mul_pow]
                        ring
                      · simp only [mul_pow]
                        ring
                      · simp only [mul_pow]
                        ring
              _ = 2 * a ^ 2 * ((∑ i : Fin n, (r i) ^ 2) + ρ ^ 2) +
                  2 * b ^ 2 * ((∑ i : Fin n, (q i) ^ 2) + η ^ 2) := by
                      rw [← Finset.mul_sum, ← Finset.mul_sum]
                      ring

/-- The fixed predictor step length is at most one half. -/
theorem predictor_fixed_alpha_le_half (n : Nat) :
    predictorFixedAlpha n ≤ (1 / 2 : ℝ) := by
  unfold predictorFixedAlpha
  have hden : 0 < Real.sqrt (hdim n) := sqrt_hdim_pos n
  rw [div_le_iff₀ hden]
  have hc := ytmStepConstant_le_half
  have hs := one_le_sqrt_hdim n
  nlinarith

/-!
# Active predictor obligation after splitting fixed material

All already-fixed algebra and neighborhood bookkeeping have been moved to
`LocalNeighborhoodEstimates`.  This file starts with the only remaining analytic
predictor estimate, followed by the small wrappers that turn it into the existing
local-theory statements.
-/

/-- Corrector estimate used in the YTM proof.

This packages the corrector half of Theorem 6: starting from the wide neighborhood
`N(1/2)`, the corrector direction with `γ = 1` accepts the full step and returns to the
tight neighborhood `N(1/4)`. -/
structure YTMCorrectorEstimate (n : Nat) : Prop where
  estimate : ∀ (w : HSState n) (d : HSDirection n),
    HSDNeighborhood ytmBetaWide w →
    HSDStepDirection w d 1 →
    CorrectorStepGuarantee ytmBetaTight w d

/-- Corrector half of the YTM local neighborhood analysis. -/
theorem YTM_corrector_estimate_from_paper (n : Nat) :
    YTMCorrectorEstimate n := by
  refine ⟨?_⟩
  intro w d hneigh hdir
  have hlocal := YTM_corrector_full_step_local_estimate w d hneigh hdir
  have hgap : gap (addStep w d 1) = gap w := by
    rw [gap_addStep_of_HSDStepDirection w d 1 1 hdir]
    ring
  exact
    { interior_next := hlocal.1
      neighborhood_next := hlocal.2
      gap_preserve := hgap }

/-- Local predictor estimate used in YTM Theorem 6, obtained from the fixed-parameter
local theory. -/
theorem predictor_step_guarantee_fixed {n : Nat}
    (T : YTMFixedLocalTheory n)
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaTight w)
    (hdir : HSDStepDirection w d 0) :
    ∃ α, PredictorStepGuarantee ytmBetaWide ytmStepConstant w d α :=
  T.predictor_estimate_fixed w d hneigh hdir

/-- Local corrector estimate used in YTM Theorem 6, obtained from the fixed-parameter
local theory. -/
theorem corrector_step_guarantee_fixed {n : Nat}
    (T : YTMFixedLocalTheory n)
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaWide w)
    (hdir : HSDStepDirection w d 1) :
    CorrectorStepGuarantee ytmBetaTight w d :=
  T.corrector_estimate_fixed w d hneigh hdir

/-- Canonical Newton direction selected from the full-row-rank HLP linear algebra. -/
noncomputable def HSDNewtonDirection {m n : Nat}
    (P : LPData m n) (std : LPStandardAssumptions P)
    (w : HSState n) (hw : Interior w) (γ : ℝ) : HSDirection n :=
  chooseSearchDirection w γ
    ((HLP_newton_linear_algebra_from_full_row_rank P std).direction_system_solvable
      std w hw γ)

/-- The selected Newton direction satisfies the reduced HSD step-direction equations. -/
theorem HSDNewtonDirection_step {m n : Nat}
    (P : LPData m n) (std : LPStandardAssumptions P)
    (w : HSState n) (hw : Interior w) (γ : ℝ) :
    HSDStepDirection w (HSDNewtonDirection P std w hw γ) γ := by
  unfold HSDNewtonDirection
  exact chosen_step_direction w γ _

/-- Fixed predictor step size used in the YTM estimate. -/
def ytmPredictorAlpha (n : Nat) : ℝ :=
  ytmStepConstant / Real.sqrt (hdim n)

/-- Corrector local guarantee from the YTM wide-to-tight estimate. -/
theorem corrector_step_guarantee_of_wide {n : Nat}
    (w : HSState n) (d : HSDirection n)
    (hneigh : HSDNeighborhood ytmBetaWide w)
    (hdir : HSDStepDirection w d 1) :
    CorrectorStepGuarantee ytmBetaTight w d :=
  (YTM_corrector_estimate_from_paper n).estimate w d hneigh hdir

/-- The contraction factor appearing in the two-step YTM estimate. -/
def ytmContraction (n : Nat) : ℝ :=
  1 - ytmStepConstant / Real.sqrt (hdim n)

/-- The two-step contraction factor is nonnegative. -/
theorem ytmContraction_nonneg (n : Nat) :
    0 ≤ ytmContraction n := by
  unfold ytmContraction
  have hα : ytmStepConstant / Real.sqrt (hdim n) ≤ 1 :=
    predictor_alpha_fixed_le_one n
  linarith

/-- The two-step contraction factor is at most one. -/
theorem ytmContraction_le_one (n : Nat) :
    ytmContraction n ≤ 1 := by
  unfold ytmContraction
  have hα_nonneg : 0 ≤ ytmStepConstant / Real.sqrt (hdim n) :=
    le_of_lt (predictor_alpha_fixed_pos n)
  linarith

/-- The two-step contraction factor is strictly less than one. -/
theorem ytmContraction_lt_one (n : Nat) :
    ytmContraction n < 1 := by
  unfold ytmContraction
  have hα_pos : 0 < ytmStepConstant / Real.sqrt (hdim n) :=
    predictor_alpha_fixed_pos n
  linarith

/-- Collected bounds for the two-step contraction factor. -/
theorem ytmContraction_bounds (n : Nat) :
    0 ≤ ytmContraction n ∧ ytmContraction n < 1 := by
  exact ⟨ytmContraction_nonneg n, ytmContraction_lt_one n⟩

/-- The contraction factor is exactly `1 - a_n`, where
`a_n = ytmStepConstant / sqrt(hdim n)`. -/
theorem ytmContraction_eq_one_sub_alpha (n : Nat) :
    ytmContraction n = 1 - ytmStepConstant / Real.sqrt (hdim n) := by
  rfl

/-- The reciprocal scale used in the logarithmic iteration bound cancels the
YTM step coefficient. -/
theorem ytm_alpha_mul_log_scale (n : Nat) (u : ℝ) :
    (ytmStepConstant / Real.sqrt (hdim n)) *
        ((Real.sqrt (hdim n) / ytmStepConstant) * u) = u := by
  have hc_ne : ytmStepConstant ≠ 0 := ne_of_gt ytmStepConstant_pos
  have hs_ne : Real.sqrt (hdim n) ≠ 0 := ne_of_gt (sqrt_hdim_pos n)
  field_simp [hc_ne, hs_ne]

/-- Elementary exponential majorization used for the YTM contraction: if `a ≤ 1`,
then `(1-a)^K ≤ exp(-aK)`. -/
theorem one_sub_pow_le_exp_neg_mul_nat
    {a : ℝ} (ha_le_one : a ≤ 1) :
    ∀ K : Nat, (1 - a) ^ K ≤ Real.exp (-(a * (K : ℝ))) := by
  intro K
  induction K with
  | zero =>
      simp
  | succ K ih =>
      have hbase : 1 - a ≤ Real.exp (-a) := by
        have h := Real.add_one_le_exp (-a)
        linarith
      have hleft_nonneg : 0 ≤ 1 - a := by
        linarith
      have hexp_nonneg : 0 ≤ Real.exp (-(a * (K : ℝ))) :=
        le_of_lt (Real.exp_pos _)
      calc
        (1 - a) ^ (K + 1)
            = (1 - a) ^ K * (1 - a) := by
                rw [pow_succ]
        _ ≤ Real.exp (-(a * (K : ℝ))) * Real.exp (-a) := by
                exact mul_le_mul ih hbase hleft_nonneg hexp_nonneg
        _ = Real.exp (-a) * Real.exp (-(a * (K : ℝ))) := by
                ring
        _ = Real.exp (-(a * ((K + 1 : Nat) : ℝ))) := by
                rw [← Real.exp_add]
                congr 1
                norm_num
                ring

/-- The YTM contraction power is bounded by the corresponding exponential decay. -/
theorem YTM_contraction_power_le_exp {n : Nat} (K : Nat) :
    (ytmContraction n) ^ K ≤
      Real.exp (-(ytmStepConstant / Real.sqrt (hdim n) * (K : ℝ))) := by
  have ha_le_one : ytmStepConstant / Real.sqrt (hdim n) ≤ 1 :=
    predictor_alpha_fixed_le_one n
  simpa [ytmContraction] using
    one_sub_pow_le_exp_neg_mul_nat ha_le_one K

/-- If the real-valued pair count satisfies the logarithmic lower bound, then the
exponential estimate already puts `gap0` below `ε`. -/
theorem ytm_exp_mul_gap_le_of_log_bound {n : Nat}
    (K : Nat) {gap0 ε : ℝ}
    (hgap0 : 0 < gap0) (hε_pos : 0 < ε)
    (hK : (Real.sqrt (hdim n) / ytmStepConstant) * Real.log (gap0 / ε) ≤
      (K : ℝ)) :
    Real.exp (-(ytmStepConstant / Real.sqrt (hdim n) * (K : ℝ))) * gap0 ≤ ε := by
  let a : ℝ := ytmStepConstant / Real.sqrt (hdim n)
  let scale : ℝ := Real.sqrt (hdim n) / ytmStepConstant
  have ha_nonneg : 0 ≤ a := by
    exact le_of_lt (predictor_alpha_fixed_pos n)
  have hlog_le : Real.log (gap0 / ε) ≤ a * (K : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hK ha_nonneg
    calc
      Real.log (gap0 / ε)
          = a * (scale * Real.log (gap0 / ε)) := by
              dsimp [a, scale]
              rw [ytm_alpha_mul_log_scale]
      _ ≤ a * (K : ℝ) := hmul
  have hratio_pos : 0 < gap0 / ε := div_pos hgap0 hε_pos
  have h_exp_le :
      Real.exp (-(a * (K : ℝ))) ≤ ε / gap0 := by
    calc
      Real.exp (-(a * (K : ℝ)))
          ≤ Real.exp (-(Real.log (gap0 / ε))) := by
              exact Real.exp_le_exp.mpr (by linarith)
      _ = ε / gap0 := by
              rw [Real.exp_neg, Real.exp_log hratio_pos]
              field_simp [ne_of_gt hgap0, ne_of_gt hε_pos]
  calc
    Real.exp (-(ytmStepConstant / Real.sqrt (hdim n) * (K : ℝ))) * gap0
        = Real.exp (-(a * (K : ℝ))) * gap0 := by
            rfl
    _ ≤ (ε / gap0) * gap0 := by
            exact mul_le_mul_of_nonneg_right h_exp_le (le_of_lt hgap0)
    _ = ε := by
            field_simp [ne_of_gt hgap0]

/-- Pair bound written using `L = log(gap0 / ε)`. -/
def ytmLogPairBoundL (n : Nat) (L : ℝ) : Nat :=
  Nat.ceil ((Real.sqrt (hdim n) / ytmStepConstant) * L)

/-- Ordinary iteration bound written using `L = log(gap0 / ε)`. -/
def ytmLogIterationBoundL (n : Nat) (L : ℝ) : Nat :=
  2 * ytmLogPairBoundL n L

/-- Gap-based stopping condition used by the formalized iteration bound. -/
def YTMGapStop {n : Nat} (ε : ℝ) (w : HSState n) : Prop :=
  gap w ≤ ε

/-- Duality-measure stopping condition corresponding to the paper's `μ ≤ ε`. -/
def YTMMuStop {n : Nat} (ε : ℝ) (w : HSState n) : Prop :=
  mu w ≤ ε

/-- Gap stopping immediately gives the formal gap-stop predicate. -/
theorem YTMGapStop_of_gap_le {n : Nat} {w : HSState n} {ε : ℝ}
    (hgap : gap w ≤ ε) :
    YTMGapStop ε w :=
  hgap

/-- Since `μ = gap / hdim`, a scaled gap bound gives the `μ ≤ ε` stopping test. -/
theorem YTMMuStop_of_gap_le_hdim_mul {n : Nat} {w : HSState n} {ε : ℝ}
    (hgap : gap w ≤ hdim n * ε) :
    YTMMuStop ε w := by
  unfold YTMMuStop mu
  rw [div_le_iff₀ (hdim_pos n)]
  nlinarith [hgap]

end HSDInteriorPointLP
