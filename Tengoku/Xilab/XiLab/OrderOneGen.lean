import Tengoku
import Tengoku.Xilab.XiLab.Growth
import Tengoku.Xilab.XiLab.HolomorphicLog

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms eq_exp_affine_of_hasOrderLeOne` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_poly_mul_exp_of_finite_zeros_of_hasOrderLeOne` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_zero_of_not_eq_exp_affine_of_hasOrderLeOne` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms hasOrderLeOne_of_exp_type` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eq_exp_affine_of_exp_type` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_poly_mul_exp_of_finite_zeros_of_exp_type` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# XiLab.OrderOneGen

Hadamard factorization at order `≤ 1` **of arbitrary type**.

Contains no `sorry`.

`XiLab/OrderOne.lean` proves the same factorization statements under
`‖f z‖ ≤ A * exp (B * ‖z‖)`, i.e. order `≤ 1` of *finite exponential* type. The odd channel
of the Riemann kernel satisfies `log max_{‖w‖ = r} ‖F‖ ≤ (r/2) log r + O(r)`, which
outgrows every `B * r`, so `F` is order `1` of *maximal* type and those theorems do not
apply to it. This file removes that gap: everything is proved from `XiLab.HasOrderLeOne`
(`XiLab/Growth.lean`), the shared predicate

  `∀ ε > 0, ∃ C > 0, ∀ z, ‖f z‖ ≤ C * exp (C * ‖z‖ ^ (1 + ε))`.

## Main results

* `XiLab.eq_exp_affine_of_hasOrderLeOne` — entire, nowhere zero, order `≤ 1` ⟹ `exp (a z + b)`.
* `XiLab.exists_poly_mul_exp_of_finite_zeros_of_hasOrderLeOne` — with finitely many zeros,
  `f = P(z) exp (a z + b)`.
* `XiLab.exists_zero_of_not_eq_exp_affine_of_hasOrderLeOne` — the contrapositive the
  application consumes.
* `XiLab.hasOrderLeOne_of_exp_type` — finite exponential type implies `HasOrderLeOne`, so the
  `XiLab/OrderOne.lean` results remain reachable (`eq_exp_affine_of_exp_type` and
  `exists_poly_mul_exp_of_finite_zeros_of_exp_type` restate them through this bridge).

## Route, and the one step that genuinely changes

Steps 1–3 follow `XiLab/OrderOne.lean`: an entire nowhere-zero `f` is `exp ∘ g`
(`XiLab.exists_entire_log`, owned by `XiLab/HolomorphicLog.lean`); the growth bound makes
`Re g` at most `L + C Φ‖z‖`; and `Complex.borelCaratheodory` upgrades that one-sided bound to
`‖g z‖ ≤ K Φ‖z‖`. Here `ε` is fixed **once and for all at `1/2`**, so the profile is

  `Φ r = (1 + r) * √(1 + r) = (1 + r) ^ (3/2)`,

carried through as `XiLab.phi32` — a product of a linear factor and a square root, which
keeps `rpow` out of every estimate after the very first one.

Step 4 is where finite type and maximal type part company. At finite type a single Cauchy
estimate bounds `‖g'‖` uniformly and Liouville finishes. At maximal type the same estimate
only gives `‖g' w‖ ≤ 6K √(1 + ‖w‖)`, which is unbounded, so Liouville does not apply. The
fix is a *second* Cauchy estimate, on `g'` over the circle of radius `R` about `w`:

  `‖g'' w‖ ≤ (3/2) K √R / R = (3/2) K / √R → 0`  as `R → ∞`,

for every fixed `w`. So `g'' ≡ 0` pointwise — no Liouville needed at the second stage at
all — and `g` is affine by `is_const_of_deriv_eq_zero` applied twice. The sublinear exponent
`1/2 < 1` is exactly what makes the quotient vanish, which is why `ε < 1` suffices and why
`ε` never has to be taken arbitrarily small.
-/

namespace XiLab

open Metric Set Bornology

/-! ## The growth profile `Φ r = (1 + r) ^ (3/2)` -/

/-- `phi32 r = (1 + r) * √(1 + r)`, i.e. `(1 + r) ^ (3/2)` written without `rpow`.-/
noncomputable def phi32 (r : ℝ) : ℝ := (1 + r) * Real.sqrt (1 + r)

theorem one_le_sqrt_one_add {r : ℝ} (hr : 0 ≤ r) : (1 : ℝ) ≤ Real.sqrt (1 + r) :=
  (Real.le_sqrt (by norm_num) (by linarith)).mpr (by nlinarith)

theorem one_le_phi32 {r : ℝ} (hr : 0 ≤ r) : 1 ≤ phi32 r := by
  have h2 : (1 : ℝ) ≤ Real.sqrt (1 + r) := one_le_sqrt_one_add hr
  unfold phi32
  nlinarith

theorem phi32_nonneg {r : ℝ} (hr : 0 ≤ r) : 0 ≤ phi32 r := le_trans zero_le_one (one_le_phi32 hr)

/-- Monotonicity of the profile.-/
theorem phi32_mono {r s : ℝ} (hr : 0 ≤ r) (h : r ≤ s) : phi32 r ≤ phi32 s := by
  have h3 : Real.sqrt (1 + r) ≤ Real.sqrt (1 + s) := Real.sqrt_le_sqrt (by linarith)
  have h4 : (0 : ℝ) ≤ Real.sqrt (1 + r) := Real.sqrt_nonneg _
  unfold phi32
  nlinarith

/-- `√3 ≤ 2`.-/
theorem sqrt_three_le_two : Real.sqrt 3 ≤ 2 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]

/-- `√2 ≤ 3/2`.-/
theorem sqrt_two_le : Real.sqrt 2 ≤ 3 / 2 := by
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]

/-- The scaling estimate: enlarging the argument so that `1 + x ≤ 3 * (1 + r)` costs at
most a factor `6` in the profile (`3 * √3 ≤ 6`).-/
theorem phi32_le_six_mul {x r : ℝ} (hr : 0 ≤ r) (h : 1 + x ≤ 3 * (1 + r)) :
    phi32 x ≤ 6 * phi32 r := by
  have hr1 : (0 : ℝ) < 1 + r := by linarith
  have hsqrt : Real.sqrt (1 + x) ≤ 2 * Real.sqrt (1 + r) := by
    calc Real.sqrt (1 + x) ≤ Real.sqrt (3 * (1 + r)) := Real.sqrt_le_sqrt h
      _ = Real.sqrt 3 * Real.sqrt (1 + r) := Real.sqrt_mul (by norm_num) _
      _ ≤ 2 * Real.sqrt (1 + r) := by
          have := Real.sqrt_nonneg (1 + r)
          nlinarith [sqrt_three_le_two]
  have hxn : (0 : ℝ) ≤ Real.sqrt (1 + x) := Real.sqrt_nonneg _
  unfold phi32
  nlinarith [Real.sqrt_nonneg (1 + r)]

/-- `r ^ (3/2 : ℝ) ≤ Φ r`.-/
theorem rpow_three_halves_le_phi32 {r : ℝ} (hr : 0 ≤ r) : r ^ ((3 : ℝ) / 2) ≤ phi32 r := by
  have h1 : (0 : ℝ) < 1 + r := by linarith
  have h2 : r ^ ((3 : ℝ) / 2) ≤ (1 + r) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hr (by linarith) (by norm_num)
  refine h2.trans (le_of_eq ?_)
  have h3 : ((3 : ℝ) / 2) = 1 + 1 / 2 := by norm_num
  rw [h3, Real.rpow_add h1, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rfl

/-! ## Borel–Carathéodory at the `3/2` profile -/

/-- **Borel–Carathéodory, global form at profile `Φ`.** If `g` is entire and
`Re (g z) ≤ L + B * Φ ‖z‖` with `B ≥ 0`, then `‖g‖` itself is `O(Φ)`.-/
theorem norm_le_phi32_of_re_le_phi32 {g : ℂ → ℂ} (hg : Differentiable ℂ g) {L B : ℝ}
    (hB : 0 ≤ B) (hre : ∀ z, (g z).re ≤ L + B * phi32 ‖z‖) (z : ℂ) :
    ‖g z‖ ≤ (2 * |L| + 12 * B + 2 + 3 * ‖g 0‖) * phi32 ‖z‖ := by
  have ht : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hp1 : (1 : ℝ) ≤ phi32 ‖z‖ := one_le_phi32 ht
  have hL : (0 : ℝ) ≤ |L| := abs_nonneg L
  have h0 : (0 : ℝ) ≤ ‖g 0‖ := norm_nonneg _
  have hR : (0 : ℝ) < 2 * ‖z‖ + 2 := by linarith
  have hMpos : (0 : ℝ) < |L| + 6 * B * phi32 ‖z‖ + 1 := by nlinarith
  have hmaps : Set.MapsTo g (ball 0 (2 * ‖z‖ + 2))
      {w : ℂ | w.re ≤ |L| + 6 * B * phi32 ‖z‖ + 1} := by
    intro x hx
    have hx' : ‖x‖ < 2 * ‖z‖ + 2 := mem_ball_zero_iff.mp hx
    have hle : phi32 ‖x‖ ≤ 6 * phi32 ‖z‖ := phi32_le_six_mul ht (by linarith)
    have h1 : (g x).re ≤ L + B * phi32 ‖x‖ := hre x
    have h2 : B * phi32 ‖x‖ ≤ B * (6 * phi32 ‖z‖) := mul_le_mul_of_nonneg_left hle hB
    have h3 : L ≤ |L| := le_abs_self L
    simp only [Set.mem_ofPred_eq]
    linarith
  have hz : z ∈ ball (0 : ℂ) (2 * ‖z‖ + 2) := by rw [mem_ball_zero_iff]; linarith
  have hbc := Complex.borelCaratheodory hMpos hg.differentiableOn hmaps hR hz
  have hden : (0 : ℝ) < 2 * ‖z‖ + 2 - ‖z‖ := by linarith
  have hbc' : ‖g z‖ ≤ 2 * (|L| + 6 * B * phi32 ‖z‖ + 1) + 3 * ‖g 0‖ := by
    refine hbc.trans ?_
    rw [← add_div, div_le_iff₀ hden]
    nlinarith [hMpos.le, ht, h0]
  nlinarith [mul_nonneg hL (sub_nonneg.mpr hp1), mul_nonneg h0 (sub_nonneg.mpr hp1)]

/-! ## First Cauchy estimate: `‖g'‖ = O(√(1 + ‖w‖))` -/

/-- Cauchy's estimate on the circle of radius `1 + ‖w‖` about `w`: a `Φ`-bound on `g`
gives a `√`-bound on `deriv g`.-/
theorem norm_deriv_le_sqrt_of_phi32_growth {g : ℂ → ℂ} (hg : Differentiable ℂ g) {K : ℝ}
    (hK : 0 ≤ K) (hgrow : ∀ z, ‖g z‖ ≤ K * phi32 ‖z‖) (w : ℂ) :
    ‖deriv g w‖ ≤ 6 * K * Real.sqrt (1 + ‖w‖) := by
  have hw : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hR : (0 : ℝ) < 1 + ‖w‖ := by linarith
  have hC : ∀ x ∈ sphere w (1 + ‖w‖), ‖g x‖ ≤ K * (6 * phi32 ‖w‖) := by
    intro x hx
    have hxw : ‖x - w‖ = 1 + ‖w‖ := mem_sphere_iff_norm.1 hx
    have hxn : ‖x‖ ≤ ‖w‖ + (1 + ‖w‖) := by
      have h := norm_add_le (x - w) w
      rw [hxw] at h
      simpa [sub_add_cancel] using h.trans_eq (by ring)
    have hle : phi32 ‖x‖ ≤ 6 * phi32 ‖w‖ := phi32_le_six_mul hw (by linarith)
    calc ‖g x‖ ≤ K * phi32 ‖x‖ := hgrow x
      _ ≤ K * (6 * phi32 ‖w‖) := by gcongr
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hg.diffContOnCl hC
  refine hd.trans (le_of_eq ?_)
  rw [div_eq_iff (ne_of_gt hR)]
  unfold phi32
  ring

/-! ## Second Cauchy estimate: `g'' ≡ 0` -/

/-- **The step that finite type does not need.** If `‖deriv g w‖ ≤ K * √(1 + ‖w‖)` then the
*second* derivative vanishes identically. Cauchy's estimate for `deriv g` on the circle of
radius `R` about `w` bounds `‖deriv (deriv g) w‖` by `(3/2) K √R / R = (3/2) K / √R`, which
tends to `0` as `R → ∞`; the sublinear exponent `1/2 < 1` is exactly what makes this work,
and it is why maximal type still forces an affine logarithm.-/
theorem deriv_deriv_eq_zero_of_sqrt_growth {g : ℂ → ℂ} (hg : Differentiable ℂ g) {K : ℝ}
    (hK : 0 ≤ K) (hgrow : ∀ w, ‖deriv g w‖ ≤ K * Real.sqrt (1 + ‖w‖)) (w : ℂ) :
    deriv (deriv g) w = 0 := by
  rw [← norm_le_zero_iff]
  refine le_of_forall_gt_imp_ge_of_dense fun δ hδ => ?_
  have hw : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  set R : ℝ := max (1 + ‖w‖) ((3 * K / (2 * δ)) ^ 2 + 1) with hR_def
  have hR1 : 1 + ‖w‖ ≤ R := le_max_left _ _
  have hR2 : (3 * K / (2 * δ)) ^ 2 + 1 ≤ R := le_max_right _ _
  have hR : (0 : ℝ) < R := by linarith
  have hsR : (0 : ℝ) < Real.sqrt R := Real.sqrt_pos.mpr hR
  have hδ' : (0 : ℝ) < 2 * δ := by linarith
  have hkey : 3 * K / (2 * δ) ≤ Real.sqrt R := by
    have hnn : (0 : ℝ) ≤ 3 * K / (2 * δ) := by positivity
    exact (Real.le_sqrt hnn hR.le).mpr (by linarith)
  have hkey2 : 3 * K ≤ 2 * δ * Real.sqrt R := by
    rw [div_le_iff₀ hδ'] at hkey
    linarith
  have hC : ∀ x ∈ sphere w R, ‖deriv g x‖ ≤ K * (3 / 2 * Real.sqrt R) := by
    intro x hx
    have hxw : ‖x - w‖ = R := mem_sphere_iff_norm.1 hx
    have hxn : ‖x‖ ≤ ‖w‖ + R := by
      have h := norm_add_le (x - w) w
      rw [hxw] at h
      simpa [sub_add_cancel] using h.trans_eq (by ring)
    have h1 : 1 + ‖x‖ ≤ 2 * R := by linarith
    have h2 : Real.sqrt (1 + ‖x‖) ≤ 3 / 2 * Real.sqrt R := by
      calc Real.sqrt (1 + ‖x‖) ≤ Real.sqrt (2 * R) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt 2 * Real.sqrt R := Real.sqrt_mul (by norm_num) _
        _ ≤ 3 / 2 * Real.sqrt R := by nlinarith [sqrt_two_le, hsR.le]
    calc ‖deriv g x‖ ≤ K * Real.sqrt (1 + ‖x‖) := hgrow x
      _ ≤ K * (3 / 2 * Real.sqrt R) := by gcongr
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hg.deriv.diffContOnCl hC
  refine hd.trans ?_
  rw [div_le_iff₀ hR]
  have h5 := mul_le_mul_of_nonneg_right hkey2 hsR.le
  have h6 : 2 * δ * Real.sqrt R * Real.sqrt R = 2 * δ * R := by
    rw [mul_assoc, Real.mul_self_sqrt hR.le]
  linarith

/-! ## Liouville, via the vanishing second derivative -/

/-- An entire function whose second derivative vanishes identically is affine.-/
theorem eq_affine_of_deriv_deriv_eq_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (h : ∀ w, deriv (deriv g) w = 0) : ∃ c : ℂ, ∀ z, g z = c * z + g 0 := by
  have hconst : ∀ x, deriv g x = deriv g 0 := fun x => is_const_of_deriv_eq_zero hg.deriv h x 0
  refine ⟨deriv g 0, fun z => ?_⟩
  set c : ℂ := deriv g 0 with hc_def
  have hdiff : Differentiable ℂ fun t : ℂ => g t - c * t := by fun_prop
  have hzero : ∀ x : ℂ, deriv (fun t : ℂ => g t - c * t) x = 0 := by
    intro x
    have h1 : HasDerivAt g (deriv g x) x := (hg x).hasDerivAt
    have h2 : HasDerivAt (fun t : ℂ => c * t) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have h3 : HasDerivAt (fun t : ℂ => g t - c * t) (deriv g x - c) x := h1.sub h2
    rw [h3.deriv, hconst x]
    ring
  have hh := is_const_of_deriv_eq_zero hdiff hzero z 0
  simp only [mul_zero, sub_zero] at hh
  linear_combination hh

/-! ## Main theorem: order `≤ 1`, no zeros -/

/-- **An entire function of order at most one with no zeros is `exp` of an affine function.**
Unlike `XiLab.eq_exp_affine_of_order_le_one` this needs only `HasOrderLeOne`, i.e. order
`≤ 1` of *arbitrary* type, so it applies to `ξ`-like kernels whose growth is `r log r`.-/
theorem eq_exp_affine_of_hasOrderLeOne {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnz : ∀ z, f z ≠ 0) (hord : HasOrderLeOne f) :
    ∃ a b : ℂ, ∀ z, f z = Complex.exp (a * z + b) := by
  obtain ⟨g, hg, hfg⟩ := exists_entire_log hf hnz
  obtain ⟨C, hC, hCz⟩ := hord (1 / 2) (by norm_num)
  have hre : ∀ z : ℂ, (g z).re ≤ Real.log C + C * phi32 ‖z‖ := by
    intro z
    have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have h1 : ‖f z‖ ≤ C * Real.exp (C * ‖z‖ ^ (1 + 1 / 2 : ℝ)) := hCz z
    have hexp : ‖z‖ ^ (1 + 1 / 2 : ℝ) ≤ phi32 ‖z‖ := by
      have he : ((1 : ℝ) + 1 / 2) = 3 / 2 := by norm_num
      rw [he]
      exact rpow_three_halves_le_phi32 hz
    have h2 : Real.exp ((g z).re) ≤ C * Real.exp (C * ‖z‖ ^ (1 + 1 / 2 : ℝ)) := by
      rw [hfg z, Complex.norm_exp] at h1
      exact h1
    have h3 : C * Real.exp (C * ‖z‖ ^ (1 + 1 / 2 : ℝ))
        ≤ Real.exp (Real.log C + C * phi32 ‖z‖) := by
      rw [Real.exp_add, Real.exp_log hC]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hexp hC.le)) hC.le
    exact Real.exp_le_exp.mp (h2.trans h3)
  have hK : (0 : ℝ) ≤ 2 * |Real.log C| + 12 * C + 2 + 3 * ‖g 0‖ := by positivity
  have hgrow := norm_le_phi32_of_re_le_phi32 hg hC.le hre
  have hd1 := norm_deriv_le_sqrt_of_phi32_growth hg hK hgrow
  have hd2 := deriv_deriv_eq_zero_of_sqrt_growth hg (by linarith : (0:ℝ) ≤ 6 * (2 * |Real.log C|
    + 12 * C + 2 + 3 * ‖g 0‖)) hd1
  obtain ⟨c, hc⟩ := eq_affine_of_deriv_deriv_eq_zero hg hd2
  exact ⟨c, g 0, fun z => by rw [hfg z, hc z]⟩

/-! ## Dividing out a zero, preserving `HasOrderLeOne` -/

/-- **The division step at arbitrary type.** If `f` is entire of order `≤ 1` and `f z₀ = 0`
then `f z = (z - z₀) * g z` with `g = dslope f z₀` entire and again of order `≤ 1`.

`ε` is threaded through unchanged: for each `ε` the constant `C` supplied by
`HasOrderLeOne f` is enlarged to `max C (max C₀ 1)`, where `C₀` bounds `dslope f z₀` on the
compact disc `closedBall z₀ 1`. Outside that disc `‖dslope f z₀ z‖ ≤ ‖f z‖`.-/
theorem exists_entire_div_of_zero_gen {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hord : HasOrderLeOne f) {z₀ : ℂ} (hz₀ : f z₀ = 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ HasOrderLeOne g ∧ (∀ z, f z = (z - z₀) * g z) := by
  have hgd : Differentiable ℂ (dslope f z₀) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (by simp)).mpr (differentiableOn_univ.mpr hf)
  have hfac : ∀ z, f z = (z - z₀) * dslope f z₀ z := by
    intro z
    have h := sub_smul_dslope f z₀ z
    rw [hz₀, sub_zero, smul_eq_mul] at h
    exact h.symm
  refine ⟨dslope f z₀, hgd, ?_, hfac⟩
  intro ε hε
  obtain ⟨C, hC, hCz⟩ := hord ε hε
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall z₀ 1).exists_bound_of_continuousOn
    hgd.continuous.continuousOn
  refine ⟨max C (max C₀ 1), lt_max_of_lt_left hC, fun z => ?_⟩
  have hrp : (0 : ℝ) ≤ ‖z‖ ^ (1 + ε) := Real.rpow_nonneg (norm_nonneg z) _
  have hCle : C ≤ max C (max C₀ 1) := le_max_left _ _
  have hC₀le : C₀ ≤ max C (max C₀ 1) := (le_max_left C₀ 1).trans (le_max_right _ _)
  have hpos : (0 : ℝ) < max C (max C₀ 1) := lt_max_of_lt_left hC
  have hexp : (1 : ℝ) ≤ Real.exp (max C (max C₀ 1) * ‖z‖ ^ (1 + ε)) :=
    Real.one_le_exp (mul_nonneg hpos.le hrp)
  rcases le_or_gt 1 ‖z - z₀‖ with h | h
  · have hnorm : ‖z - z₀‖ * ‖dslope f z₀ z‖ = ‖f z‖ := by rw [hfac z, norm_mul]
    have hle : ‖dslope f z₀ z‖ ≤ ‖f z‖ := by nlinarith [norm_nonneg (dslope f z₀ z)]
    calc ‖dslope f z₀ z‖ ≤ ‖f z‖ := hle
      _ ≤ C * Real.exp (C * ‖z‖ ^ (1 + ε)) := hCz z
      _ ≤ max C (max C₀ 1) * Real.exp (max C (max C₀ 1) * ‖z‖ ^ (1 + ε)) := by gcongr
  · have hmem : z ∈ Metric.closedBall z₀ 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact h.le
    calc ‖dslope f z₀ z‖ ≤ C₀ := hC₀ z hmem
      _ ≤ max C (max C₀ 1) := hC₀le
      _ = max C (max C₀ 1) * 1 := (mul_one _).symm
      _ ≤ max C (max C₀ 1) * Real.exp (max C (max C₀ 1) * ‖z‖ ^ (1 + ε)) := by gcongr

/-! ## Stripping a zero to its full multiplicity -/

/-- Iterating the division step: if the vanishing order of `f` at `z₀` is at most `m` then
`f z = (z - z₀) ^ j * g z` globally, with `g` entire of order `≤ 1` and `g z₀ ≠ 0`.-/
theorem exists_pow_mul_of_hasOrderLeOne (z₀ : ℂ) :
    ∀ (m : ℕ) (f : ℂ → ℂ), Differentiable ℂ f → HasOrderLeOne f →
      analyticOrderAt f z₀ ≤ (m : ℕ∞) →
      ∃ (j : ℕ) (g : ℂ → ℂ), Differentiable ℂ g ∧ HasOrderLeOne g ∧ g z₀ ≠ 0 ∧
        (∀ z, f z = (z - z₀) ^ j * g z) := by
  intro m
  induction m with
  | zero =>
    intro f hf hord hordle
    have h0 : analyticOrderAt f z₀ = 0 := le_antisymm (by simpa using hordle) (by simp)
    exact ⟨0, f, hf, hord, (hf.analyticAt z₀).analyticOrderAt_eq_zero.mp h0, by simp⟩
  | succ m ih =>
    intro f hf hord hordle
    by_cases hz₀ : f z₀ = 0
    · obtain ⟨h, hhd, hhord, hfac⟩ := exists_entire_div_of_zero_gen hf hord hz₀
      have hprod : f = (fun z : ℂ => z - z₀) * h := funext fun z => by simpa using hfac z
      have hmono : analyticOrderAt (fun z : ℂ => z - z₀) z₀ = 1 := by
        simpa using analyticOrderAt_centeredMonomial (𝕜 := ℂ) (z₀ := z₀) (n := 1)
      have hsum : analyticOrderAt f z₀ = 1 + analyticOrderAt h z₀ := by
        rw [hprod, analyticOrderAt_mul (by fun_prop) (hhd.analyticAt z₀), hmono]
      have hordh : analyticOrderAt h z₀ ≤ (m : ℕ∞) := by
        refine (ENat.add_le_add_iff_left (k := 1) (by simp)).mp ?_
        rw [← hsum]
        refine hordle.trans (le_of_eq ?_)
        push_cast
        ring
      obtain ⟨j, g, hg, hgord, hgz, hgfac⟩ := ih h hhd hhord hordh
      refine ⟨j + 1, g, hg, hgord, hgz, fun z => ?_⟩
      rw [hfac z, hgfac z]
      ring
    · exact ⟨0, f, hf, hord, hz₀, by simp⟩

/-! ## Hadamard factorization at order `≤ 1`, finitely many zeros -/

/-- Induction on the number of distinct zeros.-/
theorem exists_poly_mul_exp_aux_gen :
    ∀ (k : ℕ) (f : ℂ → ℂ), Differentiable ℂ f → HasOrderLeOne f →
      {z : ℂ | f z = 0}.Finite → {z : ℂ | f z = 0}.ncard = k →
      ∃ (P : Polynomial ℂ) (a b : ℂ), ∀ z, f z = P.eval z * Complex.exp (a * z + b) := by
  intro k
  induction k with
  | zero =>
    intro f hf hord hfin hcard
    have hempty : {z : ℂ | f z = 0} = ∅ := (Set.ncard_eq_zero hfin).mp hcard
    have hnz : ∀ z, f z ≠ 0 := by
      intro z hz
      have hmem : z ∈ ({z : ℂ | f z = 0}) := hz
      rw [hempty] at hmem
      exact hmem
    obtain ⟨a, b, hab⟩ := eq_exp_affine_of_hasOrderLeOne hf hnz hord
    exact ⟨1, a, b, fun z => by rw [hab z]; simp⟩
  | succ k ih =>
    intro f hf hord hfin hcard
    have hne : {z : ℂ | f z = 0}.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro hc
      rw [hc] at hcard
      simp at hcard
    obtain ⟨z₀, hz₀⟩ := hne
    have hfne : ¬ (f = 0) := by
      rintro rfl
      have huniv : {z : ℂ | (0 : ℂ → ℂ) z = 0} = Set.univ := by ext; simp
      rw [huniv] at hfin
      exact Set.infinite_univ hfin
    have hordne : analyticOrderAt f z₀ ≠ ⊤ := by
      rw [ne_eq, AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z₀ fun w => hf.analyticAt w]
      exact hfne
    have hle : analyticOrderAt f z₀ ≤ (((analyticOrderAt f z₀).toNat : ℕ) : ℕ∞) :=
      le_of_eq (ENat.natCast_toNat hordne).symm
    obtain ⟨j, g, hg, hgord, hgz, hgfac⟩ :=
      exists_pow_mul_of_hasOrderLeOne z₀ _ f hf hord hle
    have hzero : {z : ℂ | g z = 0} = {z : ℂ | f z = 0} \ {z₀} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · intro hw
        refine ⟨by rw [hgfac w, hw, mul_zero], ?_⟩
        rintro rfl
        exact hgz hw
      · rintro ⟨hw, hnew⟩
        have hz := hgfac w
        rw [hw] at hz
        have hpow : (w - z₀) ^ j ≠ 0 := pow_ne_zero _ (sub_ne_zero_of_ne hnew)
        exact (mul_eq_zero.mp hz.symm).resolve_left hpow
    have hfin' : {z : ℂ | g z = 0}.Finite := by
      rw [hzero]; exact hfin.sdiff
    have hcard' : {z : ℂ | g z = 0}.ncard = k := by
      have h1 : ({z : ℂ | f z = 0} \ {z₀}).ncard + 1 = {z : ℂ | f z = 0}.ncard :=
        Set.ncard_sdiff_singleton_add_one hz₀ hfin
      rw [hcard] at h1
      rw [hzero]
      omega
    obtain ⟨Q, a, b, hQ⟩ := ih g hg hgord hfin' hcard'
    refine ⟨(Polynomial.X - Polynomial.C z₀) ^ j * Q, a, b, fun z => ?_⟩
    rw [hgfac z, hQ z]
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    ring

/-- **Hadamard factorization at order `≤ 1`, finitely many zeros, arbitrary type.**-/
theorem exists_poly_mul_exp_of_finite_zeros_of_hasOrderLeOne {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hord : HasOrderLeOne f) (hfin : {z : ℂ | f z = 0}.Finite) :
    ∃ (P : Polynomial ℂ) (a b : ℂ), ∀ z, f z = P.eval z * Complex.exp (a * z + b) :=
  exists_poly_mul_exp_aux_gen _ f hf hord hfin rfl

/-- Contrapositive form: an entire function of order at most one that is *not* `exp` of an
affine function must have a zero. This is the shape the application consumes.-/
theorem exists_zero_of_not_eq_exp_affine_of_hasOrderLeOne {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hord : HasOrderLeOne f)
    (hne : ¬ ∃ a b : ℂ, ∀ z, f z = Complex.exp (a * z + b)) :
    ∃ z, f z = 0 := by
  by_contra hc
  exact hne (eq_exp_affine_of_hasOrderLeOne hf (fun z hz => hc ⟨z, hz⟩) hord)

/-! ## Bridge: finite exponential type implies `HasOrderLeOne` -/

/-- **Finite exponential type is order `≤ 1`.** The hypothesis of `XiLab/OrderOne.lean`
implies the hypothesis used here, so every theorem in this file specialises to the
finite-type situation.

The analytic content is a Young-type inequality `B r ≤ B T + r ^ (1 + ε)` valid for all
`r ≥ 0`, with the threshold `T = (max B 1) ^ (1/ε)` chosen so that `T ^ ε = max B 1`: below
`T` the left side is at most `B T`, and above `T` one has
`r ^ (1 + ε) = r * r ^ ε ≥ r * T ^ ε ≥ B r`.-/
theorem hasOrderLeOne_of_exp_type {f : ℂ → ℂ} {A B : ℝ} (hA : 0 < A)
    (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖)) : HasOrderLeOne f := by
  intro ε hε
  set B' : ℝ := max B 1 with hB'_def
  have hB'1 : (1 : ℝ) ≤ B' := le_max_right _ _
  have hB'0 : (0 : ℝ) < B' := by linarith
  have hBB' : B ≤ B' := le_max_left _ _
  set T : ℝ := B' ^ ((1 : ℝ) / ε) with hT_def
  have hT1 : (1 : ℝ) ≤ T := by rw [hT_def]; exact Real.one_le_rpow hB'1 (by positivity)
  have hT0 : (0 : ℝ) < T := by linarith
  have hTe : T ^ ε = B' := by
    rw [hT_def, ← Real.rpow_mul hB'0.le, one_div_mul_cancel (ne_of_gt hε), Real.rpow_one]
  have hyoung : ∀ r : ℝ, 0 ≤ r → B' * r ≤ B' * T + r ^ (1 + ε) := by
    intro r hr
    have hrp : (0 : ℝ) ≤ r ^ (1 + ε) := Real.rpow_nonneg hr _
    rcases le_or_gt r T with h | h
    · have := mul_le_mul_of_nonneg_left h hB'0.le
      linarith
    · have hr0 : (0 : ℝ) < r := lt_trans hT0 h
      have hsplit : r ^ (1 + ε) = r * r ^ ε := by rw [Real.rpow_add hr0, Real.rpow_one]
      have hmono : T ^ ε ≤ r ^ ε := Real.rpow_le_rpow hT0.le h.le hε.le
      rw [hTe] at hmono
      rw [hsplit]
      have h2 := mul_le_mul_of_nonneg_left hmono hr0.le
      have h3 : (0 : ℝ) ≤ B' * T := mul_nonneg hB'0.le hT0.le
      linarith
  set D : ℝ := max (A * Real.exp (B' * T)) 1 with hD_def
  have hD1 : (1 : ℝ) ≤ D := by rw [hD_def]; exact le_max_right _ _
  have hD0 : (0 : ℝ) < D := by linarith
  refine ⟨D, hD0, fun z => ?_⟩
  have hz : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hrp : (0 : ℝ) ≤ ‖z‖ ^ (1 + ε) := Real.rpow_nonneg hz _
  have hle1 : A * Real.exp (B' * T) ≤ D := by rw [hD_def]; exact le_max_left _ _
  have hle2 : ‖z‖ ^ (1 + ε) ≤ D * ‖z‖ ^ (1 + ε) := by nlinarith
  calc ‖f z‖ ≤ A * Real.exp (B * ‖z‖) := hgrowth z
    _ ≤ A * Real.exp (B' * T + ‖z‖ ^ (1 + ε)) := by
        have h1 : B * ‖z‖ ≤ B' * T + ‖z‖ ^ (1 + ε) := by
          have hy := hyoung ‖z‖ hz
          have := mul_le_mul_of_nonneg_right hBB' hz
          linarith
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) hA.le
    _ = A * Real.exp (B' * T) * Real.exp (‖z‖ ^ (1 + ε)) := by rw [Real.exp_add]; ring
    _ ≤ D * Real.exp (‖z‖ ^ (1 + ε)) :=
        mul_le_mul_of_nonneg_right hle1 (Real.exp_pos _).le
    _ ≤ D * Real.exp (D * ‖z‖ ^ (1 + ε)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle2) hD0.le

/-! ## The finite-type statements, recovered through the bridge -/

/-- `XiLab.eq_exp_affine_of_order_le_one` recovered from the maximal-type theorem.-/
theorem eq_exp_affine_of_exp_type {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnz : ∀ z, f z ≠ 0) {A B : ℝ} (hA : 0 < A)
    (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖)) :
    ∃ a b : ℂ, ∀ z, f z = Complex.exp (a * z + b) :=
  eq_exp_affine_of_hasOrderLeOne hf hnz (hasOrderLeOne_of_exp_type hA hgrowth)

/-- `XiLab.exists_poly_mul_exp_of_finite_zeros` recovered from the maximal-type theorem.-/
theorem exists_poly_mul_exp_of_finite_zeros_of_exp_type {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {A B : ℝ} (hA : 0 < A) (hgrowth : ∀ z : ℂ, ‖f z‖ ≤ A * Real.exp (B * ‖z‖))
    (hfin : {z : ℂ | f z = 0}.Finite) :
    ∃ (P : Polynomial ℂ) (a b : ℂ), ∀ z, f z = P.eval z * Complex.exp (a * z + b) :=
  exists_poly_mul_exp_of_finite_zeros_of_hasOrderLeOne hf
    (hasOrderLeOne_of_exp_type hA hgrowth) hfin

/-! ## Non-vacuity checks -/

/-! ## Acceptance test -/

end XiLab
