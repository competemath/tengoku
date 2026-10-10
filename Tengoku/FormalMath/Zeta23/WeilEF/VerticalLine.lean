/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/VerticalLine.lean.  Vertical-line integrals for the EF contour.

KEY DEVICE (no contour shifting needed on the prime side): for s = c + it on a vertical line,
H(s) := h((s−1/2)/i) = paperFT k (t − i·b) with b := c − 1/2, and
  paperFT k (t − i·b) = paperFT k_b t,  where k_b(u) := k(u)·e^{b·u}  (the TILTED test function,
still C_c²).  Hence the line integral (1/2π)∫ H(c+it)·n^{−c−it} dt is, by Fourier inversion of
k_b (Zeta23.EF.paper_inversion, proved in Zeta23/ExplicitFormula.lean, with integrability from
Zeta23/ExplicitFormula/Bridge.lean's integrable_fourier_of_contDiff_two),
  n^{−c}·k_b(log n) = n^{−c}·k(log n)·n^{b} = n^{−1/2}·k(log n).
Summing against −ζ'/ζ(c+it) = Σ Λ(n)n^{−c−it} (Mathlib LSeries, 1 < c) with a dominated
tsum/integral swap (domination: ‖paperFT k_b t‖(1+t²) ≤ ‖k_b‖₁+‖k_b''‖₁ from
Zeta23.EF.norm_paperFT_mul_one_add_sq_le × Σ Λ(n)n^{−c} < ∞) gives the prime side.
-/
import Tengoku.FormalMath.Zeta23.WeilEF.XiLogDeriv
import Tengoku.FormalMath.Zeta23.GammaFacts.StirlingVert
import Tengoku
import Tengoku.FormalMath.Zeta23.ExplicitFormula
import Tengoku.FormalMath.Zeta23.ExplicitFormula.Bridge
import Tengoku.FormalMath.Zeta23.WeilEF.GammaRBracket
import Tengoku.FormalMath.Zeta23.Poisson.PaperFT

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex MeasureTheory
open scoped ArithmeticFunction

/-- The test function on vertical lines: H(s) := h((s − 1/2)/i). -/
def Hfn (k : ℝ → ℂ) (s : ℂ) : ℂ := paperFT k ((s - 1/2) / I)

/-- The tilted test function k_b(u) := k(u)·e^{b u}. -/
def tilt (k : ℝ → ℂ) (b : ℝ) : ℝ → ℂ := fun u => k u * (Real.exp (b * u) : ℂ)

theorem tilt_contDiff {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (b : ℝ) : ContDiff ℝ 2 (tilt k b) := by
  refine hk.mul ?_
  have : ContDiff ℝ 2 (fun u : ℝ => Real.exp (b * u)) := (Real.contDiff_exp.comp
    (contDiff_const.mul contDiff_id)).of_le le_top
  exact Complex.ofRealCLM.contDiff.comp this

theorem tilt_hasCompactSupport {k : ℝ → ℂ} (hk : HasCompactSupport k) (b : ℝ) :
    HasCompactSupport (tilt k b) := by
  refine hk.mul_right

/-- On the line Re s = c: H(c+it) = paperFT (tilt k (c − 1/2)) t. -/
theorem Hfn_line (k : ℝ → ℂ) (c t : ℝ) :
    Hfn k (c + t * I) = paperFT (tilt k (c - 1/2)) t := by
  unfold Hfn tilt paperFT
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  have harg : I * ((↑c + ↑t * I - 1/2) / I) * ↑u = (((c - 1/2) * u : ℝ) : ℂ) + I * ↑t * ↑u := by
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    field_simp
    push_cast
    ring
  rw [harg, Complex.exp_add, ← Complex.ofReal_exp]
  ring

/-- Tilted inversion: (1/2π)∫ paperFT (tilt k b) t · e^{−i t y} dt = k(y)·e^{b y}. -/
theorem tilted_inversion {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (b y : ℝ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, paperFT (tilt k b) t * cexp (-I * t * y)
      = k y * (Real.exp (b * y) : ℂ) := by
  have hcont := (tilt_contDiff hk b).continuous
  have hint : Integrable (tilt k b) (volume : Measure ℝ) :=
    hcont.integrable_of_hasCompactSupport (tilt_hasCompactSupport hkc b)
  have hF := Zeta23.EF.integrable_fourier_of_contDiff_two (tilt_contDiff hk b)
    (tilt_hasCompactSupport hkc b)
  have h1 := Zeta23.EF.paper_inversion hcont hint hF y
  rw [← h1]
  rfl

/-- Step 1 (pointwise on the line): the integrand is the tsum of tilted-transform × L-series
terms.  −ζ'/ζ = LSeries ↗Λ on Re s > 1 (Mathlib), then distribute paperFT (tilt k b) t. -/
theorem integrand_eq_tsum {k : ℝ → ℂ} {c : ℝ} (hc1 : 1 < c) (t : ℝ) :
    Hfn k (c + t * I) * (-logDeriv riemannZeta (c + t * I))
      = ∑' n : ℕ, paperFT (tilt k (c - 1/2)) t * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
  have hre : 1 < ((c : ℂ) + t * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simpa using hc1
  have h1 : -logDeriv riemannZeta ((c : ℂ) + t * I) = LSeries (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) := by
    have h2 := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
    rw [logDeriv, Pi.div_apply, h2]
    ring
  rw [Hfn_line, h1, LSeries, ← tsum_mul_left]

/-- Step 2 (per-n line integral): (1/2π)∫ paperFT(tilt k b) t · term_n(c+it) dt
  = Λ(n) n^{−1/2} k(log n). -/
theorem per_n_line_integral {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        paperFT (tilt k (c - 1/2)) t * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n
      = ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hterm : ∀ t : ℝ, LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n
        = ((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ) * cexp (-I * t * Real.log n) := by
      intro t
      rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, ← Complex.cpow_neg]
      have hsplit : (-((c:ℂ) + t * I)) = (-(c:ℂ)) + (-(I * t)) := by ring
      rw [hsplit, Complex.cpow_add _ _ hnC]
      have h1 : (n:ℂ) ^ (-(c:ℂ)) = (((n:ℝ) ^ (-c) : ℝ) : ℂ) := by
        rw [show ((n:ℂ)) = (((n:ℝ):ℂ)) by push_cast; rfl,
          show (-(c:ℂ)) = ((-c : ℝ) : ℂ) by push_cast; rfl,
          ← Complex.ofReal_cpow hn0.le]
      have h2 : (n:ℂ) ^ (-(I * t)) = cexp (-I * t * Real.log n) := by
        rw [Complex.cpow_def_of_ne_zero hnC]
        congr 1
        rw [show ((n:ℂ)) = (((n:ℝ):ℂ)) by push_cast; rfl, ← Complex.ofReal_log hn0.le]
        ring
      rw [h1, h2]
      ring
    simp_rw [hterm]
    have hre : (fun t : ℝ => paperFT (tilt k (c - 1/2)) t
        * (((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ) * cexp (-I * t * Real.log n)))
        = fun t : ℝ => (((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
          * (paperFT (tilt k (c - 1/2)) t * cexp (-I * t * Real.log n)) := by
      funext t
      ring
    rw [hre, Zeta23.EF.cintegral_const_mul]
    rw [show (1 / (2 * (Real.pi : ℂ))) * ((((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
        * ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t * cexp (-I * t * Real.log n))
        = (((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
          * ((1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t
            * cexp (-I * t * Real.log n)) from by ring]
    rw [tilted_inversion hk hkc (c - 1/2) (Real.log n)]
    have hexp : Real.exp ((c - 1/2) * Real.log n) = (n:ℝ) ^ (c - 1/2) := by
      rw [Real.rpow_def_of_pos hn0]
      ring_nf
    have hpow : ((n:ℝ) ^ (-c) : ℝ) * ((n:ℝ) ^ (c - 1/2) : ℝ) = ((n:ℝ) ^ (-(1/2) : ℝ) : ℝ) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    have hsqrt : ((n:ℝ) ^ (-(1/2) : ℝ) : ℝ) = 1 / Real.sqrt n := by
      rw [Real.rpow_neg hn0.le, Real.sqrt_eq_rpow]
      exact (one_div _).symm
    calc ((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ)
        * (k (Real.log n) * ((Real.exp ((c - 1/2) * Real.log n) : ℝ) : ℂ))
        = ((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ)
          * (k (Real.log n) * (((n:ℝ) ^ (c - 1/2) : ℝ) : ℂ)) := by rw [hexp]
      _ = ((((Λ n : ℝ) * ((n:ℝ) ^ (-c) * (n:ℝ) ^ (c - 1/2)) : ℝ)) : ℂ) * k (Real.log n) := by
          push_cast
          ring
      _ = ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
          rw [hpow, hsqrt, mul_one_div]

/-- Step 3 (tsum/integral swap): dominated by ‖paperFT (tilt k b)‖ ∈ L¹ × Σ Λ(n)n^{−c} < ∞. -/
theorem line_integral_swap {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) :
    ∫ t : ℝ, (∑' n : ℕ, paperFT (tilt k (c - 1/2)) t
        * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n)
      = ∑' n : ℕ, ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t
        * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
  have hkb2 : ContDiff ℝ 2 (tilt k (c - 1/2)) := tilt_contDiff hk _
  have hkbc : HasCompactSupport (tilt k (c - 1/2)) := tilt_hasCompactSupport hkc _
  have hFkb := Zeta23.EF.integrable_fourier_of_contDiff_two hkb2 hkbc
  have hpfi : Integrable (fun t : ℝ => paperFT (tilt k (c - 1/2)) t) :=
    Zeta23.EF.integrable_paperFT_ofReal hFkb
  have hre : ∀ t : ℝ, ((c:ℂ) + t * I).re = c := by
    intro t
    simp
  have hnorm : ∀ (n : ℕ) (t : ℝ), ‖LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n‖
      = if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c)) := by
    intro n t
    rw [LSeries.norm_term_eq, hre, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Real.rpow_neg (Nat.cast_nonneg n),
      div_eq_mul_inv]
  have hcont : ∀ n : ℕ, Continuous (fun t : ℝ =>
      LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simpa [LSeries.term_zero] using continuous_const
    · simp only [LSeries.term_of_ne_zero hn]
      refine continuous_const.div ?_ (fun t => ?_)
      · refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
        exact_mod_cast hn
      · exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
  have hint : ∀ n : ℕ, Integrable (fun t : ℝ => paperFT (tilt k (c - 1/2)) t
      * LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n) := by
    intro n
    refine hpfi.mul_bdd (c := if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c)))
      (hcont n).aestronglyMeasurable ?_
    filter_upwards with t
    rw [hnorm n t]
  have heval : ∀ n : ℕ, (∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t
      * LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n‖)
      = (∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t‖)
        * (if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c))) := by
    intro n
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [norm_mul, hnorm n t]
  have hcn : Summable (fun n : ℕ => if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c))) := by
    have hs : LSeriesSummable (fun n => (Λ n : ℂ)) (c : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc1)
    have hns : Summable (fun n : ℕ => ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖) :=
      summable_norm_iff.mpr hs
    refine hns.congr fun n => ?_
    simpa using hnorm n 0
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t
      * LSeries.term (fun n => (Λ n : ℂ)) ((c:ℂ) + t * I) n‖) := by
    refine ((hcn.mul_left (∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t‖)).congr fun n => ?_)
    rw [heval n]
  exact (MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsum).tsum_eq.symm

/-- **Prime side on Re s = c ∈ (1, 3/2]**:
(1/2π)∫_ℝ H(c+it)·(−ζ'/ζ)(c+it) dt = Σ_{n≥1} Λ(n) n^{−1/2} k(log n). -/
theorem prime_side_line {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k (c + t * I) * (-logDeriv riemannZeta (c + t * I))
      = ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
  have h1 : ∀ t : ℝ, Hfn k (c + t * I) * (-logDeriv riemannZeta (c + t * I))
      = ∑' n : ℕ, paperFT (tilt k (c - 1/2)) t
        * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := fun t => integrand_eq_tsum hc1 t
  calc (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k (c + t * I) * (-logDeriv riemannZeta (c + t * I))
      = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, ∑' n : ℕ, paperFT (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
        rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
    _ = (1 / (2 * Real.pi) : ℂ) * ∑' n : ℕ, ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
        rw [line_integral_swap hk hkc hc1]
    _ = ∑' n : ℕ, (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (Λ n : ℂ)) (c + t * I) n := by
        rw [← tsum_mul_left]
    _ = ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) :=
        tsum_congr fun n => per_n_line_integral hk hkc n

/-- Coarse digamma growth on the right half-plane strip (consumed by the Γℝ line shift and the
horizontal-segment estimates; any polynomial bound works — dischargeable via a Stirling-type
estimate or directly). -/
theorem digamma_growth_strip : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1/4 ≤ s.re → s.re ≤ 1 →
    ‖Complex.digamma s‖ ≤ C * Real.log (2 + |s.im|) := by
  -- differentiability of ψ on the right half-plane
  have hdiff : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ Complex.digamma s := by
    intro s hs
    have hzero : ∀ m : ℕ, s ≠ -(m : ℂ) := by
      intro m h
      rw [h] at hs
      simp only [Complex.neg_re, Complex.natCast_re] at hs
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hΓan : AnalyticAt ℂ Complex.Gamma s := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      filter_upwards [hopen.mem_nhds hs] with w hw
      refine Complex.differentiableAt_Gamma w fun m => ?_
      intro h
      rw [h] at hw
      simp only [Complex.neg_re, Complex.natCast_re] at hw
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hΓne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hzero
    have hψan : AnalyticAt ℂ Complex.digamma s := by
      have h1 : AnalyticAt ℂ (deriv Complex.Gamma) s := hΓan.deriv
      have h2 := h1.div hΓan hΓne
      exact h2.congr (by
        filter_upwards with w
        rw [Complex.digamma_def, logDeriv_apply]
        rfl)
    exact hψan.differentiableAt
  -- bound on the compact rectangle |Im| ≤ 1/2
  have hK : IsCompact (Complex.reProdIm (Set.Icc (1/4 : ℝ) 1) (Set.Icc (-(1/2) : ℝ) (1/2))) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcontK : ContinuousOn Complex.digamma
      (Complex.reProdIm (Set.Icc (1/4 : ℝ) 1) (Set.Icc (-(1/2) : ℝ) (1/2))) := by
    intro s hs
    have hsre : 1/4 ≤ s.re := (Complex.mem_reProdIm.mp hs).1.1
    exact ((hdiff s (by linarith)).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcontK
  have hM0 : (0 : ℝ) ≤ M := by
    have h := hM (1/2 : ℂ) (by
      rw [Complex.mem_reProdIm]
      constructor
      · simp only [Complex.div_ofNat_re, Complex.one_re]
        norm_num
      · simp only [Complex.div_ofNat_im, Complex.one_im]
        norm_num)
    exact le_trans (norm_nonneg _) h
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set K₀ : ℝ := 14 + Real.pi + Real.log 4 with hK₀
  have hK₀0 : (0 : ℝ) < K₀ := by positivity
  refine ⟨max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1, by positivity, fun s hre1 hre2 => ?_⟩
  have hlogmono : Real.log 2 ≤ Real.log (2 + |s.im|) := by
    apply Real.log_le_log (by norm_num)
    have := abs_nonneg s.im
    linarith
  have hlogpos : (0 : ℝ) < Real.log (2 + |s.im|) := lt_of_lt_of_le hlog2 hlogmono
  rcases le_or_gt (|s.im|) (1/2) with him | him
  · -- compact part
    have hsK : s ∈ Complex.reProdIm (Set.Icc (1/4 : ℝ) 1) (Set.Icc (-(1/2) : ℝ) (1/2)) := by
      rw [Complex.mem_reProdIm]
      refine ⟨⟨hre1, hre2⟩, ?_⟩
      rw [Set.mem_Icc]
      constructor <;> [linarith [neg_abs_le s.im]; linarith [le_abs_self s.im]]
    calc ‖Complex.digamma s‖ ≤ M := hM s hsK
      _ = (M / Real.log 2) * Real.log 2 := by
          field_simp
      _ ≤ (max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1) * Real.log (2 + |s.im|) := by
          apply mul_le_mul ?_ hlogmono hlog2.le (by positivity)
          calc M / Real.log 2 ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) := le_max_left _ _
            _ ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1 := by linarith
  · -- Stirling part: ‖ψ‖ ≤ ‖ψ − log s + (1/2)/s‖ + ‖log s‖ + ‖(1/2)/s‖
    have hsre0 : (0 : ℝ) < s.re := by linarith
    have hst := Zeta23.StirlingVert.digamma_stirling (w := s) hsre0 (by linarith)
    have hsnorm_lo : (1/4 : ℝ) ≤ ‖s‖ :=
      le_trans hre1 (le_trans (le_abs_self _) (Complex.abs_re_le_norm s))
    have hsnorm0 : (0 : ℝ) < ‖s‖ := by linarith
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, norm_zero] at hsnorm0
      exact lt_irrefl 0 hsnorm0
    have hsnorm_hi : ‖s‖ ≤ 1 + |s.im| := by
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 1 + |s.im| := by
            have : |s.re| ≤ 1 := by
              rw [abs_le]
              constructor <;> linarith
            linarith
    -- ‖log s‖ ≤ |log ‖s‖| + π ≤ (log 4 + log(2+|im|)) + π
    have hlog_s : ‖Complex.log s‖ ≤ |Real.log ‖s‖| + Real.pi := by
      calc ‖Complex.log s‖ ≤ |(Complex.log s).re| + |(Complex.log s).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ |Real.log ‖s‖| + Real.pi := by
            rw [Complex.log_re, Complex.log_im]
            have := Complex.abs_arg_le_pi s
            linarith [abs_nonneg (Complex.arg s)]
    have hlog_abs : |Real.log ‖s‖| ≤ Real.log 4 + Real.log (2 + |s.im|) := by
      rcases le_or_gt (Real.log ‖s‖) 0 with hneg | hpos
      · -- ‖s‖ ≤ 1-ish: |log| = −log ≤ log 4 since ‖s‖ ≥ 1/4
        have h1 : Real.log (1/4 : ℝ) ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) hsnorm_lo
        have h2 : Real.log (1/4 : ℝ) = -Real.log 4 := by
          rw [show (1/4 : ℝ) = 4⁻¹ by norm_num, Real.log_inv]
        rw [abs_of_nonpos hneg]
        have h3 : (0 : ℝ) ≤ Real.log (2 + |s.im|) := by
          apply Real.log_nonneg
          have := abs_nonneg s.im
          linarith
        linarith
      · rw [abs_of_pos hpos]
        have h1 : Real.log ‖s‖ ≤ Real.log (2 + |s.im|) := by
          apply Real.log_le_log hsnorm0
          have := abs_nonneg s.im
          linarith
        have h2 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        linarith
    have hinv_s : ‖(1/2 : ℂ) / s‖ ≤ 2 := by
      rw [norm_div]
      have h1 : ‖(1/2 : ℂ)‖ = 1/2 := by
        rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by norm_num)]
      rw [h1, div_le_iff₀ hsnorm0]
      linarith
    have him2 : 3 / s.im ^ 2 ≤ 12 := by
      have h1 : (1/4 : ℝ) ≤ s.im ^ 2 := by
        have h2 : (1/2 : ℝ) ≤ |s.im| := him.le
        nlinarith [abs_nonneg s.im, sq_abs s.im]
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith
    have htot : ‖Complex.digamma s‖
        ≤ Real.log (2 + |s.im|) + K₀ := by
      have h1 : ‖Complex.digamma s‖
          ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
            + ‖(1/2 : ℂ) / s‖ := by
        have h2 : Complex.digamma s = (Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
            + Complex.log s - (1/2 : ℂ) / s := by ring
        calc ‖Complex.digamma s‖
            = ‖(Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
                + Complex.log s - (1/2 : ℂ) / s‖ := by rw [← h2]
          _ ≤ ‖(Complex.digamma s - Complex.log s + (1/2 : ℂ) / s) + Complex.log s‖
              + ‖(1/2 : ℂ) / s‖ := norm_sub_le _ _
          _ ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
              + ‖(1/2 : ℂ) / s‖ := by
              have := norm_add_le (Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
                (Complex.log s)
              linarith
      rw [hK₀]
      have hπ4 : Real.pi < 4 := Real.pi_lt_four
      calc ‖Complex.digamma s‖
          ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
            + ‖(1/2 : ℂ) / s‖ := h1
        _ ≤ 3 / s.im ^ 2 + (|Real.log ‖s‖| + Real.pi) + 2 := by
            have := hst
            linarith [hlog_s, hinv_s]
        _ ≤ 12 + ((Real.log 4 + Real.log (2 + |s.im|)) + Real.pi) + 2 := by
            linarith [him2, hlog_abs]
        _ ≤ Real.log (2 + |s.im|) + (14 + Real.pi + Real.log 4) := by linarith
    calc ‖Complex.digamma s‖ ≤ Real.log (2 + |s.im|) + K₀ := htot
      _ ≤ Real.log (2 + |s.im|) + (K₀ / Real.log 2) * Real.log (2 + |s.im|) := by
          have h3 : K₀ / Real.log 2 * Real.log 2 ≤ K₀ / Real.log 2 * Real.log (2 + |s.im|) :=
            mul_le_mul_of_nonneg_left hlogmono (by positivity)
          have h4 : K₀ / Real.log 2 * Real.log 2 = K₀ := by field_simp
          linarith
      _ = (1 + K₀ / Real.log 2) * Real.log (2 + |s.im|) := by ring
      _ ≤ (max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1) * Real.log (2 + |s.im|) := by
          apply mul_le_mul_of_nonneg_right ?_ hlogpos.le
          calc (1 + K₀ / Real.log 2) ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) :=
                le_max_right _ _
            _ ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1 := by linarith

/-- continuity ⇒ integrability on vertical lines under a majorant (used by vertical_line_shift). -/
lemma integrable_line {f : ℂ → ℂ} {σ : ℝ} (hf : ∀ t : ℝ, DifferentiableAt ℂ f (σ + t * I))
    {φ : ℝ → ℝ} (hφ : Integrable φ) (hb : ∀ t : ℝ, ‖f (σ + t * I)‖ ≤ φ t) :
    Integrable (fun t : ℝ => f (σ + t * I)) := by
  have hc : Continuous (fun t : ℝ => f (σ + t * I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hg : Continuous (fun t : ℝ => (σ : ℂ) + t * I) := by fun_prop
    show ContinuousAt (f ∘ fun t : ℝ => (σ : ℂ) + t * I) t
    exact ContinuousAt.comp_of_eq (hf t).continuousAt hg.continuousAt rfl
  exact hφ.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)

/-- General vertical-line shift for an analytic function with an integrable, uniformly-decaying
majorant on a closed strip (Cauchy on rectangles + horizontal vanishing + dominated limits).
Proof route: RectangleIntegral machinery (HolomorphicOn.vanishesOnRectangle). -/
theorem vertical_line_shift {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → DifferentiableAt ℂ f s)
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    (hbound : ∀ (σ t : ℝ), a ≤ σ → σ ≤ b → ‖f (σ + t * I)‖ ≤ φ t)
    (hφtop : Filter.Tendsto φ Filter.atTop (nhds 0))
    (hφbot : Filter.Tendsto φ Filter.atBot (nhds 0)) :
    ∫ t : ℝ, f (b + t * I) = ∫ t : ℝ, f (a + t * I) := by
  -- integrability on the vertical lines
  have hint : ∀ σ : ℝ, a ≤ σ → σ ≤ b → Integrable (fun t : ℝ => f (σ + t * I)) := fun σ h1 h2 =>
    integrable_line (fun t => hf _ (by simp [h1]) (by simp [h2])) hφ (fun t => hbound σ t h1 h2)
  have hφnn : ∀ t, 0 ≤ φ t := fun t => (norm_nonneg _).trans (hbound a t le_rfl hab)
  -- Cauchy on the rectangles [a,b] × [−R, R]
  have hrect : ∀ R : ℝ, (∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I))
      = -I * ((∫ x in a..b, f (x + R * I)) - (∫ x in a..b, f (x + (-R) * I))) := by
    intro R
    have hdiff : DifferentiableOn ℂ f (Set.uIcc a b ×ℂ Set.uIcc (-R) R) := by
      intro z hz
      rw [Set.uIcc_of_le hab] at hz
      exact (hf z hz.1.1 hz.1.2).differentiableWithinAt
    have H := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ((a : ℂ) + (-R : ℝ) * I) ((b : ℂ) + (R : ℝ) * I) (by simpa using hdiff)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add, smul_eq_mul] at H
    have key : I * ((∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I)))
        = (∫ x in a..b, f (x + R * I)) - (∫ x in a..b, f (x + (-R) * I)) := by
      push_cast at H ⊢
      linear_combination H
    calc (∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I))
        = -(I * I) * ((∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I))) := by
          rw [I_mul_I]; ring
      _ = -I * (I * ((∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I)))) := by
          ring
      _ = _ := by rw [key]
  -- the horizontal sides are small
  have hsmall : ∀ R : ℝ, ‖(∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I))‖
      ≤ (b - a) * (φ R + φ (-R)) := by
    intro R
    rw [hrect R, norm_mul, norm_neg, Complex.norm_I, one_mul]
    have h1 : ‖∫ x in a..b, f (x + R * I)‖ ≤ φ R * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => by
        rw [Set.uIoc_of_le hab] at hx
        exact hbound x R hx.1.le hx.2
    have h2 : ‖∫ x in a..b, f (x + (-R) * I)‖ ≤ φ (-R) * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => by
        rw [Set.uIoc_of_le hab] at hx
        have := hbound x (-R) hx.1.le hx.2
        simpa using this
    rw [abs_of_nonneg (by linarith)] at h1 h2
    calc ‖(∫ x in a..b, f (x + R * I)) - (∫ x in a..b, f (x + (-R) * I))‖
        ≤ ‖∫ x in a..b, f (x + R * I)‖ + ‖∫ x in a..b, f (x + (-R) * I)‖ := norm_sub_le _ _
      _ ≤ φ R * (b - a) + φ (-R) * (b - a) := add_le_add h1 h2
      _ = (b - a) * (φ R + φ (-R)) := by ring
  -- limits
  set g : ℝ → ℂ := fun R => (∫ y in (-R)..R, f (b + y * I)) - (∫ y in (-R)..R, f (a + y * I)) with hg
  have hlim1 : Filter.Tendsto g Filter.atTop (nhds ((∫ t : ℝ, f (b + t * I)) - (∫ t : ℝ, f (a + t * I)))) := by
    apply Filter.Tendsto.sub
    · exact intervalIntegral_tendsto_integral (hint b hab le_rfl) Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
    · exact intervalIntegral_tendsto_integral (hint a le_rfl hab) Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  have hlim0 : Filter.Tendsto g Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun R => norm_nonneg _) (fun R => hsmall R) ?_
    have : Filter.Tendsto (fun R => (b - a) * (φ R + φ (-R))) Filter.atTop (nhds ((b - a) * (0 + 0))) :=
      (hφtop.add (hφbot.comp Filter.tendsto_neg_atTop_atBot)).const_mul _
    simpa using this
  have := tendsto_nhds_unique hlim1 hlim0
  exact sub_eq_zero.mp this

/-- paperFT of a continuous compactly supported function is entire (differentiation under the
integral sign); needed for all contour arguments (H = Hfn k analytic in s). -/
theorem differentiable_paperFT {k : ℝ → ℂ} (hk : Continuous k) (hkc : HasCompactSupport k) :
    Differentiable ℂ (paperFT k) := by
  intro z₀
  obtain ⟨Λ₁, hΛ₁⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  have hΛ₀ : ∀ u : ℝ, k u ≠ 0 → |u| ≤ max Λ₁ 0 := fun u hu => (hΛ₁ u hu).trans (le_max_left _ _)
  have hΛ₀0 : (0:ℝ) ≤ max Λ₁ 0 := le_max_right _ _
  have hbound_int : Integrable (fun u : ℝ => ‖k u‖
      * (max Λ₁ 0 * Real.exp ((‖z₀‖ + 1) * max Λ₁ 0))) :=
    (hk.norm.integrable_of_hasCompactSupport hkc.norm).mul_const _
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (s := Metric.ball z₀ 1) (x₀ := z₀)
    (F := fun z (u : ℝ) => k u * cexp (I * z * u))
    (F' := fun z (u : ℝ) => k u * ((I : ℂ) * u) * cexp (I * z * u))
    (bound := fun u : ℝ => ‖k u‖ * (max Λ₁ 0 * Real.exp ((‖z₀‖ + 1) * max Λ₁ 0)))
    (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall fun z => (Continuous.aestronglyMeasurable (by fun_prop)))
    ((Continuous.integrable_of_hasCompactSupport (by fun_prop) hkc.mul_right))
    (Continuous.aestronglyMeasurable (by fun_prop))
    (Filter.Eventually.of_forall fun u => fun z hz => ?_)
    hbound_int
    (Filter.Eventually.of_forall fun u => fun z hz => ?_)
  · exact ⟨_, key.2.hasFDerivAt⟩
  · rcases eq_or_ne (k u) 0 with hku | hku
    · simp [hku]
    · have hu := hΛ₀ u hku
      have hz' : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have := norm_sub_norm_le z z₀
        rw [Metric.mem_ball, Complex.dist_eq] at hz
        linarith [le_of_lt hz]
      rw [norm_mul, norm_mul, Complex.norm_exp]
      have h1 : ‖(I : ℂ) * u‖ ≤ max Λ₁ 0 := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact hu
      have h2 : (I * z * u).re ≤ (‖z₀‖ + 1) * max Λ₁ 0 := by
        have hre : (I * z * u).re = -(z.im * u) := by
          simp [Complex.mul_re, Complex.mul_im]
        rw [hre]
        calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
          _ = |z.im| * |u| := abs_mul _ _
          _ ≤ (‖z₀‖ + 1) * max Λ₁ 0 := by
              refine mul_le_mul ?_ hu (abs_nonneg _) (by positivity)
              exact (Complex.abs_im_le_norm z).trans hz'
      calc ‖k u‖ * ‖(I : ℂ) * u‖ * Real.exp ((I * z * u).re)
          ≤ ‖k u‖ * (max Λ₁ 0) * Real.exp ((‖z₀‖ + 1) * max Λ₁ 0) := by
            refine mul_le_mul (mul_le_mul le_rfl h1 (norm_nonneg _) (norm_nonneg _))
              (Real.exp_le_exp.mpr h2) (Real.exp_nonneg _) (by positivity)
        _ = ‖k u‖ * (max Λ₁ 0 * Real.exp ((‖z₀‖ + 1) * max Λ₁ 0)) := by ring
  · have h1 : HasDerivAt (fun z : ℂ => I * z * (u:ℂ)) (I * u) z := by
      have := ((hasDerivAt_id z).const_mul (I : ℂ)).mul_const ((u:ℂ))
      simpa [mul_comm, mul_assoc, mul_left_comm] using this
    have h2 := h1.cexp
    have h3 := h2.const_mul (k u)
    exact h3.congr_deriv (by ring)

/-- log(2+x)/(1+x²) ≤ 6 (1+x)^{−3/2} for x ≥ 0. -/
lemma log_two_add_div_le {x : ℝ} (hx : 0 ≤ x) :
    Real.log (2 + x) / (1 + x ^ 2) ≤ 6 * (1 + x) ^ (-(3 / 2 : ℝ)) := by
  have h1 := Real.log_le_rpow_div (show (0:ℝ) ≤ 2 + x by linarith) (show (0:ℝ) < 1/2 by norm_num)
  have h2 : (2 + x) ^ (1 / 2 : ℝ) ≤ (3 / 2) * (1 + x) ^ (1 / 2 : ℝ) := by
    have : (2 + x) ^ (1 / 2 : ℝ) ≤ ((9/4) * (1 + x)) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    rw [Real.mul_rpow (by norm_num) (by linarith)] at this
    rw [show ((9:ℝ)/4) ^ (1/2:ℝ) = 3/2 by
      rw [show (9:ℝ)/4 = (3/2) ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num] at this
    exact this
  have hlog : Real.log (2 + x) ≤ 3 * (1 + x) ^ (1 / 2 : ℝ) := by
    have : (2 + x) ^ (1 / 2 : ℝ) / (1 / 2) = 2 * (2 + x) ^ (1 / 2 : ℝ) := by ring
    rw [this] at h1; linarith
  have hsq : 1 / (1 + x ^ 2) ≤ 2 * (1 + x) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg (by linarith), Real.rpow_two, div_le_iff₀ (by positivity)]
    rw [show 2 * ((1 + x) ^ 2)⁻¹ * (1 + x ^ 2) = 2 * (1 + x ^ 2) / (1 + x) ^ 2 by ring,
      le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (x - 1)]
  have h0 : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
  calc Real.log (2 + x) / (1 + x ^ 2) = Real.log (2 + x) * (1 / (1 + x ^ 2)) := by ring
    _ ≤ (3 * (1 + x) ^ (1 / 2 : ℝ)) * (2 * (1 + x) ^ (-2 : ℝ)) :=
        mul_le_mul hlog hsq (by positivity) (by positivity)
    _ = 6 * ((1 + x) ^ (1 / 2 : ℝ) * (1 + x) ^ (-2 : ℝ)) := by ring
    _ = 6 * (1 + x) ^ (-(3 / 2 : ℝ)) := by rw [← Real.rpow_add (by linarith)]; norm_num

/-- uniform decay of H = paperFT k near the real axis: for |Im z| ≤ 1,
‖paperFT k z‖ ≤ 2 e^{Lam} (‖k‖₁ + ‖k″‖₁)/(1 + (Re z)²). -/
lemma norm_paperFT_le_uniform {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hki : Integrable k) {Lam : ℝ}
    (hLam : 0 ≤ Lam) (hsupp : ∀ u, k u ≠ 0 → |u| ≤ Lam) {z : ℂ} (hz : |z.im| ≤ 1) :
    ‖paperFT k z‖ ≤ 2 * Real.exp Lam * ((∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖) / (1 + z.re ^ 2) := by
  set N₀ := ∫ u, ‖k u‖ with hN₀
  set N₂ := ∫ u, ‖deriv (deriv k) u‖ with hN₂
  have hN₀0 : 0 ≤ N₀ := integral_nonneg fun _ => norm_nonneg _
  have hN₂0 : 0 ≤ N₂ := integral_nonneg fun _ => norm_nonneg _
  have he : Real.exp (|z.im| * Lam) ≤ Real.exp Lam := Real.exp_le_exp.mpr (by nlinarith [abs_nonneg z.im])
  by_cases hre : z.re ^ 2 ≤ 1
  · have b0 := norm_paperFT_le hki hsupp z
    calc ‖paperFT k z‖ ≤ Real.exp (|z.im| * Lam) * N₀ := b0
      _ ≤ Real.exp Lam * N₀ := mul_le_mul_of_nonneg_right he hN₀0
      _ ≤ 2 * Real.exp Lam * (N₀ + N₂) / (1 + z.re ^ 2) := by
          rw [le_div_iff₀ (by positivity)]
          have := Real.exp_pos Lam
          nlinarith [mul_nonneg this.le hN₂0, mul_nonneg this.le hN₀0]
  · push Not at hre
    have hz0 : z ≠ 0 := fun h => by rw [h] at hre; simp at hre; linarith
    have b2 := norm_paperFT_le_div hk hsupp hz0
    have hzn : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith [sq_nonneg z.im]
    have hzpos : 0 < ‖z‖ ^ 2 := by linarith
    calc ‖paperFT k z‖ ≤ Real.exp (|z.im| * Lam) * N₂ / ‖z‖ ^ 2 := b2
      _ ≤ Real.exp Lam * N₂ / z.re ^ 2 := by
          gcongr
      _ ≤ 2 * Real.exp Lam * (N₀ + N₂) / (1 + z.re ^ 2) := by
          rw [div_le_div_iff₀ (by linarith) (by positivity)]
          have := Real.exp_pos Lam
          nlinarith [mul_nonneg this.le hN₂0, mul_nonneg this.le hN₀0]

end WeilEF
end Zeta23
