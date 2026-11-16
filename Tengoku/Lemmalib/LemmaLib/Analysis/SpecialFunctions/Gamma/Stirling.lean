/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Tengoku.Lemmalib.LemmaLib.Analysis.EulerMaclaurin
public import Tengoku.Seed.Analysis.Calculus.Deriv.Slope
public import Tengoku.Seed.Analysis.SpecialFunctions.Complex.LogDeriv
public import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Beta
public import Tengoku.Seed.Analysis.SpecialFunctions.Sqrt
public import Tengoku.Seed.Analysis.SpecialFunctions.Stirling

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stirling's formula for the complex Gamma function with an explicit remainder

For `z : ℂ` with `Im z ≠ 0`,

`Γ(z) = √(2π) exp ((z - 1/2) log z - z + 1/(12 z) + ρ)` with `‖ρ‖ ≤ 1 / (30 (Im z)²)`

(`exists_Gamma_eq`), and consequently

`Γ(z) = √(2π) exp ((z - 1/2) log z - z + E)` with `‖E‖ ≤ 1/(12 ‖z‖) + 1/(30 (Im z)²)`

(`exists_Gamma_eq_sqrt_two_pi_mul_exp`). Here `log` is the principal branch.

The proof applies the Euler–Maclaurin formula of `LemmaLib.Analysis.EulerMaclaurin` to
`x ↦ log (z + x)` on `[0, n]`, which expresses Euler's sequence `GammaSeq z n = n^z n! / ∏ (z + k)`
as `√(2π) exp ((z - 1/2) log z - z) exp (stirlingRest z n - logRemainder z n)` with
`stirlingRest z n → 1/(12 z)` (`GammaSeq_eq`, `tendsto_stirlingRest`) and
`‖logRemainder z n‖ ≤ 1/(30 (Im z)²)` uniformly in `n` (`norm_logRemainder_le`). Since
`GammaSeq z n → Γ(z)`, the limit of `exp (logRemainder z n)` lies in the compact set
`exp '' closedBall 0 (1/(30 (Im z)²))`, which gives `ρ` without identifying the limit of the
remainder.
-/

public section

open Complex Real Set Filter Topology MeasureTheory intervalIntegral EulerMaclaurin

namespace Complex.Stirling

section Log

variable {z : ℂ}

/--
@isnad1 id=hasderiv.0h2v.s6.1d2cee25134d from=translated src=- shape=1204dd10 vocab=a58dae6f
-/
theorem hasDerivAt_add_ofReal (z : ℂ) (x : ℝ) : HasDerivAt (fun x : ℝ => z + (x : ℂ)) 1 x :=
  (hasDerivAt_id x).ofReal_comp.const_add z

/--
@isnad1 id=hasderiv.0h2v.s6.9e39ddaeabf8 from=translated src=- shape=dedfb833 vocab=415cbc4a
-/
theorem hasDerivAt_sq_add (z : ℂ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => (z + x) ^ 2) (2 * (z + x)) x := by
  have := (hasDerivAt_add_ofReal z x).mul (hasDerivAt_add_ofReal z x)
  refine (this.congr_deriv (by ring)).congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun y => by simp [sq]

variable (hz : z.im ≠ 0)
include hz

/--
@isnad1 id=ne.1h2v.s5.1c19967f4f42 from=translated src=- shape=62ba10bf vocab=035a1fdb
-/
theorem add_ofReal_ne_zero (x : ℝ) : z + x ≠ 0 := fun h => hz (by simpa using congrArg Complex.im h)

/--
@isnad1 id=mem.1h2v.s5.170b766975c8 from=translated src=- shape=5ce07e1c vocab=66cdbbe2
-/
theorem add_ofReal_mem_slitPlane (x : ℝ) : z + x ∈ slitPlane :=
  mem_slitPlane_iff.2 (Or.inr (by simpa using hz))

/--
@isnad1 id=hasderiv.1h2v.s6.9c0cfd47b9bb from=translated src=- shape=3004e770 vocab=bbafab58
-/
theorem hasDerivAt_log_add (x : ℝ) :
    HasDerivAt (fun x : ℝ => Complex.log (z + x)) ((z + x)⁻¹) x := by
  have := (hasDerivAt_add_ofReal z x).clog_real (add_ofReal_mem_slitPlane hz x)
  simpa using this

/--
@isnad1 id=hasderiv.1h2v.s6.d0c2d6df8747 from=translated src=- shape=bdc59c27 vocab=4399dc2f
-/
theorem hasDerivAt_inv_add (x : ℝ) :
    HasDerivAt (fun x : ℝ => (z + x)⁻¹) (-((z + x) ^ 2)⁻¹) x := by
  have := (hasDerivAt_add_ofReal z x).inv (add_ofReal_ne_zero hz x)
  exact this.congr_deriv (by ring)

/--
@isnad1 id=hasderiv.1h2v.s7.be0b8ccba8a3 from=translated src=- shape=70647ca2 vocab=84ec652e
-/
theorem hasDerivAt_neg_inv_sq_add (x : ℝ) :
    HasDerivAt (fun x : ℝ => -((z + x) ^ 2)⁻¹) (2 * ((z + x) ^ 3)⁻¹) x := by
  have h := hasDerivAt_sq_add z x
  have hne := add_ofReal_ne_zero hz x
  have := (h.inv (pow_ne_zero 2 hne)).neg
  refine this.congr_deriv ?_
  field_simp

/--
@isnad1 id=hasderiv.1h2v.s6.821e36b43342 from=translated src=- shape=5c04f695 vocab=01211817
-/
theorem hasDerivAt_antideriv_log (x : ℝ) :
    HasDerivAt (fun x : ℝ => (z + x) * Complex.log (z + x) - (z + x)) (Complex.log (z + x)) x := by
  have h := hasDerivAt_add_ofReal z x
  have := (h.mul (hasDerivAt_log_add hz x)).sub h
  refine this.congr_deriv ?_
  rw [mul_inv_cancel₀ (add_ofReal_ne_zero hz x)]
  ring

/--
@isnad1 id=eq.1h2v.s7.fdfcfb055d6b from=translated src=- shape=8a6680cf vocab=9963143c
-/
theorem integral_log_add (n : ℕ) :
    ∫ x in (0 : ℝ)..n, Complex.log (z + x) =
      (z + n) * Complex.log (z + n) - (z + n) - (z * Complex.log z - z) := by
  have hcont : Continuous fun x : ℝ => Complex.log (z + x) :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_log_add hz x).continuousAt
  have := integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_antideriv_log hz x)
    (hcont.intervalIntegrable (0 : ℝ) n)
  rw [this]
  simp

/-- The Euler–Maclaurin remainder for `log (z + x)` on `[0, n]`.-/
noncomputable def logRemainder (z : ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n, ∫ x in (k : ℝ)..(k + 1 : ℕ), 2 * ((z + x) ^ 3)⁻¹ * P3 (x - k)

/--
@isnad1 id=eq.1h2v.s7.554383b92e64 from=translated src=- shape=b5b8463c vocab=da2bf8d7
-/
theorem sum_log_add_eq (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Complex.log (z + k) =
      (z + n) * Complex.log (z + n) - (z + n) - (z * Complex.log z - z) +
        (Complex.log z + Complex.log (z + n)) / 2 + ((z + n)⁻¹ - z⁻¹) / 12 + logRemainder z n := by
  have hcont : Continuous fun x : ℝ => 2 * ((z + x) ^ 3)⁻¹ := by
    have : ∀ x : ℝ, (z + x) ^ 3 ≠ 0 := fun x => pow_ne_zero 3 (add_ofReal_ne_zero hz x)
    fun_prop (disch := exact this _)
  have := sum_eq_integral_add (f := fun x : ℝ => Complex.log (z + x)) (f' := fun x => (z + x)⁻¹)
    (f'' := fun x => -((z + x) ^ 2)⁻¹) (f''' := fun x => 2 * ((z + x) ^ 3)⁻¹) n
    (hasDerivAt_log_add hz) (hasDerivAt_inv_add hz) (hasDerivAt_neg_inv_sq_add hz) hcont
  simp only [Complex.ofReal_natCast, ofReal_zero, add_zero] at this
  rw [this, integral_log_add hz n]
  rfl

end Log

/-- The Stirling main term `√(2π) exp ((z - 1/2) log z - z)`.-/
noncomputable def stirlingMain (z : ℂ) : ℂ :=
  (Real.sqrt (2 * π) : ℂ) * Complex.exp ((z - 1 / 2) * Complex.log z - z)

/-- The part of the exponent of `GammaSeq z n / stirlingMain z` that tends to `1/(12 z)`.-/
noncomputable def stirlingRest (z : ℂ) (n : ℕ) : ℂ :=
  z - (z + n + 1 / 2) * Complex.log (1 + z / n) +
    (Real.log (Stirling.stirlingSeq n / Real.sqrt π) : ℂ) + (12 * z)⁻¹ - (12 * (z + n))⁻¹

/--
@isnad1 id=ne.0h1v.s3.b75b900152c8 from=translated src=- shape=b14ee516 vocab=f4ebe6a8
-/
theorem stirlingMain_ne_zero (z : ℂ) : stirlingMain z ≠ 0 := by
  unfold stirlingMain
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (by positivity)).ne')
    (Complex.exp_ne_zero _)

/--
@isnad1 id=eq.1h1v.s6.decec228948e from=translated src=- shape=7ca535fa vocab=45434930
-/
theorem log_stirlingSeq {n : ℕ} (hn : 0 < n) :
    Real.log (Stirling.stirlingSeq n) =
      Real.log n.factorial - (Real.log 2 + Real.log n) / 2 - n * (Real.log n - 1) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  unfold Stirling.stirlingSeq
  rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_sqrt (by positivity), Real.log_pow, Real.log_div hn'.ne' (Real.exp_pos 1).ne',
    Real.log_exp, Real.log_mul (by norm_num) hn'.ne']
  ring

/--
@isnad1 id=lt.1h1v.s4.c18f71640b9f from=translated src=- shape=7f2e781e vocab=3784312a
-/
theorem stirlingSeq_pos {n : ℕ} (hn : 0 < n) : 0 < Stirling.stirlingSeq n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  unfold Stirling.stirlingSeq
  positivity

/--
@isnad1 id=ne.1h2v.s5.1e6a3f9578b2 from=translated src=- shape=c5e6e33d vocab=78518fad
-/
theorem add_natCast_ne_zero {z : ℂ} (hz : z.im ≠ 0) (j : ℕ) : z + j ≠ 0 :=
  fun h => hz (by simpa using congrArg Complex.im h)

/--
@isnad1 id=eq.2h2v.s6.01aa6543cfa3 from=translated src=- shape=be1fc4a4 vocab=7837ff52
-/
theorem log_add_natCast {z : ℂ} (hz : z.im ≠ 0) {n : ℕ} (hn : 0 < n) :
    Complex.log (z + n) = Real.log n + Complex.log (1 + z / n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hne : (1 : ℂ) + z / n ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [Complex.div_im, hn'.ne'] at this
    exact hz (by simpa [hn'.ne'] using this)
  have := Complex.log_ofReal_mul hn' hne
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2 : ((n : ℝ) : ℂ) * (1 + z / n) = z + n := by
    push_cast
    field_simp
    ring
  rw [← h2, this]

/--
@isnad1 id=eq.2h2v.s5.a1b1fefffb08 from=translated src=- shape=2c68c260 vocab=a89e118e
-/
theorem GammaSeq_eq {z : ℂ} (hz : z.im ≠ 0) {n : ℕ} (hn : 0 < n) :
    Complex.GammaSeq z n =
      stirlingMain z * Complex.exp (stirlingRest z n - logRemainder z n) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  -- the left side as an exponential
  have hprod : ∏ j ∈ Finset.range (n + 1), (z + j) =
      Complex.exp (∑ j ∈ Finset.range (n + 1), Complex.log (z + j)) := by
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun j _ => (Complex.exp_log (add_natCast_ne_zero hz j)).symm
  have hfact : (n.factorial : ℂ) = Complex.exp (Real.log n.factorial) := by
    rw [← Complex.ofReal_exp, Real.exp_log (Nat.cast_pos.2 n.factorial_pos)]
    push_cast
    rfl
  have hL : Complex.GammaSeq z n = Complex.exp (Real.log n * z + Real.log n.factorial -
      ∑ j ∈ Finset.range (n + 1), Complex.log (z + j)) := by
    rw [Complex.GammaSeq, hprod, hfact, Complex.cpow_def_of_ne_zero hnC,
      ← Complex.exp_add, ← Complex.exp_sub]
    simp only [Complex.natCast_log]
  -- the right side as an exponential
  have hsqrt : (Real.sqrt (2 * π) : ℂ) = Complex.exp (((Real.log 2 + Real.log π) / 2 : ℝ)) := by
    rw [← Real.log_mul (by norm_num) Real.pi_pos.ne', ← Real.log_sqrt (by positivity),
      ← Complex.ofReal_exp, Real.exp_log (by positivity)]
  have hR : stirlingMain z * Complex.exp (stirlingRest z n - logRemainder z n) =
      Complex.exp ((Real.log 2 + Real.log π) / 2 + ((z - 1 / 2) * Complex.log z - z) +
        (stirlingRest z n - logRemainder z n)) := by
    rw [stirlingMain, hsqrt, ← Complex.exp_add, ← Complex.exp_add]
    push_cast
    rfl
  rw [hL, hR]
  congr 1
  -- the exponents agree
  rw [sum_log_add_eq hz n, stirlingRest, log_add_natCast hz hn,
    Real.log_div (stirlingSeq_pos hn).ne' (by positivity), Real.log_sqrt Real.pi_pos.le,
    log_stirlingSeq hn]
  push_cast
  field_simp
  ring

section Bound

/-- `G a b x = (a + x) / (b² √((a+x)² + b²))`, an antiderivative of `((a+x)² + b²)^{-3/2}`.-/
noncomputable def G (a b x : ℝ) : ℝ := (a + x) / (b ^ 2 * Real.sqrt ((a + x) ^ 2 + b ^ 2))

/--
@isnad1 id=hasderiv.1h3v.s7.e84a66955f6b from=translated src=- shape=19c6882d vocab=91c12e79
-/
theorem hasDerivAt_G {a b : ℝ} (hb : b ≠ 0) (x : ℝ) :
    HasDerivAt (G a b) (1 / Real.sqrt ((a + x) ^ 2 + b ^ 2) ^ 3) x := by
  have hpos : 0 < (a + x) ^ 2 + b ^ 2 := by positivity
  have hS : 0 < Real.sqrt ((a + x) ^ 2 + b ^ 2) := Real.sqrt_pos.2 hpos
  have hS2 := Real.sq_sqrt hpos.le
  have hu : HasDerivAt (fun y : ℝ => a + y) 1 x := (hasDerivAt_id x).const_add a
  have hin : HasDerivAt (fun y : ℝ => (a + y) ^ 2 + b ^ 2) (2 * (a + x)) x := by
    have := (hu.pow 2).add_const (b ^ 2)
    simpa using this
  have hsq := hin.sqrt hpos.ne'
  have hv := hsq.const_mul (b ^ 2)
  have := hu.div hv (by positivity)
  refine this.congr_deriv ?_
  set S := Real.sqrt ((a + x) ^ 2 + b ^ 2) with hSdef
  field_simp
  linear_combination hS2

/--
@isnad1 id=le.1h3v.s5.69f150c95abe from=translated src=- shape=b4c4f63d vocab=9510e252
-/
theorem abs_G_le {a b : ℝ} (hb : b ≠ 0) (x : ℝ) : |G a b x| ≤ 1 / b ^ 2 := by
  have hpos : 0 < (a + x) ^ 2 + b ^ 2 := by positivity
  have hS : 0 < Real.sqrt ((a + x) ^ 2 + b ^ 2) := Real.sqrt_pos.2 hpos
  have hb2 : 0 < b ^ 2 := by positivity
  have habs : |a + x| ≤ Real.sqrt ((a + x) ^ 2 + b ^ 2) := Real.abs_le_sqrt (by nlinarith)
  have hden : 0 < b ^ 2 * Real.sqrt ((a + x) ^ 2 + b ^ 2) := mul_pos hb2 hS
  unfold G
  rw [abs_div, abs_of_pos hden, div_le_div_iff₀ hden hb2]
  calc |a + x| * b ^ 2 ≤ Real.sqrt ((a + x) ^ 2 + b ^ 2) * b ^ 2 := by gcongr
    _ = 1 * (b ^ 2 * Real.sqrt ((a + x) ^ 2 + b ^ 2)) := by ring

/--
@isnad1 id=eq.0h2v.s6.bd55ae039678 from=translated src=- shape=cd4f2427 vocab=ee9c003e
-/
theorem norm_add_ofReal (z : ℂ) (x : ℝ) : ‖z + x‖ = Real.sqrt ((z.re + x) ^ 2 + z.im ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp

/--
@isnad1 id=le.2h3v.s7.0a7daeba8261 from=translated src=- shape=d08f4535 vocab=f5df8b7f
-/
theorem norm_integrand_le {z : ℂ} (hz : z.im ≠ 0) (k : ℕ) {x : ℝ} (hx : x ∈ Icc (k : ℝ) (k + 1)) :
    ‖2 * ((z + x) ^ 3)⁻¹ * P3 (x - k)‖ ≤
      1 / 60 * (1 / Real.sqrt ((z.re + x) ^ 2 + z.im ^ 2) ^ 3) := by
  rw [norm_mul, norm_mul, norm_inv, norm_pow, norm_add_ofReal, Complex.norm_ofNat]
  have hP := norm_P3_le (u := x - k) (by linarith [hx.1]) (by linarith [hx.2])
  have hS : 0 < Real.sqrt ((z.re + x) ^ 2 + z.im ^ 2) := Real.sqrt_pos.2 (by positivity)
  calc 2 * (Real.sqrt ((z.re + x) ^ 2 + z.im ^ 2) ^ 3)⁻¹ * ‖P3 (x - k)‖ ≤
      2 * (Real.sqrt ((z.re + x) ^ 2 + z.im ^ 2) ^ 3)⁻¹ * (1 / 120) := by gcongr
    _ = _ := by ring

/--
@isnad1 id=le.1h2v.s6.83d2eff08dc5 from=translated src=- shape=4aa6e797 vocab=c1c57bc2
-/
theorem norm_logRemainder_le {z : ℂ} (hz : z.im ≠ 0) (n : ℕ) :
    ‖logRemainder z n‖ ≤ 1 / (30 * z.im ^ 2) := by
  set g : ℝ → ℝ := fun x => 1 / Real.sqrt ((z.re + x) ^ 2 + z.im ^ 2) ^ 3 with hg
  have hgc : Continuous g := by
    have : ∀ x : ℝ, Real.sqrt ((z.re + x) ^ 2 + z.im ^ 2) ^ 3 ≠ 0 := fun x =>
      pow_ne_zero 3 (Real.sqrt_pos.2 (by positivity)).ne'
    rw [hg]
    fun_prop (disch := exact this _)
  have hterm : ∀ k : ℕ, ‖∫ x in (k : ℝ)..(k + 1 : ℕ), 2 * ((z + x) ^ 3)⁻¹ * P3 (x - k)‖ ≤
      1 / 60 * (G z.re z.im (k + 1 : ℕ) - G z.re z.im k) := by
    intro k
    have hk : (k : ℝ) ≤ (k + 1 : ℕ) := by push_cast; linarith
    have hint : ∫ x in (k : ℝ)..(k + 1 : ℕ), 1 / 60 * g x =
        1 / 60 * (G z.re z.im (k + 1 : ℕ) - G z.re z.im k) := by
      rw [intervalIntegral.integral_const_mul,
        integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_G hz x) (hgc.intervalIntegrable _ _)]
    rw [← hint]
    refine norm_integral_le_of_norm_le hk ?_ ((hgc.const_mul _).intervalIntegrable _ _)
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx' : x ∈ Icc (k : ℝ) (k + 1) := ⟨hx.1.le, by simpa using hx.2⟩
    exact norm_integrand_le hz k hx'
  calc ‖logRemainder z n‖ ≤ ∑ k ∈ Finset.range n,
        ‖∫ x in (k : ℝ)..(k + 1 : ℕ), 2 * ((z + x) ^ 3)⁻¹ * P3 (x - k)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, 1 / 60 * (G z.re z.im (k + 1 : ℕ) - G z.re z.im k) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = 1 / 60 * (G z.re z.im n - G z.re z.im 0) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub (fun k : ℕ => G z.re z.im k)]
        simp
    _ ≤ 1 / 60 * (1 / z.im ^ 2 + 1 / z.im ^ 2) := by
        gcongr
        have h1 := abs_G_le (a := z.re) hz (n : ℝ)
        have h2 := abs_G_le (a := z.re) hz 0
        rw [abs_le] at h1 h2
        linarith [h1.2, h2.1]
    _ = 1 / (30 * z.im ^ 2) := by ring

end Bound

section Limit

variable {z : ℂ}

/--
@isnad1 id=ne.1h1v.s4.6a50cfd61fa0 from=translated src=- shape=790175b1 vocab=d59ed19f
-/
theorem ne_zero_of_im_ne_zero' (hz : z.im ≠ 0) : z ≠ 0 := fun h => hz (by simp [h])

/--
@isnad1 id=tendsto.0h1v.s5.781df05deda0 from=translated src=- shape=031e1207 vocab=117eb1b8
-/
theorem tendsto_div_natCast : Tendsto (fun n : ℕ => z / n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have : (fun n : ℕ => ‖z / n‖) = fun n : ℕ => ‖z‖ / n := by
    ext n; rw [norm_div, Complex.norm_natCast]
  rw [this]
  exact tendsto_const_div_atTop_nhds_zero_nat _

/--
@isnad1 id=tendsto.1h1v.s6.e1ed6c787d02 from=translated src=- shape=19b16e56 vocab=570852d9
-/
theorem tendsto_div_natCast_nhdsNE (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ => z / n) atTop (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨tendsto_div_natCast (z := z), ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  exact div_ne_zero (ne_zero_of_im_ne_zero' hz) hn'

/--
@isnad1 id=tendsto.0h1v.s5.fd660266f9fb from=translated src=- shape=0ebaf4e8 vocab=65a15041
-/
theorem tendsto_log_one_add_div :
    Tendsto (fun n : ℕ => Complex.log (1 + z / n)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 1 + z / n) atTop (𝓝 1) := by
    simpa using (tendsto_div_natCast (z := z)).const_add 1
  have := (continuousAt_clog one_mem_slitPlane).tendsto.comp h1
  simpa [Function.comp_def] using this

/--
@isnad1 id=tendsto.1h1v.s6.d6cf35ebe567 from=translated src=- shape=e8e5f7ca vocab=c5afdfec
-/
theorem tendsto_inv_mul_log_one_add_div (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ => (z / n)⁻¹ * Complex.log (1 + z / n)) atTop (𝓝 1) := by
  have h := (Complex.hasDerivAt_log one_mem_slitPlane).tendsto_slope_zero.comp
    (tendsto_div_natCast_nhdsNE hz)
  simpa [Function.comp_def] using h

/--
@isnad1 id=tendsto.1h1v.s6.9520fff86128 from=translated src=- shape=7e96f945 vocab=35048a21
-/
theorem tendsto_mul_log_one_add_div (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ => (z + n + 1 / 2) * Complex.log (1 + z / n)) atTop (𝓝 z) := by
  have h := ((tendsto_log_one_add_div (z := z)).const_mul (z + 1 / 2)).add
    ((tendsto_inv_mul_log_one_add_div hz).const_mul z)
  simp only [mul_zero, mul_one, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  have hz0 := ne_zero_of_im_ne_zero' hz
  field_simp
  ring

/--
@isnad1 id=tendsto.1h1v.s6.50a5037ef2d8 from=translated src=- shape=3169ec3d vocab=ab5848b9
-/
theorem tendsto_inv_add_natCast (hz : z.im ≠ 0) :
    Tendsto (fun n : ℕ => (12 * (z + n))⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 12 * z * (1 + z / n)) atTop (𝓝 (12 * z * (1 + 0))) :=
    tendsto_const_nhds.mul ((tendsto_div_natCast (z := z)).const_add 1)
  have h := (tendsto_div_natCast (z := z)).div h1 (by simp [ne_zero_of_im_ne_zero' hz])
  simp only [zero_div] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.1 hn)
  have hz0 := ne_zero_of_im_ne_zero' hz
  have hzn : z + n ≠ 0 := add_natCast_ne_zero hz n
  simp only [Pi.div_apply]
  field_simp
  rw [add_comm (n : ℂ) z, div_self hzn]

/--
@isnad1 id=tendsto.0h0v.s5.46878406797b from=translated src=- shape=52e5a813 vocab=b0bcf63a
-/
theorem tendsto_log_stirlingSeq_div :
    Tendsto (fun n : ℕ => (Real.log (Stirling.stirlingSeq n / Real.sqrt π) : ℂ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => Stirling.stirlingSeq n / Real.sqrt π) atTop (𝓝 1) := by
    have := Stirling.tendsto_stirlingSeq_sqrt_pi.div_const (Real.sqrt π)
    rwa [div_self (Real.sqrt_pos.2 Real.pi_pos).ne'] at this
  have h2 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h1)
  simp only [Function.comp_def, Real.log_one] at h2
  have := (Complex.continuous_ofReal.tendsto 0).comp h2
  simpa [Function.comp_def] using this

/--
@isnad1 id=tendsto.1h1v.s5.8cb01826ce06 from=translated src=- shape=a79d44d8 vocab=17a8990d
-/
theorem tendsto_stirlingRest (hz : z.im ≠ 0) :
    Tendsto (stirlingRest z) atTop (𝓝 ((12 * z)⁻¹)) := by
  have h := ((((tendsto_const_nhds (x := z)).sub (tendsto_mul_log_one_add_div hz)).add
    tendsto_log_stirlingSeq_div).add (tendsto_const_nhds (x := (12 * z)⁻¹))).sub
    (tendsto_inv_add_natCast hz)
  simp only [sub_self, zero_add, sub_zero] at h
  exact h

end Limit

/--
@isnad1 id=ne.1h1v.s4.c7a2747d8b95 from=translated src=- shape=03055dfc vocab=bebdf0b9
-/
theorem Gamma_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : Complex.Gamma z ≠ 0 :=
  Complex.Gamma_ne_zero fun m h => hz (by simp [h])

/-- Stirling's formula with an explicit remainder: for `Im z ≠ 0`,
`Γ(z) = √(2π) exp ((z - 1/2) log z - z + 1/(12 z) + ρ)` with `‖ρ‖ ≤ 1 / (30 (Im z)²)`.
@isnad1 id=ex.1h1v.s6.d934267effc2 from=translated src=- shape=cf27facc vocab=2b779778
-/
theorem exists_Gamma_eq {z : ℂ} (hz : z.im ≠ 0) :
    ∃ ρ : ℂ, ‖ρ‖ ≤ 1 / (30 * z.im ^ 2) ∧
      Complex.Gamma z = stirlingMain z * Complex.exp ((12 * z)⁻¹ + ρ) := by
  set c : ℝ := 1 / (30 * z.im ^ 2) with hc
  set K : Set ℂ := Complex.exp '' Metric.closedBall 0 c with hK
  have hKc : IsCompact K := (isCompact_closedBall 0 c).image Complex.continuous_exp
  have hmem : ∀ n, Complex.exp (logRemainder z n) ∈ K := fun n =>
    ⟨logRemainder z n, mem_closedBall_zero_iff.2 (norm_logRemainder_le hz n), rfl⟩
  have hΓ := Gamma_ne_zero_of_im_ne_zero hz
  set L : ℂ := stirlingMain z * Complex.exp ((12 * z)⁻¹) / Complex.Gamma z with hL
  have hlim : Tendsto (fun n => Complex.exp (logRemainder z n)) atTop (𝓝 L) := by
    have h := (tendsto_const_nhds (x := stirlingMain z).mul
      ((tendsto_stirlingRest hz).cexp)).div (Complex.GammaSeq_tendsto_Gamma z) hΓ
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Pi.div_apply]
    rw [GammaSeq_eq hz hn, Complex.exp_sub]
    have := stirlingMain_ne_zero z
    have := Complex.exp_ne_zero (stirlingRest z n)
    have := Complex.exp_ne_zero (logRemainder z n)
    field_simp
  have hLK : L ∈ K := hKc.isClosed.mem_of_tendsto hlim (Eventually.of_forall hmem)
  obtain ⟨ρ', hρ', hρ'L⟩ := hLK
  refine ⟨-ρ', by simpa using mem_closedBall_zero_iff.1 hρ', ?_⟩
  rw [Complex.exp_add, Complex.exp_neg, hρ'L, hL]
  have := stirlingMain_ne_zero z
  field_simp

/-- Stirling's formula with an explicit remainder, for `Im z ≠ 0`:
`Γ(z) = √(2π) exp ((z - 1/2) log z - z + E)` with `‖E‖ ≤ 1/(12 ‖z‖) + 1/(30 (Im z)²)`.
@isnad1 id=ex.1h1v.s7.da6404e10c09 from=translated src=- shape=16383ab9 vocab=360d40cb
-/
theorem exists_Gamma_eq_sqrt_two_pi_mul_exp {z : ℂ} (hz : z.im ≠ 0) :
    ∃ E : ℂ, ‖E‖ ≤ 1 / (12 * ‖z‖) + 1 / (30 * z.im ^ 2) ∧
      Complex.Gamma z = Real.sqrt (2 * π) * Complex.exp ((z - 1 / 2) * Complex.log z - z + E) := by
  obtain ⟨ρ, hρ, hΓ⟩ := exists_Gamma_eq hz
  refine ⟨(12 * z)⁻¹ + ρ, ?_, ?_⟩
  · refine (norm_add_le _ _).trans ?_
    rw [norm_inv, norm_mul, Complex.norm_ofNat, one_div]
    exact add_le_add le_rfl hρ
  · rw [hΓ, stirlingMain, mul_assoc, ← Complex.exp_add]

end Complex.Stirling
