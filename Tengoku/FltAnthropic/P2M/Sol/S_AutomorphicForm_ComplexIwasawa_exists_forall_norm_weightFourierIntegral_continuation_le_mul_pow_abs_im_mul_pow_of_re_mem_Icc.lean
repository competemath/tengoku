import Tengoku
import Tengoku.Seed.Analysis.SpecialFunctions.Gamma.Basic
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.MeasureTheory.Measure.Lebesgue.Complex
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv
import Tengoku.Seed.Analysis.Complex.CauchyIntegral
import Tengoku.Seed.Analysis.Calculus.ParametricIntegral
import Tengoku.Seed.MeasureTheory.Integral.IntegralEqImproper
import Tengoku.FltAnthropic.Theorems.Thm_AutomorphicForm_ComplexIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_ComplexIwasawa_exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_norm_weightFourierIntegral_continuation_le_mul_pow_abs_im_mul_pow_of_re_mem_Icc

open Set MeasureTheory
open scoped Topology ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace Ws31
namespace ArchC

def Bc (z : ℂ) : ℂ := ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)

def Ec (ζ z : ℂ) : ℂ := Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))

def F (a b : ℕ) (w ζ z : ℂ) : ℂ := z ^ a * (starRingEnd ℂ) z ^ b * Bc z ^ (-w) * Ec ζ z

def jj (a b : ℕ) (w ζ : ℂ) : ℂ := ∫ z : ℂ, F a b w ζ z

def cZ (ζ : ℂ) : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (starRingEnd ℂ) ζ

/--
@isnad1 id=ne.1h1v.s4.b9b291909ae7 from=translated src=- shape=5aedd577 vocab=a57bad55
-/
theorem cZ_ne_zero {ζ : ℂ} (hζ : ζ ≠ 0) : cZ ζ ≠ 0 := by
  unfold cZ
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_
  · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  · exact (map_ne_zero (starRingEnd ℂ)).mpr hζ

/--
@isnad1 id=eq.0h1v.s5.821bb6cf4887 from=translated src=- shape=71a20443 vocab=54e6234c
-/
theorem norm_cZ (ζ : ℂ) : ‖cZ ζ‖ = 2 * Real.pi * ‖ζ‖ := by
  unfold cZ
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_conj, Complex.norm_two]

/--
@isnad1 id=lt.0h1v.s5.2c020e684e4f from=translated src=- shape=3f2b734f vocab=cecca3b4
-/
theorem one_add_norm_sq_pos (z : ℂ) : 0 < 1 + ‖z‖ ^ 2 := by positivity

/--
@isnad1 id=le.0h1v.s5.a297539f23d3 from=translated src=- shape=3f2b734f vocab=a046eacb
-/
theorem one_le_one_add_norm_sq (z : ℂ) : 1 ≤ 1 + ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]

/--
@isnad1 id=eq.0h2v.s4.8b964f276c2e from=translated src=- shape=0e981eee vocab=8f00fe85
-/
theorem norm_Ec (ζ z : ℂ) : ‖Ec ζ z‖ = 1 := by
  rw [Ec, ← neg_mul, ← Complex.ofReal_neg]
  exact Complex.norm_exp_ofReal_mul_I _

/--
@isnad1 id=eq.0h5v.s6.ce0e9f1793a8 from=translated src=- shape=ea5b7ff1 vocab=5d372206
-/
theorem norm_F (a b : ℕ) (w ζ z : ℂ) : ‖F a b w ζ z‖ = ‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-w.re) := by
  unfold F Bc
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_add_norm_sq_pos z), Complex.neg_re, norm_Ec, mul_one, pow_add]

/--
@isnad1 id=le.0h2v.s6.ff674d3f88b2 from=translated src=- shape=e44f0f5d vocab=76c00b32
-/
theorem norm_pow_le_bracket (m : ℕ) (z : ℂ) : ‖z‖ ^ m ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
  have hR0 : 0 < 1 + ‖z‖ ^ 2 := one_add_norm_sq_pos z
  have h1 : ‖z‖ ≤ (1 + ‖z‖ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    refine Real.le_sqrt_of_sq_le ?_
    linarith
  calc ‖z‖ ^ m = ‖z‖ ^ (m : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ ((1 + ‖z‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (m : ℝ) := Real.rpow_le_rpow (norm_nonneg _) h1 (Nat.cast_nonneg _)
    _ = (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
        rw [← Real.rpow_mul hR0.le]
        ring_nf

/--
@isnad1 id=le.1h6v.s7.1bc0a5f5800f from=translated src=- shape=706656f3 vocab=ce6d842a
-/
theorem norm_F_le (a b : ℕ) {σ : ℝ} {w : ℂ} (hw : σ ≤ w.re) (ζ z : ℂ) :
    ‖F a b w ζ z‖ ≤ (1 + ‖z‖ ^ 2) ^ (-(2 * σ - ((a + b : ℕ) : ℝ)) / 2) := by
  rw [norm_F]
  have hR0 : 0 < 1 + ‖z‖ ^ 2 := one_add_norm_sq_pos z
  have h2 : (1 + ‖z‖ ^ 2) ^ (-w.re) ≤ (1 + ‖z‖ ^ 2) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_one_add_norm_sq z) (by linarith)
  calc ‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-w.re)
      ≤ (1 + ‖z‖ ^ 2) ^ (((a + b : ℕ) : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-σ) :=
        mul_le_mul (norm_pow_le_bracket (a + b) z) h2 (Real.rpow_nonneg hR0.le _) (Real.rpow_nonneg hR0.le _)
    _ = (1 + ‖z‖ ^ 2) ^ (-(2 * σ - ((a + b : ℕ) : ℝ)) / 2) := by
        rw [← Real.rpow_add hR0]
        ring_nf

/--
@isnad1 id=integrab.1h3v.s7.7e6e72133f88 from=translated src=- shape=1ff2884e vocab=a9b0fae6
-/
theorem integrable_bracket (a b : ℕ) {σ : ℝ} (hσ : ((a + b : ℕ) : ℝ) / 2 + 1 < σ) :
    Integrable (fun z : ℂ => (1 + ‖z‖ ^ 2) ^ (-(2 * σ - ((a + b : ℕ) : ℝ)) / 2)) := by
  refine integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) ?_
  rw [Complex.finrank_real_complex]
  push_cast at hσ ⊢
  linarith

/--
@isnad1 id=continuo.0h0v.s4.137acfd2fff9 from=translated src=- shape=e3d48bcb vocab=5b00397e
-/
theorem continuous_Bc : Continuous Bc :=
  Complex.continuous_ofReal.comp (continuous_const.add (continuous_norm.pow 2))

/--
@isnad1 id=mem.0h1v.s3.a227546c7a7d from=translated src=- shape=ca401064 vocab=2006d2da
-/
theorem Bc_mem_slitPlane (z : ℂ) : Bc z ∈ Complex.slitPlane :=
  Complex.ofReal_mem_slitPlane.2 (one_add_norm_sq_pos z)

/--
@isnad1 id=continuo.0h1v.s5.eec80b68b5be from=translated src=- shape=f736e2c1 vocab=cfbeafb3
-/
theorem continuous_Ec (ζ : ℂ) : Continuous (Ec ζ) := by
  unfold Ec
  have h1 : Continuous (fun z : ℂ => (4 * Real.pi * (ζ * z).re : ℝ)) :=
    continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul continuous_id))
  exact Complex.continuous_exp.comp (((Complex.continuous_ofReal.comp h1).mul continuous_const).neg)

/--
@isnad1 id=continuo.0h4v.s5.7e21ba3ce353 from=translated src=- shape=8113348d vocab=7fb7ee53
-/
theorem continuous_F (a b : ℕ) (w ζ : ℂ) : Continuous (fun z => F a b w ζ z) := by
  have h1 : Continuous (fun z : ℂ => z ^ a * conj z ^ b) :=
    (continuous_id.pow a).mul (Complex.continuous_conj.pow b)
  have h2 : Continuous (fun z : ℂ => Bc z ^ (-w)) :=
    continuous_Bc.cpow continuous_const Bc_mem_slitPlane
  exact (h1.mul h2).mul (continuous_Ec ζ)

/--
@isnad1 id=integrab.1h4v.s6.ef6d52ab848b from=translated src=- shape=92a91aed vocab=5082b790
-/
theorem integrable_F (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) (ζ : ℂ) :
    Integrable (fun z => F a b w ζ z) :=
  (integrable_bracket a b hw).mono' (continuous_F a b w ζ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => norm_F_le a b le_rfl ζ z)

def G (a b : ℕ) (w z : ℂ) : ℂ := z ^ a * conj z ^ b * Bc z ^ (-w)

def Gx (a b : ℕ) (w z : ℂ) : ℂ :=
  ((a : ℂ) * z ^ (a - 1) * 1 * conj z ^ b + z ^ a * ((b : ℂ) * conj z ^ (b - 1) * 1)) * Bc z ^ (-w)
    + z ^ a * conj z ^ b * (-w * Bc z ^ (-w - 1) * (((2 * z.re : ℝ)) : ℂ))

def Gy (a b : ℕ) (w z : ℂ) : ℂ :=
  ((a : ℂ) * z ^ (a - 1) * (1 * Complex.I) * conj z ^ b + z ^ a * ((b : ℂ) * conj z ^ (b - 1) * (-(1 * Complex.I))))
      * Bc z ^ (-w)
    + z ^ a * conj z ^ b * (-w * Bc z ^ (-w - 1) * (((2 * z.im : ℝ)) : ℂ))

def cX (ζ : ℂ) : ℂ := ((4 * Real.pi * ζ.re : ℝ) : ℂ) * Complex.I

def cY (ζ : ℂ) : ℂ := ((4 * Real.pi * ζ.im : ℝ) : ℂ) * Complex.I

/--
@isnad1 id=eq.0h2v.s4.75528f14e0de from=translated src=- shape=60689d7d vocab=8ee53555
-/
theorem mk_eq (x y : ℝ) : (⟨x, y⟩ : ℂ) = (x : ℂ) + (y : ℂ) * Complex.I := Complex.mk_eq_add_mul_I x y

/--
@isnad1 id=eq.0h2v.s5.8a6d88aad9eb from=translated src=- shape=bc238a59 vocab=1feee932
-/
theorem conj_mk' (x y : ℝ) : conj (⟨x, y⟩ : ℂ) = (x : ℂ) - (y : ℂ) * Complex.I := by
  rw [mk_eq, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; ring

/--
@isnad1 id=eq.0h2v.s6.6f51c785e0c5 from=translated src=- shape=9dd1f078 vocab=193323eb
-/
theorem norm_sq_mk (x y : ℝ) : ‖(⟨x, y⟩ : ℂ)‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_mk]; ring

/--
@isnad1 id=eq.0h2v.s6.7cc6a7ee0ab3 from=translated src=- shape=816c3bf5 vocab=cef6594f
-/
theorem Bc_mk (x y : ℝ) : Bc ⟨x, y⟩ = (((1 + (x ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
  rw [Bc, norm_sq_mk]

/--
@isnad1 id=eq.0h3v.s5.89523ffe1a3a from=translated src=- shape=60cdbdeb vocab=2d41a00e
-/
theorem re_mul_mk (ζ : ℂ) (x y : ℝ) : (ζ * ⟨x, y⟩).re = ζ.re * x - ζ.im * y := by
  simp [Complex.mul_re]

/--
@isnad1 id=eq.0h3v.s6.5e6d473f59b8 from=translated src=- shape=79680578 vocab=57608c82
-/
theorem Ec_mk (ζ : ℂ) (x y : ℝ) :
    Ec ζ ⟨x, y⟩ = Complex.exp (-(((4 * Real.pi * (ζ.re * x - ζ.im * y) : ℝ) : ℂ) * Complex.I)) := by
  rw [Ec, re_mul_mk]

/--
@isnad1 id=hasderiv.0h1v.s6.b7918fe4771e from=translated src=- shape=93588a94 vocab=1a38dff6
-/
theorem hasDerivAt_ofReal (x : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 x := by
  simpa using (hasDerivAt_id x).ofReal_comp

/--
@isnad1 id=lt.0h2v.s6.a227054943be from=translated src=- shape=c732094e vocab=65df512c
-/
theorem one_add_sq_sq_pos (x y : ℝ) : 0 < 1 + (x ^ 2 + y ^ 2) := by positivity

/--
@isnad1 id=hasderiv.0h5v.s6.a502744b497b from=translated src=- shape=52a7fb61 vocab=75abc2ef
-/
theorem hasDerivAt_G_x (a b : ℕ) (w : ℂ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => G a b w ⟨t, y⟩) (Gx a b w ⟨x, y⟩) x := by
  have hP := (hasDerivAt_pow a (((x : ℝ) : ℂ) + (y : ℂ) * Complex.I)).comp x
    ((hasDerivAt_ofReal x).add_const ((y : ℂ) * Complex.I))
  have hQ := (hasDerivAt_pow b (((x : ℝ) : ℂ) - (y : ℂ) * Complex.I)).comp x
    ((hasDerivAt_ofReal x).sub_const ((y : ℂ) * Complex.I))
  have hR : HasDerivAt (fun t : ℝ => 1 + (t ^ 2 + y ^ 2)) (2 * x) x := by
    have h := ((hasDerivAt_pow 2 x).add_const (y ^ 2)).const_add 1
    simpa using h
  have hB : HasDerivAt (fun t : ℝ => (((1 + (t ^ 2 + y ^ 2)) : ℝ) : ℂ)) (((2 * x) : ℝ) : ℂ) x := hR.ofReal_comp
  have hslit : (((1 + (x ^ 2 + y ^ 2)) : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr (one_add_sq_sq_pos x y)
  have hBw := (Complex.hasStrictDerivAt_cpow_const (c := -w) hslit).hasDerivAt.comp x hB
  have hprod := (hP.mul hQ).mul hBw
  have e : (fun t : ℝ => G a b w ⟨t, y⟩) = fun t : ℝ =>
      ((fun z : ℂ => z ^ a) ∘ (fun t : ℝ => ((t : ℝ) : ℂ) + (y : ℂ) * Complex.I)) t
      * ((fun z : ℂ => z ^ b) ∘ (fun t : ℝ => ((t : ℝ) : ℂ) - (y : ℂ) * Complex.I)) t
      * ((fun z : ℂ => z ^ (-w)) ∘ (fun t : ℝ => (((1 + (t ^ 2 + y ^ 2)) : ℝ) : ℂ))) t := by
    funext t
    simp only [Function.comp_apply, G]
    rw [conj_mk', Bc_mk, mk_eq]
  rw [e]
  refine hprod.congr_deriv ?_
  simp only [Function.comp_apply, Pi.mul_apply, Gx]
  rw [conj_mk', Bc_mk, mk_eq]

/--
@isnad1 id=hasderiv.0h5v.s6.f80be0692831 from=translated src=- shape=c428f87f vocab=14c3f279
-/
theorem hasDerivAt_G_y (a b : ℕ) (w : ℂ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => G a b w ⟨x, t⟩) (Gy a b w ⟨x, y⟩) y := by
  have hP := (hasDerivAt_pow a (((x : ℝ) : ℂ) + (y : ℂ) * Complex.I)).comp y
    (((hasDerivAt_ofReal y).mul_const Complex.I).const_add ((x : ℝ) : ℂ))
  have hQ := (hasDerivAt_pow b (((x : ℝ) : ℂ) - (y : ℂ) * Complex.I)).comp y
    (((hasDerivAt_ofReal y).mul_const Complex.I).const_sub ((x : ℝ) : ℂ))
  have hR : HasDerivAt (fun t : ℝ => 1 + (x ^ 2 + t ^ 2)) (2 * y) y := by
    have h := ((hasDerivAt_pow 2 y).const_add (x ^ 2)).const_add 1
    simpa using h
  have hB : HasDerivAt (fun t : ℝ => (((1 + (x ^ 2 + t ^ 2)) : ℝ) : ℂ)) (((2 * y) : ℝ) : ℂ) y := hR.ofReal_comp
  have hslit : (((1 + (x ^ 2 + y ^ 2)) : ℝ) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr (one_add_sq_sq_pos x y)
  have hBw := (Complex.hasStrictDerivAt_cpow_const (c := -w) hslit).hasDerivAt.comp y hB
  have hprod := (hP.mul hQ).mul hBw
  have e : (fun t : ℝ => G a b w ⟨x, t⟩) = fun t : ℝ =>
      ((fun z : ℂ => z ^ a) ∘ (fun t : ℝ => ((x : ℝ) : ℂ) + (t : ℂ) * Complex.I)) t
      * ((fun z : ℂ => z ^ b) ∘ (fun t : ℝ => ((x : ℝ) : ℂ) - (t : ℂ) * Complex.I)) t
      * ((fun z : ℂ => z ^ (-w)) ∘ (fun t : ℝ => (((1 + (x ^ 2 + t ^ 2)) : ℝ) : ℂ))) t := by
    funext t
    simp only [Function.comp_apply, G]
    rw [conj_mk', Bc_mk, mk_eq]
  rw [e]
  refine hprod.congr_deriv ?_
  simp only [Function.comp_apply, Pi.mul_apply, Gy]
  rw [conj_mk', Bc_mk, mk_eq]

/--
@isnad1 id=hasderiv.0h3v.s6.6ea1511c53d5 from=translated src=- shape=6e18ce3c vocab=8d0e4fb9
-/
theorem hasDerivAt_Ec_x (ζ : ℂ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => Ec ζ ⟨t, y⟩) (Ec ζ ⟨x, y⟩ * (-cX ζ)) x := by
  have h0 : HasDerivAt (fun t : ℝ => 4 * Real.pi * (ζ.re * t - ζ.im * y)) (4 * Real.pi * ζ.re) x := by
    have h := (((hasDerivAt_id x).const_mul ζ.re).sub_const (ζ.im * y)).const_mul (4 * Real.pi)
    simpa using h
  have h1 : HasDerivAt (fun t : ℝ => -(((4 * Real.pi * (ζ.re * t - ζ.im * y) : ℝ) : ℂ) * Complex.I))
      (-((((4 * Real.pi * ζ.re) : ℝ) : ℂ) * Complex.I)) x := ((h0.ofReal_comp).mul_const Complex.I).neg
  have e : (fun t : ℝ => Ec ζ ⟨t, y⟩) = fun t : ℝ =>
      Complex.exp (-(((4 * Real.pi * (ζ.re * t - ζ.im * y) : ℝ) : ℂ) * Complex.I)) := by
    funext t; exact Ec_mk ζ t y
  rw [e, Ec_mk]
  refine h1.cexp.congr_deriv ?_
  simp only [cX]

/--
@isnad1 id=hasderiv.0h3v.s6.fcdfd6cec7cc from=translated src=- shape=110adbc4 vocab=2b65774b
-/
theorem hasDerivAt_Ec_y (ζ : ℂ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => Ec ζ ⟨x, t⟩) (Ec ζ ⟨x, y⟩ * cY ζ) y := by
  have h0 : HasDerivAt (fun t : ℝ => 4 * Real.pi * (ζ.re * x - ζ.im * t)) (4 * Real.pi * (-ζ.im)) y := by
    have h := (((hasDerivAt_id y).const_mul ζ.im).const_sub (ζ.re * x)).const_mul (4 * Real.pi)
    simpa using h
  have h1 : HasDerivAt (fun t : ℝ => -(((4 * Real.pi * (ζ.re * x - ζ.im * t) : ℝ) : ℂ) * Complex.I))
      (-((((4 * Real.pi * -ζ.im) : ℝ) : ℂ) * Complex.I)) y := ((h0.ofReal_comp).mul_const Complex.I).neg
  have e : (fun t : ℝ => Ec ζ ⟨x, t⟩) = fun t : ℝ =>
      Complex.exp (-(((4 * Real.pi * (ζ.re * x - ζ.im * t) : ℝ) : ℂ) * Complex.I)) := by
    funext t; exact Ec_mk ζ x t
  rw [e, Ec_mk]
  refine h1.cexp.congr_deriv ?_
  simp only [cY]
  push_cast
  ring

/--
@isnad1 id=eq.0h1v.s6.f83aa2d9eaa5 from=translated src=- shape=73c41b61 vocab=c385d05c
-/
theorem two_re_eq (z : ℂ) : (((2 * z.re : ℝ)) : ℂ) = z + conj z :=
  Complex.ext (by simp [two_mul]) (by simp)

/--
@isnad1 id=eq.0h1v.s6.56a720be1458 from=translated src=- shape=edefd814 vocab=02ffbe28
-/
theorem two_im_eq (z : ℂ) : (((2 * z.im : ℝ)) : ℂ) = -Complex.I * (z - conj z) :=
  Complex.ext (by simp [two_mul]) (by simp)

/--
@isnad1 id=eq.0h2v.s5.b8f24c4eba5d from=translated src=- shape=89133ad3 vocab=9a2ef7f3
-/
theorem Bc_cpow_neg_add_one (w z : ℂ) : Bc z ^ (-(w + 1)) = Bc z ^ (-w - 1) := by
  congr 1; ring

/--
@isnad1 id=eq.0h5v.s7.b568938c61b9 from=translated src=- shape=24a309a3 vocab=06396976
-/
theorem GxEc_eq (a b : ℕ) (w ζ z : ℂ) : Gx a b w z * Ec ζ z =
    (a : ℂ) * F (a - 1) b w ζ z + (b : ℂ) * F a (b - 1) w ζ z
      - w * (F (a + 1) b (w + 1) ζ z + F a (b + 1) (w + 1) ζ z) := by
  have hre := two_re_eq z
  simp only [Gx, F, Bc_cpow_neg_add_one, pow_succ]
  linear_combination (-w * z ^ a * conj z ^ b * Bc z ^ (-w - 1) * Ec ζ z) * hre

/--
@isnad1 id=eq.0h5v.s7.f489fc2591c5 from=translated src=- shape=47db2402 vocab=61062eb9
-/
theorem GyEc_eq (a b : ℕ) (w ζ z : ℂ) : Gy a b w z * Ec ζ z =
    Complex.I * (a : ℂ) * F (a - 1) b w ζ z - Complex.I * (b : ℂ) * F a (b - 1) w ζ z
      + Complex.I * w * (F (a + 1) b (w + 1) ζ z - F a (b + 1) (w + 1) ζ z) := by
  have him := two_im_eq z
  simp only [Gy, F, Bc_cpow_neg_add_one, pow_succ]
  linear_combination (-w * z ^ a * conj z ^ b * Bc z ^ (-w - 1) * Ec ζ z) * him

/--
@isnad1 id=eq.0h5v.s7.1b40771a427c from=translated src=- shape=5dea1ce7 vocab=800d0d2f
-/
theorem comb_eq (a b : ℕ) (w ζ z : ℂ) : (Gx a b w z + Complex.I * Gy a b w z) * Ec ζ z =
    2 * (b : ℂ) * F a (b - 1) w ζ z - 2 * w * F (a + 1) b (w + 1) ζ z := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rw [add_mul, mul_assoc, GxEc_eq, GyEc_eq]
  linear_combination ((a : ℂ) * F (a - 1) b w ζ z - (b : ℂ) * F a (b - 1) w ζ z
    + w * (F (a + 1) b (w + 1) ζ z - F a (b + 1) (w + 1) ζ z)) * hI

/--
@isnad1 id=lt.1h3v.s6.8ebfb93a671d from=translated src=- shape=e0e493c4 vocab=7affd5db
-/
theorem thr_a_sub (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) :
    ((a - 1 + b : ℕ) : ℝ) / 2 + 1 < w.re := by
  have : ((a - 1 + b : ℕ) : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast (by omega : a - 1 + b ≤ a + b)
  linarith

/--
@isnad1 id=lt.1h3v.s6.273344d39716 from=translated src=- shape=0973fc3a vocab=7affd5db
-/
theorem thr_b_sub (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) :
    ((a + (b - 1) : ℕ) : ℝ) / 2 + 1 < w.re := by
  have : ((a + (b - 1) : ℕ) : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast (by omega : a + (b - 1) ≤ a + b)
  linarith

/--
@isnad1 id=lt.1h3v.s6.51d3683176ed from=translated src=- shape=c632b5b9 vocab=bc29241d
-/
theorem thr_a_add (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) :
    ((a + 1 + b : ℕ) : ℝ) / 2 + 1 < (w + 1).re := by
  simp only [Complex.add_re, Complex.one_re]
  push_cast at hw ⊢
  linarith

/--
@isnad1 id=lt.1h3v.s6.00831d6960e5 from=translated src=- shape=40dd461a vocab=bc29241d
-/
theorem thr_b_add (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) :
    ((a + (b + 1) : ℕ) : ℝ) / 2 + 1 < (w + 1).re := by
  simp only [Complex.add_re, Complex.one_re]
  push_cast at hw ⊢
  linarith

/--
@isnad1 id=integrab.1h4v.s6.a83a1c755e14 from=translated src=- shape=4d78049a vocab=350bab4c
-/
theorem integrable_GxEc (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) (ζ : ℂ) :
    Integrable (fun z => Gx a b w z * Ec ζ z) := by
  simp_rw [GxEc_eq]
  exact (((integrable_F (a - 1) b (thr_a_sub a b hw) ζ).const_mul _).add
    ((integrable_F a (b - 1) (thr_b_sub a b hw) ζ).const_mul _)).sub
    (((integrable_F (a + 1) b (thr_a_add a b hw) ζ).add (integrable_F a (b + 1) (thr_b_add a b hw) ζ)).const_mul _)

/--
@isnad1 id=integrab.1h4v.s6.cd55bf392715 from=translated src=- shape=4d78049a vocab=8710bc01
-/
theorem integrable_GyEc (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) (ζ : ℂ) :
    Integrable (fun z => Gy a b w z * Ec ζ z) := by
  simp_rw [GyEc_eq]
  exact (((integrable_F (a - 1) b (thr_a_sub a b hw) ζ).const_mul _).sub
    ((integrable_F a (b - 1) (thr_b_sub a b hw) ζ).const_mul _)).add
    (((integrable_F (a + 1) b (thr_a_add a b hw) ζ).sub (integrable_F a (b + 1) (thr_b_add a b hw) ζ)).const_mul _)

/--
@isnad1 id=le.0h6v.s7.29fec9270cd8 from=translated src=- shape=d9a22267 vocab=d80b4c3f
-/
theorem norm_F_mk_le (a b : ℕ) (w ζ : ℂ) (x y : ℝ) :
    ‖F a b w ζ ⟨x, y⟩‖ ≤ (1 + (x ^ 2 + y ^ 2)) ^ (-(2 * w.re - ((a + b : ℕ) : ℝ)) / 2) := by
  have h := norm_F_le a b (le_rfl : w.re ≤ w.re) ζ ⟨x, y⟩
  rwa [norm_sq_mk] at h

/--
@isnad1 id=and.1h5v.s7.b9a67e52935f from=translated src=- shape=04c28d1c vocab=d49e771e
-/
theorem tendsto_F_x (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) (ζ : ℂ) (y : ℝ) :
    Filter.Tendsto (fun x : ℝ => F a b w ζ ⟨x, y⟩) Filter.atBot (𝓝 0) ∧
    Filter.Tendsto (fun x : ℝ => F a b w ζ ⟨x, y⟩) Filter.atTop (𝓝 0) := by
  have hs : 0 < (2 * w.re - ((a + b : ℕ) : ℝ)) / 2 := by
    have h0 : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hr := tendsto_rpow_neg_atTop hs
  have e : ∀ x : ℝ, (1 + (x ^ 2 + y ^ 2)) ^ (-(2 * w.re - ((a + b : ℕ) : ℝ)) / 2)
      = (1 + (x ^ 2 + y ^ 2)) ^ (-((2 * w.re - ((a + b : ℕ) : ℝ)) / 2)) := fun x => by
    congr 1; ring
  have htop : Filter.Tendsto (fun x : ℝ => 1 + (x ^ 2 + y ^ 2)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ _
      (Filter.tendsto_atTop_add_const_right _ _ (Filter.tendsto_pow_atTop two_ne_zero))
  have hbot : Filter.Tendsto (fun x : ℝ => 1 + (x ^ 2 + y ^ 2)) Filter.atBot Filter.atTop := by
    have h := Filter.tendsto_atTop_add_const_left Filter.atBot (1 : ℝ)
      (Filter.tendsto_atTop_add_const_right Filter.atBot (y ^ 2)
        ((Filter.tendsto_pow_atTop two_ne_zero).comp Filter.tendsto_abs_atBot_atTop))
    refine h.congr' (Filter.Eventually.of_forall fun x => ?_)
    simp [sq_abs]
  constructor
  · refine squeeze_zero_norm (fun x => (norm_F_mk_le a b w ζ x y).trans (le_of_eq (e x))) ?_
    exact hr.comp hbot
  · refine squeeze_zero_norm (fun x => (norm_F_mk_le a b w ζ x y).trans (le_of_eq (e x))) ?_
    exact hr.comp htop

/--
@isnad1 id=and.1h5v.s7.463356615ed0 from=translated src=- shape=c7bd1b17 vocab=d49e771e
-/
theorem tendsto_F_y (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) (ζ : ℂ) (x : ℝ) :
    Filter.Tendsto (fun y : ℝ => F a b w ζ ⟨x, y⟩) Filter.atBot (𝓝 0) ∧
    Filter.Tendsto (fun y : ℝ => F a b w ζ ⟨x, y⟩) Filter.atTop (𝓝 0) := by
  have hs : 0 < (2 * w.re - ((a + b : ℕ) : ℝ)) / 2 := by
    have h0 : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hr := tendsto_rpow_neg_atTop hs
  have e : ∀ y : ℝ, (1 + (x ^ 2 + y ^ 2)) ^ (-(2 * w.re - ((a + b : ℕ) : ℝ)) / 2)
      = (1 + (x ^ 2 + y ^ 2)) ^ (-((2 * w.re - ((a + b : ℕ) : ℝ)) / 2)) := fun y => by
    congr 1; ring
  have htop : Filter.Tendsto (fun y : ℝ => 1 + (x ^ 2 + y ^ 2)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_left _ _
      (Filter.tendsto_atTop_add_const_left _ _ (Filter.tendsto_pow_atTop two_ne_zero))
  have hbot : Filter.Tendsto (fun y : ℝ => 1 + (x ^ 2 + y ^ 2)) Filter.atBot Filter.atTop := by
    have h := Filter.tendsto_atTop_add_const_left Filter.atBot (1 : ℝ)
      (Filter.tendsto_atTop_add_const_left Filter.atBot (x ^ 2)
        ((Filter.tendsto_pow_atTop two_ne_zero).comp Filter.tendsto_abs_atBot_atTop))
    refine h.congr' (Filter.Eventually.of_forall fun y => ?_)
    simp [sq_abs]
  constructor
  · refine squeeze_zero_norm (fun y => (norm_F_mk_le a b w ζ x y).trans (le_of_eq (e y))) ?_
    exact hr.comp hbot
  · refine squeeze_zero_norm (fun y => (norm_F_mk_le a b w ζ x y).trans (le_of_eq (e y))) ?_
    exact hr.comp htop

/--
@isnad1 id=measurep.0h0v.s6.3fe4208aad91 from=translated src=- shape=3387d7ec vocab=afdab508
-/
theorem mp_symm : MeasurePreserving (⇑Complex.measurableEquivRealProd.symm)
    (volume : Measure (ℝ × ℝ)) (volume : Measure ℂ) :=
  Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd

/--
@isnad1 id=eq.0h1v.s6.a7de53dc9f71 from=translated src=- shape=f303cc39 vocab=ab833c4d
-/
theorem integral_eq_prod (g : ℂ → ℂ) : ∫ z, g z = ∫ p : ℝ × ℝ, g ⟨p.1, p.2⟩ := by
  have h := mp_symm.integral_comp' g
  simp_rw [Complex.measurableEquivRealProd_symm_apply] at h
  exact h.symm

/--
@isnad1 id=iff.0h1v.s6.7cde29573f81 from=translated src=- shape=53404787 vocab=31e20364
-/
theorem integrable_prod_iff (g : ℂ → ℂ) :
    Integrable (fun p : ℝ × ℝ => g ⟨p.1, p.2⟩) ↔ Integrable g := by
  have h := mp_symm.integrable_comp_emb Complex.measurableEquivRealProd.symm.measurableEmbedding (g := g)
  have e : (g ∘ ⇑Complex.measurableEquivRealProd.symm) = fun p : ℝ × ℝ => g ⟨p.1, p.2⟩ := by
    funext p; simp [Complex.measurableEquivRealProd_symm_apply]
  rw [e] at h
  exact h

/--
@isnad1 id=eq.1h4v.s6.e3f1f6444316 from=translated src=- shape=d414eb3e vocab=562409b4
-/
theorem ibp_x (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) (ζ : ℂ) :
    cX ζ * jj a b w ζ = ∫ z, Gx a b w z * Ec ζ z := by
  have hF' : Integrable (fun z => F a b w ζ z * (-cX ζ)) := (integrable_F a b hw ζ).mul_const _
  have hGxE := integrable_GxEc a b hw ζ
  have hF'2 : Integrable (fun p : ℝ × ℝ => F a b w ζ ⟨p.1, p.2⟩ * (-cX ζ)) (volume.prod volume) :=
    (integrable_prod_iff (fun z => F a b w ζ z * (-cX ζ))).mpr hF'
  have hGxE2 : Integrable (fun p : ℝ × ℝ => Gx a b w ⟨p.1, p.2⟩ * Ec ζ ⟨p.1, p.2⟩) (volume.prod volume) :=
    (integrable_prod_iff (fun z => Gx a b w z * Ec ζ z)).mpr hGxE
  have hs1 := hF'2.prod_left_ae
  have hs2 := hGxE2.prod_left_ae
  have step1 : cX ζ * jj a b w ζ = -∫ z, F a b w ζ z * (-cX ζ) := by
    rw [integral_mul_const, jj]; ring
  have step2 : (∫ z, F a b w ζ z * (-cX ζ)) = ∫ y : ℝ, ∫ x : ℝ, F a b w ζ ⟨x, y⟩ * (-cX ζ) := by
    rw [integral_eq_prod (fun z => F a b w ζ z * (-cX ζ)), Measure.volume_eq_prod, integral_prod_symm _ hF'2]
  have step4 : (∫ z, Gx a b w z * Ec ζ z) = ∫ y : ℝ, ∫ x : ℝ, Gx a b w ⟨x, y⟩ * Ec ζ ⟨x, y⟩ := by
    rw [integral_eq_prod (fun z => Gx a b w z * Ec ζ z), Measure.volume_eq_prod, integral_prod_symm _ hGxE2]
  rw [step1, step2, step4, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hs1, hs2] with y hy1 hy2
  have i1 : Integrable ((fun x : ℝ => G a b w ⟨x, y⟩) * fun x : ℝ => Ec ζ ⟨x, y⟩ * (-cX ζ)) := by
    refine hy1.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, F, G]; ring
  have i2 : Integrable ((fun x : ℝ => Gx a b w ⟨x, y⟩) * fun x : ℝ => Ec ζ ⟨x, y⟩) := by
    refine hy2.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]
  have hlim := tendsto_F_x a b hw ζ y
  have elim : ((fun x : ℝ => G a b w ⟨x, y⟩) * fun x : ℝ => Ec ζ ⟨x, y⟩) = fun x => F a b w ζ ⟨x, y⟩ := by
    funext x; simp only [Pi.mul_apply, F, G]
  have ibp := integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => G a b w ⟨x, y⟩) (v := fun x : ℝ => Ec ζ ⟨x, y⟩)
    (u' := fun x : ℝ => Gx a b w ⟨x, y⟩) (v' := fun x : ℝ => Ec ζ ⟨x, y⟩ * (-cX ζ))
    (fun x _ => hasDerivAt_G_x a b w x y) (fun x _ => hasDerivAt_Ec_x ζ x y) i1 i2
    (by rw [elim]; exact hlim.1) (by rw [elim]; exact hlim.2)
  beta_reduce at ibp
  rw [sub_zero, zero_sub] at ibp
  have e3 : (∫ x : ℝ, F a b w ζ ⟨x, y⟩ * (-cX ζ)) = ∫ x : ℝ, G a b w ⟨x, y⟩ * (Ec ζ ⟨x, y⟩ * (-cX ζ)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [F, G]; ring
  rw [e3, ibp, neg_neg]

/--
@isnad1 id=eq.1h4v.s6.7eb0c43f7321 from=translated src=- shape=603358ab vocab=ea44b55b
-/
theorem ibp_y (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) (ζ : ℂ) :
    -cY ζ * jj a b w ζ = ∫ z, Gy a b w z * Ec ζ z := by
  have hF' : Integrable (fun z => F a b w ζ z * cY ζ) := (integrable_F a b hw ζ).mul_const _
  have hGyE := integrable_GyEc a b hw ζ
  have hF'2 : Integrable (fun p : ℝ × ℝ => F a b w ζ ⟨p.1, p.2⟩ * cY ζ) (volume.prod volume) :=
    (integrable_prod_iff (fun z => F a b w ζ z * cY ζ)).mpr hF'
  have hGyE2 : Integrable (fun p : ℝ × ℝ => Gy a b w ⟨p.1, p.2⟩ * Ec ζ ⟨p.1, p.2⟩) (volume.prod volume) :=
    (integrable_prod_iff (fun z => Gy a b w z * Ec ζ z)).mpr hGyE
  have hs1 := hF'2.prod_right_ae
  have hs2 := hGyE2.prod_right_ae
  have step1 : -cY ζ * jj a b w ζ = -∫ z, F a b w ζ z * cY ζ := by
    rw [integral_mul_const, jj]; ring
  have step2 : (∫ z, F a b w ζ z * cY ζ) = ∫ x : ℝ, ∫ y : ℝ, F a b w ζ ⟨x, y⟩ * cY ζ := by
    rw [integral_eq_prod (fun z => F a b w ζ z * cY ζ), Measure.volume_eq_prod, integral_prod _ hF'2]
  have step4 : (∫ z, Gy a b w z * Ec ζ z) = ∫ x : ℝ, ∫ y : ℝ, Gy a b w ⟨x, y⟩ * Ec ζ ⟨x, y⟩ := by
    rw [integral_eq_prod (fun z => Gy a b w z * Ec ζ z), Measure.volume_eq_prod, integral_prod _ hGyE2]
  rw [step1, step2, step4, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hs1, hs2] with x hx1 hx2
  have i1 : Integrable ((fun y : ℝ => G a b w ⟨x, y⟩) * fun y : ℝ => Ec ζ ⟨x, y⟩ * cY ζ) := by
    refine hx1.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.mul_apply, F, G]; ring
  have i2 : Integrable ((fun y : ℝ => Gy a b w ⟨x, y⟩) * fun y : ℝ => Ec ζ ⟨x, y⟩) := by
    refine hx2.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.mul_apply]
  have hlim := tendsto_F_y a b hw ζ x
  have elim : ((fun y : ℝ => G a b w ⟨x, y⟩) * fun y : ℝ => Ec ζ ⟨x, y⟩) = fun y => F a b w ζ ⟨x, y⟩ := by
    funext y; simp only [Pi.mul_apply, F, G]
  have ibp := integral_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => G a b w ⟨x, y⟩) (v := fun y : ℝ => Ec ζ ⟨x, y⟩)
    (u' := fun y : ℝ => Gy a b w ⟨x, y⟩) (v' := fun y : ℝ => Ec ζ ⟨x, y⟩ * cY ζ)
    (fun y _ => hasDerivAt_G_y a b w x y) (fun y _ => hasDerivAt_Ec_y ζ x y) i1 i2
    (by rw [elim]; exact hlim.1) (by rw [elim]; exact hlim.2)
  beta_reduce at ibp
  rw [sub_zero, zero_sub] at ibp
  have e3 : (∫ y : ℝ, F a b w ζ ⟨x, y⟩ * cY ζ) = ∫ y : ℝ, G a b w ⟨x, y⟩ * (Ec ζ ⟨x, y⟩ * cY ζ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [F, G]; ring
  rw [e3, ibp, neg_neg]

/--
@isnad1 id=eq.0h1v.s5.f9da18b96400 from=translated src=- shape=c742f5ea vocab=2bccb050
-/
theorem conj_eq_re_sub_im (ζ : ℂ) : conj ζ = (ζ.re : ℂ) - (ζ.im : ℂ) * Complex.I :=
  Complex.ext (by simp) (by simp)

/--
@isnad1 id=eq.0h1v.s5.7564ea704cd0 from=translated src=- shape=cfe93f19 vocab=abf71ffc
-/
theorem two_cZ (ζ : ℂ) : 2 * cZ ζ = cX ζ + Complex.I * (-cY ζ) := by
  simp only [cZ, cX, cY]
  rw [show (starRingEnd ℂ) ζ = conj ζ from rfl, conj_eq_re_sub_im]
  push_cast
  ring

/--
@isnad1 id=eq.1h4v.s7.0fa814fc46de from=translated src=- shape=bc2b35a3 vocab=f76164aa
-/
theorem recur (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) (ζ : ℂ) :
    cZ ζ * jj a b w ζ = (b : ℂ) * jj a (b - 1) w ζ - w * jj (a + 1) b (w + 1) ζ := by
  have hGx := integrable_GxEc a b hw ζ
  have hGy := integrable_GyEc a b hw ζ
  have h1 : 2 * (cZ ζ * jj a b w ζ) = (∫ z, Gx a b w z * Ec ζ z) + Complex.I * ∫ z, Gy a b w z * Ec ζ z := by
    rw [← ibp_x a b hw ζ, ← ibp_y a b hw ζ, ← mul_assoc, two_cZ]; ring
  have h2 : (∫ z, Gx a b w z * Ec ζ z) + Complex.I * ∫ z, Gy a b w z * Ec ζ z
      = ∫ z, (Gx a b w z + Complex.I * Gy a b w z) * Ec ζ z := by
    rw [← integral_const_mul, ← integral_add hGx (hGy.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    ring
  have h3 : (∫ z, (Gx a b w z + Complex.I * Gy a b w z) * Ec ζ z)
      = 2 * ((b : ℂ) * jj a (b - 1) w ζ - w * jj (a + 1) b (w + 1) ζ) := by
    simp_rw [comb_eq]
    have i1 : Integrable (fun z => 2 * (b : ℂ) * F a (b - 1) w ζ z) :=
      (integrable_F a (b - 1) (thr_b_sub a b hw) ζ).const_mul _
    have i2 : Integrable (fun z => 2 * w * F (a + 1) b (w + 1) ζ z) :=
      (integrable_F (a + 1) b (thr_a_add a b hw) ζ).const_mul _
    rw [integral_sub i1 i2, integral_const_mul, integral_const_mul, jj, jj]
    ring
  have h := h1.trans (h2.trans h3)
  linear_combination (2 : ℂ)⁻¹ * h

/--
@isnad1 id=and.0h2v.s8.3ccdf41974e9 from=translated src=- shape=ebbfd3d8 vocab=d391863b
-/
theorem base (a b : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ => jj a b p.1 p.2) ({w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} ×ˢ Set.univ) ∧
    (∀ ζ : ℂ, DifferentiableOn ℂ (fun w : ℂ => jj a b w ζ) {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re}) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ ζ : ℂ, ‖jj a b w ζ‖ ≤ C * (1 + ‖ζ‖) ^ (-(N : ℝ))) :=
  AutomorphicForm.ComplexIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral a b

def H (n a b : ℕ) : Set ℂ := {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 - (n : ℝ) / 2 < w.re}

/--
@isnad1 id=isopen.0h3v.s4.ccfd1d644a09 from=translated src=- shape=0e1038f4 vocab=04a65ada
-/
theorem isOpen_H (n a b : ℕ) : IsOpen (H n a b) := isOpen_lt continuous_const Complex.continuous_re

/--
@isnad1 id=eq.0h2v.s6.de561429bdb0 from=translated src=- shape=bca4b623 vocab=a421a074
-/
theorem H_zero (a b : ℕ) : H 0 a b = {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} := by
  ext w; simp [H]

/--
@isnad1 id=mem.1h4v.s6.7f13c7f83ce1 from=translated src=- shape=c4bd9ae6 vocab=ed44d9f7
-/
theorem add_one_mem_H {n a b : ℕ} {w : ℂ} (hw : w ∈ H (n + 1) a b) : w + 1 ∈ H n (a + 1) b := by
  simp only [H, mem_ofPred_eq, Complex.add_re, Complex.one_re] at hw ⊢
  push_cast at hw ⊢
  linarith

/--
@isnad1 id=mem.1h4v.s5.1dabbd33c4ef from=translated src=- shape=2099ef36 vocab=ed44d9f7
-/
theorem pred_mem_H {n a b : ℕ} {w : ℂ} (hw : w ∈ H (n + 1) a (b + 1)) : w ∈ H n a b := by
  simp only [H, mem_ofPred_eq] at hw ⊢
  push_cast at hw ⊢
  linarith

/--
@isnad1 id=le.1h4v.s4.0ac70f969774 from=translated src=- shape=5ca0126e vocab=938ea57e
-/
theorem H_mono {m n : ℕ} (h : m ≤ n) (a b : ℕ) : H m a b ⊆ H n a b := by
  intro w hw
  simp only [H, mem_ofPred_eq] at hw ⊢
  have : (m : ℝ) ≤ n := by exact_mod_cast h
  linarith

def J : ℕ → ℕ → ℕ → ℂ → ℂ → ℂ
  | 0, a, b, w, ζ => jj a b w ζ
  | n + 1, a, b, w, ζ => (cZ ζ)⁻¹ * ((b : ℂ) * J n a (b - 1) w ζ - w * J n (a + 1) b (w + 1) ζ)

/--
@isnad1 id=eq.0h4v.s4.7acb8ae09b7e from=translated src=- shape=8c981ba2 vocab=1a5319fd
-/
theorem J_zero (a b : ℕ) (w ζ : ℂ) : J 0 a b w ζ = jj a b w ζ := rfl

/--
@isnad1 id=eq.0h5v.s6.bf0a539aa2a0 from=translated src=- shape=096eb008 vocab=d30fa8ce
-/
theorem J_succ (n a b : ℕ) (w ζ : ℂ) :
    J (n + 1) a b w ζ = (cZ ζ)⁻¹ * ((b : ℂ) * J n a (b - 1) w ζ - w * J n (a + 1) b (w + 1) ζ) := rfl

/--
@isnad1 id=eq.2h5v.s5.f697f6fae487 from=translated src=- shape=21a3eaad vocab=dbb436f3
-/
theorem J_succ_eq (n : ℕ) : ∀ (a b : ℕ) (w ζ : ℂ), w ∈ H n a b → ζ ≠ 0 →
    J (n + 1) a b w ζ = J n a b w ζ := by
  induction n with
  | zero =>
    intro a b w ζ hw hζ
    have hw' : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re := by rw [H_zero] at hw; exact hw
    rw [J_succ, J_zero, J_zero, J_zero, ← recur a b hw' ζ, ← mul_assoc, inv_mul_cancel₀ (cZ_ne_zero hζ), one_mul]
  | succ n ih =>
    intro a b w ζ hw hζ
    rw [J_succ (n + 1) a b w ζ, J_succ n a b w ζ]
    congr 1
    cases b with
    | zero =>
      rw [ih (a + 1) 0 (w + 1) ζ (add_one_mem_H hw) hζ]
      simp only [Nat.cast_zero, zero_mul]
    | succ b' =>
      rw [Nat.add_sub_cancel] at ⊢
      rw [ih a b' w ζ (pred_mem_H hw) hζ, ih (a + 1) (b' + 1) (w + 1) ζ (add_one_mem_H hw) hζ]

/--
@isnad1 id=eq.3h6v.s5.4bea00650dda from=translated src=- shape=6d6cd917 vocab=687557db
-/
theorem J_eq_of_le {m n : ℕ} (h : m ≤ n) (a b : ℕ) (w ζ : ℂ) (hw : w ∈ H m a b) (hζ : ζ ≠ 0) :
    J n a b w ζ = J m a b w ζ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [show m + (d + 1) = (m + d) + 1 from by ring, J_succ_eq (m + d) a b w ζ (H_mono (Nat.le_add_right m d) a b hw) hζ]
    exact ih (Nat.le_add_right m d)

/--
@isnad1 id=differen.1h4v.s6.1d9d77245a9d from=translated src=- shape=3ea9f3bb vocab=1eeeffd7
-/
theorem J_differentiableOn (n : ℕ) : ∀ (a b : ℕ) (ζ : ℂ), ζ ≠ 0 →
    DifferentiableOn ℂ (fun w => J n a b w ζ) (H n a b) := by
  induction n with
  | zero => intro a b ζ _; rw [H_zero]; exact (base a b).2.1 ζ
  | succ n ih =>
    intro a b ζ hζ
    have h1 : DifferentiableOn ℂ (fun w => (b : ℂ) * J n a (b - 1) w ζ) (H (n + 1) a b) := by
      cases b with
      | zero =>
        refine (differentiableOn_const (0 : ℂ)).congr (fun w _ => ?_)
        simp only [Nat.cast_zero, zero_mul]
      | succ b' =>
        rw [Nat.add_sub_cancel]
        exact ((ih a b' ζ hζ).mono (fun w hw => pred_mem_H hw)).const_mul _
    have h2 : DifferentiableOn ℂ (fun w => J n (a + 1) b (w + 1) ζ) (H (n + 1) a b) :=
      (ih (a + 1) b ζ hζ).comp ((differentiable_id.add_const (1 : ℂ)).differentiableOn) (fun w hw => add_one_mem_H hw)
    show DifferentiableOn ℂ (fun w => (cZ ζ)⁻¹ * ((b : ℂ) * J n a (b - 1) w ζ - w * J n (a + 1) b (w + 1) ζ))
      (H (n + 1) a b)
    exact (h1.sub (differentiableOn_id.mul h2)).const_mul _

/--
@isnad1 id=le.1h1v.s5.beea6a6659b0 from=translated src=- shape=82284ddd vocab=c108f400
-/
theorem norm_inv_cZ_le {ζ : ℂ} (hζ : ζ ≠ 0) : ‖(cZ ζ)⁻¹‖ ≤ max 1 ‖ζ‖⁻¹ := by
  rw [norm_inv, norm_cZ]
  refine le_trans ?_ (le_max_right _ _)
  have hζ' : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  rw [inv_le_inv₀ (by positivity) hζ']
  have : (1 : ℝ) ≤ 2 * Real.pi := by have := Real.two_le_pi; linarith
  nlinarith

def nw (a b : ℕ) (w : ℂ) : ℕ := ⌈((a + b : ℕ) : ℝ) + 2 - 2 * w.re⌉₊ + 1

def Jg (a b : ℕ) (w ζ : ℂ) : ℂ := J (nw a b w) a b w ζ

/--
@isnad1 id=le.1h1v.s5.9c1382ee1ce4 from=translated src=- shape=49c88383 vocab=87e942d5
-/
theorem norm_inv_cZ_le'' {ζ : ℂ} (hζ1 : 1 ≤ ‖ζ‖) : ‖(cZ ζ)⁻¹‖ ≤ 2 * (1 + ‖ζ‖)⁻¹ := by
  rw [norm_inv, norm_cZ]
  have hz : 0 < ‖ζ‖ := by linarith
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by have := Real.two_le_pi; linarith
  have h1 : (2 * Real.pi * ‖ζ‖)⁻¹ ≤ ‖ζ‖⁻¹ := by
    rw [inv_le_inv₀ (by positivity) hz]; nlinarith
  refine h1.trans ?_
  rw [inv_le_iff_one_le_mul₀ hz]
  have hpos : (0 : ℝ) < 1 + ‖ζ‖ := by positivity
  rw [show 2 * (1 + ‖ζ‖)⁻¹ * ‖ζ‖ = (2 * ‖ζ‖) / (1 + ‖ζ‖) by ring, le_div_iff₀ hpos]
  linarith

/--
@isnad1 id=le.2h5v.s7.61e5683fa9c0 from=translated src=- shape=e6801c97 vocab=ebf7b9d4
-/
theorem jj_norm_le (a b : ℕ) {σ : ℝ} (hσ : ((a + b : ℕ) : ℝ) / 2 + 1 < σ) {w : ℂ} (hw : σ ≤ w.re) (ζ : ℂ) :
    ‖jj a b w ζ‖ ≤ ∫ z : ℂ, (1 + ‖z‖ ^ 2) ^ (-(2 * σ - ((a + b : ℕ) : ℝ)) / 2) := by
  unfold jj
  refine (norm_integral_le_integral_norm _).trans ?_
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (integrable_bracket a b hσ)
    (Filter.Eventually.of_forall fun z => norm_F_le a b hw ζ z)

/--
@isnad1 id=le.2h3v.s6.315c532f0963 from=translated src=- shape=ade7fa17 vocab=f0535296
-/
theorem norm_le_of_strip {σ₁ σ₂ : ℝ} {w : ℂ} (hw1 : σ₁ ≤ w.re) (hw2 : w.re ≤ σ₂) :
    ‖w‖ ≤ (max |σ₁| |σ₂| + 1) * (1 + |w.im|) := by
  have h1 : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
  have h2 : |w.re| ≤ max |σ₁| |σ₂| := by
    rw [abs_le]; constructor
    · have := neg_abs_le σ₁; have := le_max_left |σ₁| |σ₂|; linarith
    · have := le_abs_self σ₂; have := le_max_right |σ₁| |σ₂|; linarith
  have h3 : 0 ≤ max |σ₁| |σ₂| := le_trans (abs_nonneg _) (le_max_left _ _)
  nlinarith [abs_nonneg w.im]

/--
@isnad1 id=eq.1h2v.s6.55fdb4754fe4 from=translated src=- shape=a7bc1c81 vocab=25daf03d
-/
theorem rpow_neg_succ (r : ℝ) (hr : 0 ≤ r) (N : ℕ) :
    (1 + r) ^ (-((N + 1 : ℕ) : ℝ)) = (1 + r) ^ (-(N : ℝ)) * (1 + r)⁻¹ := by
  have h : (0 : ℝ) < 1 + r := by positivity
  rw [show (-((N + 1 : ℕ) : ℝ)) = -(N : ℝ) + (-1) by push_cast; ring, Real.rpow_add h, Real.rpow_neg_one]

/--
@isnad1 id=le.2h2v.s6.c4b65b3bac7a from=translated src=- shape=f093f34e vocab=225c5d83
-/
theorem rpow_neg_nat_ge {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (N : ℕ) : (2 : ℝ)⁻¹ ^ N ≤ (1 + r) ^ (-(N : ℝ)) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← inv_pow]
  exact pow_le_pow_left₀ (by norm_num) (by rw [inv_le_inv₀ (by norm_num) (by positivity)]; linarith) N

/--
@isnad1 id=ex.1h5v.s7.987a73bb86d6 from=translated src=- shape=b8df6a6c vocab=5abb38b7
-/
theorem strip_base (N : ℕ) : ∀ (a b : ℕ) (σ₁ σ₂ : ℝ), ((a + b : ℕ) : ℝ) / 2 + 1 < σ₁ → ∃ C : ℝ, 0 < C ∧
    ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ∀ ζ : ℂ, ζ ≠ 0 →
      ‖jj a b w ζ‖ ≤ C * (1 + |w.im|) ^ N * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
  induction N with
  | zero =>
    intro a b σ₁ σ₂ hσ₁
    have hI : 0 ≤ ∫ z : ℂ, (1 + ‖z‖ ^ 2) ^ (-(2 * σ₁ - ((a + b : ℕ) : ℝ)) / 2) := integral_nonneg fun z => by positivity
    refine ⟨(∫ z : ℂ, (1 + ‖z‖ ^ 2) ^ (-(2 * σ₁ - ((a + b : ℕ) : ℝ)) / 2)) + 1, by linarith, fun w hw1 _ ζ _ => ?_⟩
    rw [pow_zero, mul_one, Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one]
    exact (jj_norm_le a b hσ₁ hw1 ζ).trans (by linarith)
  | succ N ih =>
    intro a b σ₁ σ₂ hσ₁

    have hT1 : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ∀ ζ : ℂ, ζ ≠ 0 →
        ‖(b : ℂ) * jj a (b - 1) w ζ‖ ≤ C₁ * (((1 + |w.im|)) ^ N * (1 + ‖ζ‖) ^ (-(N : ℝ))) := by
      cases b with
      | zero =>
        refine ⟨1, one_pos, fun w _ _ ζ _ => ?_⟩
        simp only [Nat.cast_zero, zero_mul, norm_zero, one_mul]
        positivity
      | succ b' =>
        obtain ⟨C₁, hC₁, hb₁⟩ := ih a b' σ₁ σ₂ (by push_cast at hσ₁ ⊢; linarith)
        refine ⟨((b' + 1 : ℕ) : ℝ) * C₁, by positivity, fun w hw1 hw2 ζ hζ => ?_⟩
        rw [Nat.add_sub_cancel, norm_mul, Complex.norm_natCast, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := hb₁ w hw1 hw2 ζ hζ
        rw [mul_assoc] at this
        exact this
    obtain ⟨C₁, hC₁, hb₁⟩ := hT1
    obtain ⟨C₂, hC₂, hb₂⟩ := ih (a + 1) b (σ₁ + 1) (σ₂ + 1) (by push_cast at hσ₁ ⊢; linarith)
    set R : ℝ := max |σ₁| |σ₂| + 1 with hR
    have hR0 : 0 ≤ R := by have : 0 ≤ max |σ₁| |σ₂| := le_trans (abs_nonneg _) (le_max_left _ _); linarith
    set I₀ : ℝ := ∫ z : ℂ, (1 + ‖z‖ ^ 2) ^ (-(2 * σ₁ - ((a + b : ℕ) : ℝ)) / 2) with hI₀
    have hI₀0 : 0 ≤ I₀ := integral_nonneg fun z => by positivity
    refine ⟨2 * (C₁ + R * C₂ + 1) + (I₀ + 1) * 2 ^ (N + 1), by positivity, fun w hw1 hw2 ζ hζ => ?_⟩
    set P : ℝ := 1 + |w.im| with hP
    set D : ℝ := (1 + ‖ζ‖) ^ (-(N : ℝ)) with hD
    have hP1 : 1 ≤ P := by rw [hP]; linarith [abs_nonneg w.im]
    have hD0 : 0 ≤ D := Real.rpow_nonneg (by positivity) _
    have hPD : 0 ≤ P ^ N * D := by positivity
    have hDs : (1 + ‖ζ‖) ^ (-((N + 1 : ℕ) : ℝ)) = D * (1 + ‖ζ‖)⁻¹ := rpow_neg_succ _ (norm_nonneg ζ) N
    by_cases hz1 : 1 ≤ ‖ζ‖
    · have him1 : (w + 1).im = w.im := by simp
      have e1 : ‖(b : ℂ) * jj a (b - 1) w ζ‖ ≤ C₁ * (P ^ N * D) := hb₁ w hw1 hw2 ζ hζ
      have e2 : ‖jj (a + 1) b (w + 1) ζ‖ ≤ C₂ * (P ^ N * D) := by
        have := hb₂ (w + 1) (by simp; linarith) (by simp; linarith) ζ hζ
        rw [him1] at this; rw [mul_assoc] at this; exact this
      have hw' : ‖w‖ ≤ R * P := norm_le_of_strip hw1 hw2
      have hrec := recur a b (lt_of_lt_of_le hσ₁ hw1) ζ
      have hjj : jj a b w ζ = (cZ ζ)⁻¹ * ((b : ℂ) * jj a (b - 1) w ζ - w * jj (a + 1) b (w + 1) ζ) := by
        rw [← hrec, ← mul_assoc, inv_mul_cancel₀ (cZ_ne_zero hζ), one_mul]
      have step : ‖(b : ℂ) * jj a (b - 1) w ζ - w * jj (a + 1) b (w + 1) ζ‖
          ≤ (C₁ + R * C₂ + 1) * (P * (P ^ N * D)) := by
        have hsub := norm_sub_le ((b : ℂ) * jj a (b - 1) w ζ) (w * jj (a + 1) b (w + 1) ζ)
        have hwC : ‖w * jj (a + 1) b (w + 1) ζ‖ ≤ (R * P) * (C₂ * (P ^ N * D)) := by
          rw [norm_mul]; exact mul_le_mul hw' e2 (norm_nonneg _) (by positivity)
        have e1' : ‖(b : ℂ) * jj a (b - 1) w ζ‖ ≤ C₁ * (P * (P ^ N * D)) :=
          e1.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hPD hP1) hC₁.le)
        have hPX : 0 ≤ P * (P ^ N * D) := by positivity
        have e3 : (R * P) * (C₂ * (P ^ N * D)) = R * C₂ * (P * (P ^ N * D)) := by ring
        rw [e3] at hwC
        nlinarith
      rw [hjj, norm_mul, hDs]
      calc ‖(cZ ζ)⁻¹‖ * ‖(b : ℂ) * jj a (b - 1) w ζ - w * jj (a + 1) b (w + 1) ζ‖
          ≤ (2 * (1 + ‖ζ‖)⁻¹) * ((C₁ + R * C₂ + 1) * (P * (P ^ N * D))) :=
            mul_le_mul (norm_inv_cZ_le'' hz1) step (norm_nonneg _) (by positivity)
        _ = 2 * (C₁ + R * C₂ + 1) * P ^ (N + 1) * (D * (1 + ‖ζ‖)⁻¹) := by rw [pow_succ]; ring
        _ ≤ (2 * (C₁ + R * C₂ + 1) + (I₀ + 1) * 2 ^ (N + 1)) * P ^ (N + 1) * (D * (1 + ‖ζ‖)⁻¹) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            linarith [show (0:ℝ) ≤ (I₀ + 1) * 2 ^ (N + 1) by positivity]
    · rw [not_le] at hz1
      have htriv : ‖jj a b w ζ‖ ≤ I₀ := jj_norm_le a b hσ₁ hw1 ζ
      have hlow : (2 : ℝ)⁻¹ ^ (N + 1) ≤ (1 + ‖ζ‖) ^ (-((N + 1 : ℕ) : ℝ)) := rpow_neg_nat_ge (norm_nonneg ζ) hz1 (N + 1)
      have hPN : 1 ≤ P ^ (N + 1) := one_le_pow₀ hP1
      have h2 : (2 : ℝ) ^ (N + 1) * (2 : ℝ)⁻¹ ^ (N + 1) = 1 := by rw [← mul_pow]; norm_num
      calc ‖jj a b w ζ‖ ≤ I₀ + 1 := by linarith
        _ = ((I₀ + 1) * 2 ^ (N + 1)) * 1 * (2 : ℝ)⁻¹ ^ (N + 1) := by rw [mul_one, mul_assoc, h2, mul_one]
        _ ≤ ((I₀ + 1) * 2 ^ (N + 1)) * P ^ (N + 1) * (1 + ‖ζ‖) ^ (-((N + 1 : ℕ) : ℝ)) := by gcongr
        _ ≤ (2 * (C₁ + R * C₂ + 1) + (I₀ + 1) * 2 ^ (N + 1)) * P ^ (N + 1) * (1 + ‖ζ‖) ^ (-((N + 1 : ℕ) : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            linarith [show (0:ℝ) ≤ 2 * (C₁ + R * C₂ + 1) by positivity]

/--
@isnad1 id=ex.1h6v.s8.3eb6e62a9b8f from=translated src=- shape=ab1d1f50 vocab=004f370b
-/
theorem strip_tower (n : ℕ) : ∀ (a b : ℕ) (σ₁ σ₂ : ℝ), ((a + b : ℕ) : ℝ) / 2 + 1 - (n : ℝ) / 2 < σ₁ → ∀ N : ℕ,
    ∃ (A : ℕ) (C : ℝ), 0 < C ∧
    ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ∀ ζ : ℂ, ζ ≠ 0 →
      ‖J n a b w ζ‖ ≤ C * (1 + |w.im|) ^ A * (max 1 ‖ζ‖⁻¹) ^ n * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
  induction n with
  | zero =>
    intro a b σ₁ σ₂ hσ N
    obtain ⟨C, hC, hb⟩ := strip_base N a b σ₁ σ₂ (by simpa using hσ)
    exact ⟨N, C, hC, fun w hw1 hw2 ζ hζ => by rw [J_zero, pow_zero, mul_one]; exact hb w hw1 hw2 ζ hζ⟩
  | succ n ih =>
    intro a b σ₁ σ₂ hσ N
    have hT1 : ∃ (A₁ : ℕ) (C₁ : ℝ), 0 < C₁ ∧ ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ → ∀ ζ : ℂ, ζ ≠ 0 →
        ‖(b : ℂ) * J n a (b - 1) w ζ‖ ≤ C₁ * (1 + |w.im|) ^ A₁ * (max 1 ‖ζ‖⁻¹) ^ n * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
      cases b with
      | zero =>
        refine ⟨0, 1, one_pos, fun w _ _ ζ _ => ?_⟩
        simp only [Nat.cast_zero, zero_mul, norm_zero, pow_zero, mul_one, one_mul]
        positivity
      | succ b' =>
        obtain ⟨A₁, C₁, hC₁, hb₁⟩ := ih a b' σ₁ σ₂ (by push_cast at hσ ⊢; linarith) N
        refine ⟨A₁, ((b' + 1 : ℕ) : ℝ) * C₁, by positivity, fun w hw1 hw2 ζ hζ => ?_⟩
        rw [Nat.add_sub_cancel, norm_mul, Complex.norm_natCast, mul_assoc, mul_assoc, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := hb₁ w hw1 hw2 ζ hζ
        rw [mul_assoc, mul_assoc] at this
        exact this
    obtain ⟨A₁, C₁, hC₁, hb₁⟩ := hT1
    obtain ⟨A₂, C₂, hC₂, hb₂⟩ := ih (a + 1) b (σ₁ + 1) (σ₂ + 1) (by push_cast at hσ ⊢; linarith) N
    set R : ℝ := max |σ₁| |σ₂| + 1 with hR
    have hR0 : 0 ≤ R := by have : 0 ≤ max |σ₁| |σ₂| := le_trans (abs_nonneg _) (le_max_left _ _); linarith
    set A : ℕ := A₁ + A₂ with hA
    refine ⟨A + 1, C₁ + R * C₂ + 1, by positivity, fun w hw1 hw2 ζ hζ => ?_⟩
    set P : ℝ := 1 + |w.im| with hP
    set M : ℝ := max 1 ‖ζ‖⁻¹ with hM
    set D : ℝ := (1 + ‖ζ‖) ^ (-(N : ℝ)) with hD
    have hP1 : 1 ≤ P := by rw [hP]; linarith [abs_nonneg w.im]
    have hM1 : 1 ≤ M := le_max_left _ _
    have hD0 : 0 ≤ D := Real.rpow_nonneg (by positivity) _
    have hX : 0 ≤ P ^ A * M ^ n * D := by positivity
    have him1 : (w + 1).im = w.im := by simp
    have e1 : ‖(b : ℂ) * J n a (b - 1) w ζ‖ ≤ C₁ * (P ^ A * M ^ n * D) := by
      refine (hb₁ w hw1 hw2 ζ hζ).trans ?_
      rw [mul_assoc, mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hC₁.le
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP1 (by rw [hA]; omega)) (by positivity)
    have e2 : ‖J n (a + 1) b (w + 1) ζ‖ ≤ C₂ * (P ^ A * M ^ n * D) := by
      have h := hb₂ (w + 1) (by simp; linarith) (by simp; linarith) ζ hζ
      rw [him1] at h
      refine h.trans ?_
      rw [mul_assoc, mul_assoc, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hC₂.le
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hP1 (by rw [hA]; omega)) (by positivity)
    have hw' : ‖w‖ ≤ R * P := norm_le_of_strip hw1 hw2
    rw [J_succ, norm_mul]
    have step : ‖(b : ℂ) * J n a (b - 1) w ζ - w * J n (a + 1) b (w + 1) ζ‖
        ≤ (C₁ + R * C₂ + 1) * (P * (P ^ A * M ^ n * D)) := by
      have hsub := norm_sub_le ((b : ℂ) * J n a (b - 1) w ζ) (w * J n (a + 1) b (w + 1) ζ)
      have hwC : ‖w * J n (a + 1) b (w + 1) ζ‖ ≤ (R * P) * (C₂ * (P ^ A * M ^ n * D)) := by
        rw [norm_mul]; exact mul_le_mul hw' e2 (norm_nonneg _) (by positivity)
      have e1' : ‖(b : ℂ) * J n a (b - 1) w ζ‖ ≤ C₁ * (P * (P ^ A * M ^ n * D)) :=
        e1.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hX hP1) hC₁.le)
      have hPX : 0 ≤ P * (P ^ A * M ^ n * D) := by positivity
      have e3 : (R * P) * (C₂ * (P ^ A * M ^ n * D)) = R * C₂ * (P * (P ^ A * M ^ n * D)) := by ring
      rw [e3] at hwC
      nlinarith
    calc ‖(cZ ζ)⁻¹‖ * ‖(b : ℂ) * J n a (b - 1) w ζ - w * J n (a + 1) b (w + 1) ζ‖
        ≤ M * ((C₁ + R * C₂ + 1) * (P * (P ^ A * M ^ n * D))) :=
          mul_le_mul (norm_inv_cZ_le hζ) step (norm_nonneg _) (le_trans zero_le_one hM1)
      _ = (C₁ + R * C₂ + 1) * P ^ (A + 1) * M ^ (n + 1) * D := by rw [pow_succ, pow_succ]; ring

end Ws31.ArchC

/--
@isnad1 id=other.0h4v.s9.5c8d80fb78fe from=translated src=- shape=0b1eadf9 vocab=d9337242
-/
theorem solution
    (a b : ℕ) (σ₁ σ₂ : ℝ) :
    let j : ℂ → ℂ → ℂ := fun w ζ => ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))
    ∃ A₀ : ℕ, ∀ N : ℕ, ∃ (C : ℝ) (A : ℕ), 0 < C ∧
      ∀ (ζ : ℂ), ζ ≠ 0 → ∀ (J : ℂ → ℂ), Differentiable ℂ J →
        (∀ w : ℂ, ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → J w = j w ζ) →
        ∀ w : ℂ, σ₁ ≤ w.re → w.re ≤ σ₂ →
          ‖J w‖ ≤ C * (1 + |w.im|) ^ A * (max 1 ‖ζ‖⁻¹) ^ A₀ * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
  intro j
  have hj : j = fun w ζ => Ws31.ArchC.jj a b w ζ := rfl
  set n : ℕ := ⌈((a + b : ℕ) : ℝ) + 2 - 2 * σ₁⌉₊ + 1 with hn
  have hσn : ((a + b : ℕ) : ℝ) / 2 + 1 - (n : ℝ) / 2 < σ₁ := by
    rw [hn]; have := Nat.le_ceil (((a + b : ℕ) : ℝ) + 2 - 2 * σ₁); push_cast at this ⊢; linarith
  refine ⟨n, fun N => ?_⟩
  obtain ⟨A, C, hC, hb⟩ := Ws31.ArchC.strip_tower n a b σ₁ σ₂ hσn N
  refine ⟨C, A, hC, fun ζ hζ Jf hJd hJeq w hw1 hw2 => ?_⟩
  have hwH : w ∈ Ws31.ArchC.H n a b := by
    show ((a + b : ℕ) : ℝ) / 2 + 1 - (n : ℝ) / 2 < w.re; exact lt_of_lt_of_le hσn hw1
  have hU : IsPreconnected (Ws31.ArchC.H n a b) := (convex_halfSpace_re_gt _).isPreconnected
  set z₀ : ℂ := ((((a + b : ℕ) : ℝ) / 2 + 2 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = ((a + b : ℕ) : ℝ) / 2 + 2 := by rw [hz₀, Complex.ofReal_re]
  have h1H : z₀ ∈ Ws31.ArchC.H n a b := by
    show ((a + b : ℕ) : ℝ) / 2 + 1 - (n : ℝ) / 2 < z₀.re
    rw [hz₀re]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hfan : AnalyticOnNhd ℂ Jf (Ws31.ArchC.H n a b) := (hJd.differentiableOn).analyticOnNhd (Ws31.ArchC.isOpen_H n a b)
  have hgan : AnalyticOnNhd ℂ (fun w => Ws31.ArchC.J n a b w ζ) (Ws31.ArchC.H n a b) :=
    (Ws31.ArchC.J_differentiableOn n a b ζ hζ).analyticOnNhd (Ws31.ArchC.isOpen_H n a b)
  have heq : Jf =ᶠ[nhds z₀] (fun w => Ws31.ArchC.J n a b w ζ) := by
    have hmem : {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} ∈ nhds z₀ :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by show _ < z₀.re; rw [hz₀re]; linarith)
    refine Filter.eventually_of_mem hmem fun w hw => ?_
    have hw0 : w ∈ Ws31.ArchC.H 0 a b := by rw [Ws31.ArchC.H_zero]; exact hw
    rw [hJeq w hw, hj]
    show Ws31.ArchC.jj a b w ζ = Ws31.ArchC.J n a b w ζ
    rw [Ws31.ArchC.J_eq_of_le (Nat.zero_le n) a b w ζ hw0 hζ, Ws31.ArchC.J_zero]
  have key : Jf w = Ws31.ArchC.J n a b w ζ := hfan.eqOn_of_preconnected_of_eventuallyEq hgan hU h1H heq hwH
  rw [key]
  exact hb w hw1 hw2 ζ hζ
