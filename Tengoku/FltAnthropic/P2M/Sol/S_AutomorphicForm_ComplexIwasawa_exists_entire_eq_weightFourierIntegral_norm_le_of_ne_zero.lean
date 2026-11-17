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

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_ComplexIwasawa_exists_entire_eq_weightFourierIntegral_norm_le_of_ne_zero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_ComplexIwasawa_exists_entire_eq_weightFourierIntegral_norm_le_of_ne_zero

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
@isnad1 id=ne.1h1v.s4.6192f30b1c52 from=translated src=- shape=5aedd577 vocab=d7ed41d9
-/
theorem cZ_ne_zero {ζ : ℂ} (hζ : ζ ≠ 0) : cZ ζ ≠ 0 := by
  unfold cZ
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) ?_
  · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  · exact (map_ne_zero (starRingEnd ℂ)).mpr hζ

/--
@isnad1 id=eq.0h1v.s5.dd825fa5eb78 from=translated src=- shape=71a20443 vocab=b07cb289
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
@isnad1 id=eq.0h2v.s4.b3a4ad885bed from=translated src=- shape=0e981eee vocab=ddeafdfe
-/
theorem norm_Ec (ζ z : ℂ) : ‖Ec ζ z‖ = 1 := by
  rw [Ec, ← neg_mul, ← Complex.ofReal_neg]
  exact Complex.norm_exp_ofReal_mul_I _

/--
@isnad1 id=eq.0h5v.s6.ecc1acc01670 from=translated src=- shape=ea5b7ff1 vocab=0d403286
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
@isnad1 id=le.1h6v.s7.4aa69a2134e9 from=translated src=- shape=706656f3 vocab=b30c0956
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
@isnad1 id=continuo.0h0v.s4.1d579f9b4ed6 from=translated src=- shape=e3d48bcb vocab=9ad37309
-/
theorem continuous_Bc : Continuous Bc :=
  Complex.continuous_ofReal.comp (continuous_const.add (continuous_norm.pow 2))

/--
@isnad1 id=mem.0h1v.s3.73027b496303 from=translated src=- shape=ca401064 vocab=9cdac337
-/
theorem Bc_mem_slitPlane (z : ℂ) : Bc z ∈ Complex.slitPlane :=
  Complex.ofReal_mem_slitPlane.2 (one_add_norm_sq_pos z)

/--
@isnad1 id=continuo.0h1v.s5.afbae09a7ae2 from=translated src=- shape=f736e2c1 vocab=4f80406f
-/
theorem continuous_Ec (ζ : ℂ) : Continuous (Ec ζ) := by
  unfold Ec
  have h1 : Continuous (fun z : ℂ => (4 * Real.pi * (ζ * z).re : ℝ)) :=
    continuous_const.mul (Complex.continuous_re.comp (continuous_const.mul continuous_id))
  exact Complex.continuous_exp.comp (((Complex.continuous_ofReal.comp h1).mul continuous_const).neg)

/--
@isnad1 id=continuo.0h4v.s5.70ca14e3fedb from=translated src=- shape=8113348d vocab=4541e806
-/
theorem continuous_F (a b : ℕ) (w ζ : ℂ) : Continuous (fun z => F a b w ζ z) := by
  have h1 : Continuous (fun z : ℂ => z ^ a * conj z ^ b) :=
    (continuous_id.pow a).mul (Complex.continuous_conj.pow b)
  have h2 : Continuous (fun z : ℂ => Bc z ^ (-w)) :=
    continuous_Bc.cpow continuous_const Bc_mem_slitPlane
  exact (h1.mul h2).mul (continuous_Ec ζ)

/--
@isnad1 id=integrab.1h4v.s6.e117c124673a from=translated src=- shape=92a91aed vocab=7db7c3ca
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
@isnad1 id=eq.0h2v.s6.9ba1996ef47c from=translated src=- shape=816c3bf5 vocab=8c684617
-/
theorem Bc_mk (x y : ℝ) : Bc ⟨x, y⟩ = (((1 + (x ^ 2 + y ^ 2)) : ℝ) : ℂ) := by
  rw [Bc, norm_sq_mk]

/--
@isnad1 id=eq.0h3v.s5.89523ffe1a3a from=translated src=- shape=60cdbdeb vocab=2d41a00e
-/
theorem re_mul_mk (ζ : ℂ) (x y : ℝ) : (ζ * ⟨x, y⟩).re = ζ.re * x - ζ.im * y := by
  simp [Complex.mul_re]

/--
@isnad1 id=eq.0h3v.s6.42f421328320 from=translated src=- shape=79680578 vocab=b7588a55
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
@isnad1 id=hasderiv.0h5v.s6.e2853385ba4c from=translated src=- shape=52a7fb61 vocab=d038a6cb
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
@isnad1 id=hasderiv.0h5v.s6.a2d74b9fe478 from=translated src=- shape=c428f87f vocab=be675d23
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
@isnad1 id=hasderiv.0h3v.s6.1c457c43d39e from=translated src=- shape=6e18ce3c vocab=b0e3d83e
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
@isnad1 id=hasderiv.0h3v.s6.007c0d04459e from=translated src=- shape=110adbc4 vocab=02928a1e
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
@isnad1 id=eq.0h2v.s5.04bc87829929 from=translated src=- shape=89133ad3 vocab=4482045a
-/
theorem Bc_cpow_neg_add_one (w z : ℂ) : Bc z ^ (-(w + 1)) = Bc z ^ (-w - 1) := by
  congr 1; ring

/--
@isnad1 id=eq.0h5v.s7.e2f453ec1325 from=translated src=- shape=24a309a3 vocab=1205edf3
-/
theorem GxEc_eq (a b : ℕ) (w ζ z : ℂ) : Gx a b w z * Ec ζ z =
    (a : ℂ) * F (a - 1) b w ζ z + (b : ℂ) * F a (b - 1) w ζ z
      - w * (F (a + 1) b (w + 1) ζ z + F a (b + 1) (w + 1) ζ z) := by
  have hre := two_re_eq z
  simp only [Gx, F, Bc_cpow_neg_add_one, pow_succ]
  linear_combination (-w * z ^ a * conj z ^ b * Bc z ^ (-w - 1) * Ec ζ z) * hre

/--
@isnad1 id=eq.0h5v.s7.2fdc7bff591a from=translated src=- shape=47db2402 vocab=c76fd605
-/
theorem GyEc_eq (a b : ℕ) (w ζ z : ℂ) : Gy a b w z * Ec ζ z =
    Complex.I * (a : ℂ) * F (a - 1) b w ζ z - Complex.I * (b : ℂ) * F a (b - 1) w ζ z
      + Complex.I * w * (F (a + 1) b (w + 1) ζ z - F a (b + 1) (w + 1) ζ z) := by
  have him := two_im_eq z
  simp only [Gy, F, Bc_cpow_neg_add_one, pow_succ]
  linear_combination (-w * z ^ a * conj z ^ b * Bc z ^ (-w - 1) * Ec ζ z) * him

/--
@isnad1 id=eq.0h5v.s7.f92c6c84e7cb from=translated src=- shape=5dea1ce7 vocab=a5a04982
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
@isnad1 id=integrab.1h4v.s6.5c0d2fd200c5 from=translated src=- shape=4d78049a vocab=6e89d679
-/
theorem integrable_GxEc (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) (ζ : ℂ) :
    Integrable (fun z => Gx a b w z * Ec ζ z) := by
  simp_rw [GxEc_eq]
  exact (((integrable_F (a - 1) b (thr_a_sub a b hw) ζ).const_mul _).add
    ((integrable_F a (b - 1) (thr_b_sub a b hw) ζ).const_mul _)).sub
    (((integrable_F (a + 1) b (thr_a_add a b hw) ζ).add (integrable_F a (b + 1) (thr_b_add a b hw) ζ)).const_mul _)

/--
@isnad1 id=integrab.1h4v.s6.ec969972c325 from=translated src=- shape=4d78049a vocab=a37c4365
-/
theorem integrable_GyEc (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) (ζ : ℂ) :
    Integrable (fun z => Gy a b w z * Ec ζ z) := by
  simp_rw [GyEc_eq]
  exact (((integrable_F (a - 1) b (thr_a_sub a b hw) ζ).const_mul _).sub
    ((integrable_F a (b - 1) (thr_b_sub a b hw) ζ).const_mul _)).add
    (((integrable_F (a + 1) b (thr_a_add a b hw) ζ).sub (integrable_F a (b + 1) (thr_b_add a b hw) ζ)).const_mul _)

/--
@isnad1 id=le.0h6v.s7.0459517cb61c from=translated src=- shape=d9a22267 vocab=1d32db6d
-/
theorem norm_F_mk_le (a b : ℕ) (w ζ : ℂ) (x y : ℝ) :
    ‖F a b w ζ ⟨x, y⟩‖ ≤ (1 + (x ^ 2 + y ^ 2)) ^ (-(2 * w.re - ((a + b : ℕ) : ℝ)) / 2) := by
  have h := norm_F_le a b (le_rfl : w.re ≤ w.re) ζ ⟨x, y⟩
  rwa [norm_sq_mk] at h

/--
@isnad1 id=and.1h5v.s7.f9ade3ca79f1 from=translated src=- shape=04c28d1c vocab=b0e2f332
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
@isnad1 id=and.1h5v.s7.3a332ce927ac from=translated src=- shape=c7bd1b17 vocab=b0e2f332
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
@isnad1 id=eq.1h4v.s6.35ae787b447b from=translated src=- shape=d414eb3e vocab=ac23e6ae
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
@isnad1 id=eq.1h4v.s6.2307ee3a7c7e from=translated src=- shape=603358ab vocab=abb3b0ee
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
@isnad1 id=eq.0h1v.s5.969cdaf8711b from=translated src=- shape=cfe93f19 vocab=dcf2006c
-/
theorem two_cZ (ζ : ℂ) : 2 * cZ ζ = cX ζ + Complex.I * (-cY ζ) := by
  simp only [cZ, cX, cY]
  rw [show (starRingEnd ℂ) ζ = conj ζ from rfl, conj_eq_re_sub_im]
  push_cast
  ring

/--
@isnad1 id=eq.1h4v.s7.914f22ade664 from=translated src=- shape=bc2b35a3 vocab=609790e3
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
@isnad1 id=and.0h2v.s8.201d40c4251f from=translated src=- shape=ebbfd3d8 vocab=b05f0cae
-/
theorem base (a b : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ => jj a b p.1 p.2) ({w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} ×ˢ Set.univ) ∧
    (∀ ζ : ℂ, DifferentiableOn ℂ (fun w : ℂ => jj a b w ζ) {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re}) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ ζ : ℂ, ‖jj a b w ζ‖ ≤ C * (1 + ‖ζ‖) ^ (-(N : ℝ))) :=
  AutomorphicForm.ComplexIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral a b

def H (n a b : ℕ) : Set ℂ := {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 - (n : ℝ) / 2 < w.re}

/--
@isnad1 id=isopen.0h3v.s4.78409dfdeaad from=translated src=- shape=0e1038f4 vocab=dca91ce4
-/
theorem isOpen_H (n a b : ℕ) : IsOpen (H n a b) := isOpen_lt continuous_const Complex.continuous_re

/--
@isnad1 id=eq.0h2v.s6.ab13b6a82d97 from=translated src=- shape=bca4b623 vocab=d01ec467
-/
theorem H_zero (a b : ℕ) : H 0 a b = {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} := by
  ext w; simp [H]

/--
@isnad1 id=mem.1h4v.s6.9e8ac62ac528 from=translated src=- shape=c4bd9ae6 vocab=434154aa
-/
theorem add_one_mem_H {n a b : ℕ} {w : ℂ} (hw : w ∈ H (n + 1) a b) : w + 1 ∈ H n (a + 1) b := by
  simp only [H, mem_ofPred_eq, Complex.add_re, Complex.one_re] at hw ⊢
  push_cast at hw ⊢
  linarith

/--
@isnad1 id=mem.1h4v.s5.18f8baff25ce from=translated src=- shape=2099ef36 vocab=434154aa
-/
theorem pred_mem_H {n a b : ℕ} {w : ℂ} (hw : w ∈ H (n + 1) a (b + 1)) : w ∈ H n a b := by
  simp only [H, mem_ofPred_eq] at hw ⊢
  push_cast at hw ⊢
  linarith

/--
@isnad1 id=le.1h4v.s4.2647f51c3e8c from=translated src=- shape=5ca0126e vocab=261fee05
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
@isnad1 id=eq.0h4v.s4.b65eadba135d from=translated src=- shape=8c981ba2 vocab=53b55955
-/
theorem J_zero (a b : ℕ) (w ζ : ℂ) : J 0 a b w ζ = jj a b w ζ := rfl

/--
@isnad1 id=eq.0h5v.s6.506f204577a9 from=translated src=- shape=096eb008 vocab=81efc33a
-/
theorem J_succ (n a b : ℕ) (w ζ : ℂ) :
    J (n + 1) a b w ζ = (cZ ζ)⁻¹ * ((b : ℂ) * J n a (b - 1) w ζ - w * J n (a + 1) b (w + 1) ζ) := rfl

/--
@isnad1 id=eq.2h5v.s5.51e06aa3ef9a from=translated src=- shape=21a3eaad vocab=8448b142
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
@isnad1 id=eq.3h6v.s5.fcf7fdad6ab7 from=translated src=- shape=6d6cd917 vocab=35d95896
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
@isnad1 id=differen.1h4v.s6.9f75bbae6b55 from=translated src=- shape=3ea9f3bb vocab=7743fc60
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
@isnad1 id=continuo.0h0v.s4.d24f176e750e from=translated src=- shape=e3d48bcb vocab=49eb7315
-/
theorem continuous_cZ : Continuous cZ := by
  unfold cZ
  exact continuous_const.mul (continuous_star)

/--
@isnad1 id=continuo.0h3v.s6.6511886aff6c from=translated src=- shape=19386925 vocab=c94856ce
-/
theorem J_continuousOn (n : ℕ) : ∀ a b : ℕ,
    ContinuousOn (fun p : ℂ × ℂ => J n a b p.1 p.2) (H n a b ×ˢ {ζ : ℂ | ζ ≠ 0}) := by
  induction n with
  | zero =>
    intro a b; rw [H_zero]
    exact (base a b).1.mono (Set.prod_mono le_rfl (Set.subset_univ _))
  | succ n ih =>
    intro a b
    have m1 : MapsTo (fun p : ℂ × ℂ => (p.1 + 1, p.2)) (H (n + 1) a b ×ˢ {ζ : ℂ | ζ ≠ 0})
        (H n (a + 1) b ×ˢ {ζ : ℂ | ζ ≠ 0}) := fun p hp => ⟨add_one_mem_H hp.1, hp.2⟩
    have c1 : Continuous (fun p : ℂ × ℂ => (p.1 + 1, p.2)) := by fun_prop
    have h1 : ContinuousOn (fun p : ℂ × ℂ => (b : ℂ) * J n a (b - 1) p.1 p.2) (H (n + 1) a b ×ˢ {ζ : ℂ | ζ ≠ 0}) := by
      cases b with
      | zero =>
        refine (continuousOn_const (c := (0 : ℂ))).congr (fun p _ => ?_)
        simp only [Nat.cast_zero, zero_mul]
      | succ b' =>
        rw [Nat.add_sub_cancel]
        exact continuousOn_const.mul ((ih a b').mono (Set.prod_mono (fun w hw => pred_mem_H hw) le_rfl))
    have h2 : ContinuousOn (fun p : ℂ × ℂ => J n (a + 1) b (p.1 + 1) p.2) (H (n + 1) a b ×ˢ {ζ : ℂ | ζ ≠ 0}) :=
      (ih (a + 1) b).comp c1.continuousOn m1
    have hc : ContinuousOn (fun p : ℂ × ℂ => (cZ p.2)⁻¹) (H (n + 1) a b ×ˢ {ζ : ℂ | ζ ≠ 0}) :=
      (continuous_cZ.comp continuous_snd).continuousOn.inv₀ (fun p hp => cZ_ne_zero hp.2)
    show ContinuousOn (fun p : ℂ × ℂ => (cZ p.2)⁻¹ * ((b : ℂ) * J n a (b - 1) p.1 p.2
      - p.1 * J n (a + 1) b (p.1 + 1) p.2)) (H (n + 1) a b ×ˢ {ζ : ℂ | ζ ≠ 0})
    exact hc.mul (h1.sub (continuous_fst.continuousOn.mul h2))

/--
@isnad1 id=le.1h1v.s5.8e2039c9da56 from=translated src=- shape=82284ddd vocab=9685f192
-/
theorem norm_inv_cZ_le {ζ : ℂ} (hζ : ζ ≠ 0) : ‖(cZ ζ)⁻¹‖ ≤ max 1 ‖ζ‖⁻¹ := by
  rw [norm_inv, norm_cZ]
  refine le_trans ?_ (le_max_right _ _)
  have hζ' : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ
  rw [inv_le_inv₀ (by positivity) hζ']
  have : (1 : ℝ) ≤ 2 * Real.pi := by have := Real.two_le_pi; linarith
  nlinarith

/--
@isnad1 id=ex.2h4v.s7.81ccc577bc22 from=translated src=- shape=c25c489a vocab=f997227e
-/
theorem J_bound (n : ℕ) : ∀ (a b : ℕ) (K : Set ℂ), IsCompact K → K ⊆ H n a b → ∃ A : ℕ, ∀ N : ℕ,
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 →
      ‖J n a b w ζ‖ ≤ C * (max 1 ‖ζ‖⁻¹) ^ A * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
  induction n with
  | zero =>
    intro a b K hK hKH
    refine ⟨0, fun N => ?_⟩
    obtain ⟨C, hC, hb⟩ := (base a b).2.2 K hK (by rw [H_zero] at hKH; exact hKH) N
    exact ⟨C, hC, fun w hw ζ _ => by rw [pow_zero, mul_one, J_zero]; exact hb w hw ζ⟩
  | succ n ih =>
    intro a b K hK hKH
    have hK1 : IsCompact ((fun w : ℂ => w + 1) '' K) := hK.image (by fun_prop)
    have hK1H : (fun w : ℂ => w + 1) '' K ⊆ H n (a + 1) b := by
      rintro _ ⟨w, hw, rfl⟩; exact add_one_mem_H (hKH hw)

    have hT1 : ∃ A₁ : ℕ, ∀ N : ℕ, ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 →
        ‖(b : ℂ) * J n a (b - 1) w ζ‖ ≤ C₁ * (max 1 ‖ζ‖⁻¹) ^ A₁ * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
      cases b with
      | zero =>
        refine ⟨0, fun N => ⟨1, one_pos, fun w _ ζ _ => ?_⟩⟩
        simp only [Nat.cast_zero, zero_mul, norm_zero, pow_zero, mul_one, one_mul]
        exact Real.rpow_nonneg (by positivity) _
      | succ b' =>
        have hKH' : K ⊆ H n a b' := fun w hw => pred_mem_H (hKH hw)
        obtain ⟨A₁, hA₁⟩ := ih a b' K hK hKH'
        refine ⟨A₁, fun N => ?_⟩
        obtain ⟨C₁, hC₁, hb₁⟩ := hA₁ N
        refine ⟨((b' + 1 : ℕ) : ℝ) * C₁, by positivity, fun w hw ζ hζ => ?_⟩
        rw [Nat.add_sub_cancel, norm_mul, Complex.norm_natCast, mul_assoc, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have := hb₁ w hw ζ hζ
        rw [mul_assoc] at this
        exact this
    obtain ⟨A₁, hA₁⟩ := hT1
    obtain ⟨A₂, hA₂⟩ := ih (a + 1) b _ hK1 hK1H
    obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
    set R : ℝ := max R₀ 0 with hRdef
    have hR0 : 0 ≤ R := le_max_right _ _
    have hR : ∀ w ∈ K, ‖w‖ ≤ R := fun w hw => (hR₀ w hw).trans (le_max_left _ _)
    set A : ℕ := A₁ + A₂ with hAdef
    refine ⟨A + 1, fun N => ?_⟩
    obtain ⟨C₁, hC₁, hb₁⟩ := hA₁ N
    obtain ⟨C₂, hC₂, hb₂⟩ := hA₂ N
    refine ⟨C₁ + R * C₂ + 1, by positivity, fun w hw ζ hζ => ?_⟩
    set M : ℝ := max 1 ‖ζ‖⁻¹ with hMdef
    set D : ℝ := (1 + ‖ζ‖) ^ (-(N : ℝ)) with hDdef
    have hM : 1 ≤ M := le_max_left _ _
    have hD : 0 ≤ D := Real.rpow_nonneg (by positivity) _
    have hMA : 0 ≤ M ^ A * D := mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) hD
    have e1 : ‖(b : ℂ) * J n a (b - 1) w ζ‖ ≤ C₁ * (M ^ A * D) := by
      refine (hb₁ w hw ζ hζ).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hM (by rw [hAdef]; omega)) hD) hC₁.le
    have e2 : ‖J n (a + 1) b (w + 1) ζ‖ ≤ C₂ * (M ^ A * D) := by
      refine (hb₂ (w + 1) ⟨w, hw, rfl⟩ ζ hζ).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hM (by rw [hAdef]; omega)) hD) hC₂.le
    rw [J_succ, norm_mul]
    have step : ‖(b : ℂ) * J n a (b - 1) w ζ - w * J n (a + 1) b (w + 1) ζ‖
        ≤ (C₁ + R * C₂ + 1) * (M ^ A * D) := by
      refine (norm_sub_le _ _).trans ?_
      have hw' := hR w hw
      have hwC : ‖w * J n (a + 1) b (w + 1) ζ‖ ≤ R * (C₂ * (M ^ A * D)) := by
        rw [norm_mul]
        exact mul_le_mul hw' e2 (norm_nonneg _) hR0
      nlinarith [e1, hwC, hMA, hC₁.le, hC₂.le]
    calc ‖(cZ ζ)⁻¹‖ * ‖(b : ℂ) * J n a (b - 1) w ζ - w * J n (a + 1) b (w + 1) ζ‖
        ≤ M * ((C₁ + R * C₂ + 1) * (M ^ A * D)) :=
          mul_le_mul (norm_inv_cZ_le hζ) step (norm_nonneg _) (zero_le_one.trans hM)
      _ = (C₁ + R * C₂ + 1) * M ^ (A + 1) * D := by rw [pow_succ]; ring

def nw (a b : ℕ) (w : ℂ) : ℕ := ⌈((a + b : ℕ) : ℝ) + 2 - 2 * w.re⌉₊ + 1

/--
@isnad1 id=mem.0h3v.s4.235c858f6ac0 from=translated src=- shape=73d37bf0 vocab=6bea847f
-/
theorem mem_H_nw (a b : ℕ) (w : ℂ) : w ∈ H (nw a b w) a b := by
  simp only [H, nw, mem_ofPred_eq]
  have := Nat.le_ceil (((a + b : ℕ) : ℝ) + 2 - 2 * w.re)
  push_cast at this ⊢
  linarith

def Jg (a b : ℕ) (w ζ : ℂ) : ℂ := J (nw a b w) a b w ζ

/--
@isnad1 id=eq.2h5v.s5.0db4c63baf25 from=translated src=- shape=c79c69d1 vocab=29540706
-/
theorem Jg_eq (a b : ℕ) {n : ℕ} {w : ℂ} (hw : w ∈ H n a b) {ζ : ℂ} (hζ : ζ ≠ 0) : Jg a b w ζ = J n a b w ζ := by
  have h1 := J_eq_of_le (le_max_left (nw a b w) n) a b w ζ (mem_H_nw a b w) hζ
  have h2 := J_eq_of_le (le_max_right (nw a b w) n) a b w ζ hw hζ
  unfold Jg
  exact h1.symm.trans h2

/--
@isnad1 id=analytic.1h3v.s5.01addde27fab from=translated src=- shape=a311a951 vocab=fa4c01f3
-/
theorem clause_a (a b : ℕ) (ζ : ℂ) (hζ : ζ ≠ 0) : AnalyticOnNhd ℂ (fun w : ℂ => Jg a b w ζ) Set.univ := by
  refine DifferentiableOn.analyticOnNhd (fun w₀ _ => ?_) isOpen_univ
  apply DifferentiableAt.differentiableWithinAt
  have hmem : H (nw a b w₀) a b ∈ 𝓝 w₀ := (isOpen_H _ _ _).mem_nhds (mem_H_nw a b w₀)
  have hd : DifferentiableAt ℂ (fun w => J (nw a b w₀) a b w ζ) w₀ :=
    (J_differentiableOn _ a b ζ hζ).differentiableAt hmem
  refine hd.congr_of_eventuallyEq ?_
  exact Filter.eventually_of_mem hmem (fun w hw => Jg_eq a b hw hζ)

/--
@isnad1 id=eq.2h4v.s6.0e348b27e3d3 from=translated src=- shape=df621bc5 vocab=cd28ad11
-/
theorem clause_b (a b : ℕ) (w ζ : ℂ) (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) (hζ : ζ ≠ 0) :
    Jg a b w ζ = jj a b w ζ := by
  have hw0 : w ∈ H 0 a b := by rw [H_zero]; exact hw
  rw [Jg_eq a b hw0 hζ, J_zero]

/--
@isnad1 id=continuo.0h2v.s6.e350fdfc864d from=translated src=- shape=88de36ff vocab=bdb67608
-/
theorem clause_c (a b : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ => Jg a b p.1 p.2) (Set.univ ×ˢ {ζ : ℂ | ζ ≠ 0}) := by
  intro p hp
  have hζ : p.2 ≠ 0 := hp.2
  have hO : IsOpen (H (nw a b p.1) a b ×ˢ {ζ : ℂ | ζ ≠ 0}) := (isOpen_H _ _ _).prod isOpen_ne
  have hmem : H (nw a b p.1) a b ×ˢ {ζ : ℂ | ζ ≠ 0} ∈ 𝓝 p := hO.mem_nhds ⟨mem_H_nw _ _ _, hζ⟩
  have hc : ContinuousAt (fun q : ℂ × ℂ => J (nw a b p.1) a b q.1 q.2) p :=
    ((J_continuousOn _ a b) p ⟨mem_H_nw _ _ _, hζ⟩).continuousAt hmem
  refine (hc.congr_of_eventuallyEq ?_).continuousWithinAt
  exact Filter.eventually_of_mem hmem (fun q hq => Jg_eq a b hq.1 hq.2)

/--
@isnad1 id=ex.1h3v.s7.541289dd35d0 from=translated src=- shape=18aeb14f vocab=9637437c
-/
theorem clause_d (a b : ℕ) (K : Set ℂ) (hK : IsCompact K) :
    ∃ A : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 →
      ‖Jg a b w ζ‖ ≤ C * (max 1 ‖ζ‖⁻¹) ^ A * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
  obtain ⟨m, hm⟩ := (hK.image Complex.continuous_re).bddBelow
  set n : ℕ := ⌈((a + b : ℕ) : ℝ) + 2 - 2 * m⌉₊ + 1 with hndef
  have hKH : K ⊆ H n a b := by
    intro w hw
    have h1 : m ≤ w.re := hm ⟨w, hw, rfl⟩
    simp only [H, hndef, mem_ofPred_eq]
    have := Nat.le_ceil (((a + b : ℕ) : ℝ) + 2 - 2 * m)
    push_cast at this ⊢
    linarith
  obtain ⟨A, hA⟩ := J_bound n a b K hK hKH
  refine ⟨A, fun N => ?_⟩
  obtain ⟨C, hC, hb⟩ := hA N
  exact ⟨C, hC, fun w hw ζ hζ => by rw [Jg_eq a b (hKH hw) hζ]; exact hb w hw ζ hζ⟩

end Ws31.ArchC

end

/--
@isnad1 id=other.0h2v.s9.47b77476cc27 from=translated src=- shape=ec60d0d6 vocab=d01dd82e
-/
theorem solution (a b : ℕ) :
    let j : ℂ → ℂ → ℂ := fun w ζ => ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))
    ∃ J : ℂ → ℂ → ℂ,
      (∀ ζ : ℂ, ζ ≠ 0 → AnalyticOnNhd ℂ (fun w : ℂ => J w ζ) Set.univ) ∧
      (∀ (w : ℂ) (ζ : ℂ), ((a + b : ℕ) : ℝ) / 2 + 1 < w.re → ζ ≠ 0 → J w ζ = j w ζ) ∧
      ContinuousOn (fun p : ℂ × ℂ => J p.1 p.2) (Set.univ ×ˢ {ζ : ℂ | ζ ≠ 0}) ∧
      (∀ K : Set ℂ, IsCompact K → ∃ A : ℕ, ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
        ∀ w ∈ K, ∀ ζ : ℂ, ζ ≠ 0 → ‖J w ζ‖ ≤ C * (max 1 ‖ζ‖⁻¹) ^ A * (1 + ‖ζ‖) ^ (-(N : ℝ))) := by
  intro j
  have hj : j = fun w ζ => Ws31.ArchC.jj a b w ζ := rfl
  refine ⟨Ws31.ArchC.Jg a b, fun ζ hζ => Ws31.ArchC.clause_a a b ζ hζ, ?_, Ws31.ArchC.clause_c a b,
    fun K hK => Ws31.ArchC.clause_d a b K hK⟩
  intro w ζ hw hζ
  rw [hj]
  exact Ws31.ArchC.clause_b a b w ζ hw hζ
