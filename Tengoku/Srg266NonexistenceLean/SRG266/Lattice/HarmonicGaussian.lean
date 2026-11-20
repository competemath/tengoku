/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.HarmonicQuadratic
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace SRG266.Lattice

open MeasureTheory Filter Asymptotics
open scoped RealInnerProductSpace Topology

/--
@isnad1 id=ex.1h2v.s6.7ccd5c706e3f from=translated src=- shape=5e27888f vocab=7bd747cc
-/
theorem exists_bound_pow_mul_rexp_neg_sq (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      |r| ^ k * Real.exp (-a * r ^ 2) ≤ C := by
  let h : ℝ → ℝ := fun r ↦ |r| ^ k * Real.exp (-a * r ^ 2)
  have ht : Tendsto h (cocompact ℝ) (𝓝 0) := by
    simpa only [h, Real.rpow_natCast] using
      tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact ha (k : ℝ)
  have hcont : Continuous h := by
    dsimp only [h]
    fun_prop
  have hbounded : Bornology.IsBounded (Set.range h) :=
    hcont.isBounded_range_iff_isBigO.mpr (ht.isBigO_one ℝ)
  rw [isBounded_iff_forall_norm_le] at hbounded
  obtain ⟨C, hC⟩ := hbounded
  refine ⟨max C 0, le_max_right _ _, fun r ↦ ?_⟩
  have hr := hC (h r) ⟨r, rfl⟩
  have hh : 0 ≤ h r := mul_nonneg (pow_nonneg (abs_nonneg _) _) (Real.exp_pos _).le
  exact (show h r ≤ C by simpa [Real.norm_of_nonneg hh] using hr).trans
    (le_max_left _ _)

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def realGaussian (t : ℝ) : V → ℂ := fun v ↦
  Complex.exp (-((Real.pi * t : ℝ) : ℂ) * ‖v‖ ^ 2)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/--
@isnad1 id=continuo.0h2v.s5.356a526e3468 from=translated src=- shape=5e19da9f vocab=c4c5c8db
-/
theorem realGaussian_continuous (t : ℝ) :
    Continuous (realGaussian (V := V) t) := by
  unfold realGaussian
  fun_prop

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/--
@isnad1 id=eq.0h3v.s5.38861eda870e from=translated src=- shape=6bfde282 vocab=352b1c4b
-/
@[simp]
theorem realGaussian_neg (t : ℝ) (v : V) :
    realGaussian t (-v) = realGaussian t v := by
  simp [realGaussian]

/--
@isnad1 id=integrab.1h3v.s7.bcb1a4b083b2 from=translated src=- shape=0ea71d7a vocab=462c16eb
-/
theorem integrable_norm_pow_mul_rexp_neg_sq_norm (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable fun v : V ↦ ‖v‖ ^ k * Real.exp (-b * ‖v‖ ^ 2) := by
  let a : ℝ := b / 2
  have ha : 0 < a := div_pos hb (by norm_num)
  obtain ⟨C, hCnonneg, hC⟩ := exists_bound_pow_mul_rexp_neg_sq k ha
  have hbaseComplex := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := V) (b := (a : ℂ)) (by simpa using ha) 0 0
  have hbase : Integrable fun v : V ↦ Real.exp (-a * ‖v‖ ^ 2) := by
    convert hbaseComplex.norm using 1
    funext v
    rw [Complex.norm_exp]
    have hre :
        (-((a : ℂ)) * (‖v‖ : ℂ) ^ 2 + 0 * (inner ℝ (0 : V) v : ℂ)).re =
          -a * ‖v‖ ^ 2 := by
      have hpow : (‖v‖ : ℂ) ^ 2 = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
        norm_cast
      rw [hpow]
      norm_num
      left
      norm_cast
    rw [hre]
  apply Integrable.mono' (hbase.const_mul C)
  · fun_prop
  · filter_upwards with v
    rw [Real.norm_of_nonneg
      (mul_nonneg (pow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le)]
    have hv := hC ‖v‖
    rw [abs_of_nonneg (norm_nonneg _)] at hv
    have hbdiv : b = a + a := by
      dsimp only [a]
      ring
    rw [hbdiv]
    have hexp : -(a + a) * ‖v‖ ^ 2 =
        -a * ‖v‖ ^ 2 + -a * ‖v‖ ^ 2 := by ring
    rw [hexp, Real.exp_add]
    calc
      ‖v‖ ^ k * (Real.exp (-a * ‖v‖ ^ 2) *
          Real.exp (-a * ‖v‖ ^ 2)) =
          (‖v‖ ^ k * Real.exp (-a * ‖v‖ ^ 2)) *
            Real.exp (-a * ‖v‖ ^ 2) := by ring
      _ ≤ C * Real.exp (-a * ‖v‖ ^ 2) := by
        gcongr

/--
@isnad1 id=integrab.1h3v.s7.6b4211a27dc9 from=translated src=- shape=2aa72300 vocab=be97b661
-/
theorem realGaussian_moment_integrable (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable fun v : V ↦ ‖v‖ ^ k * ‖realGaussian (V := V) t v‖ := by
  have h := integrable_norm_pow_mul_rexp_neg_sq_norm
    (V := V) k (mul_pos Real.pi_pos ht)
  convert h using 1
  funext v
  rw [realGaussian, Complex.norm_exp]
  have hre :
      (-((Real.pi * t : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2).re =
        -(Real.pi * t) * ‖v‖ ^ 2 := by
    norm_cast
  rw [hre]

def harmonicGaussian (t : ℝ) (x y : V) : V → ℂ := fun v ↦
  (harmonicQuadratic x y v : ℂ) * realGaussian t v

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/--
@isnad1 id=continuo.0h4v.s5.f24dcdc91a37 from=translated src=- shape=0e10e583 vocab=31399676
-/
theorem harmonicGaussian_continuous (t : ℝ) (x y : V) :
    Continuous (harmonicGaussian t x y) := by
  unfold harmonicGaussian harmonicQuadratic realGaussian
  fun_prop

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/--
@isnad1 id=eq.0h4v.s5.2c4dc36e978c from=translated src=- shape=7ed9ca5f vocab=65280d54
-/
@[simp]
theorem harmonicGaussian_zero (t : ℝ) (x y : V) :
    harmonicGaussian t x y 0 = 0 := by
  simp [harmonicGaussian]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/--
@isnad1 id=eq.0h5v.s5.5fe21788221d from=translated src=- shape=cb84f5fc vocab=9f831d90
-/
@[simp]
theorem harmonicGaussian_neg (t : ℝ) (x y v : V) :
    harmonicGaussian t x y (-v) = harmonicGaussian t x y v := by
  simp [harmonicGaussian]

/--
@isnad1 id=integrab.1h4v.s6.8fae82821a58 from=translated src=- shape=41b1df54 vocab=9d0da464
-/
theorem harmonicGaussian_integrable {t : ℝ} (ht : 0 < t) (x y : V) :
    Integrable (harmonicGaussian t x y) := by
  let C : ℝ := ((Module.finrank ℝ V : ℝ) + 1) * ‖x‖ * ‖y‖
  have hmoment := integrable_norm_pow_mul_rexp_neg_sq_norm
    (V := V) 2 (mul_pos Real.pi_pos ht)
  apply Integrable.mono' (hmoment.const_mul C)
  · exact (harmonicGaussian_continuous t x y).aestronglyMeasurable
  · filter_upwards with v
    rw [harmonicGaussian, realGaussian, norm_mul, Complex.norm_exp]
    have hre :
        (-((Real.pi * t : ℝ) : ℂ) * (‖v‖ : ℂ) ^ 2).re =
          -(Real.pi * t) * ‖v‖ ^ 2 := by
      norm_cast
    rw [hre]
    have hp := abs_harmonicQuadratic_le x y v
    rw [Complex.norm_real, Real.norm_eq_abs]
    change |harmonicQuadratic x y v| * Real.exp (-(Real.pi * t) * ‖v‖ ^ 2) ≤
      C * (‖v‖ ^ 2 * Real.exp (-(Real.pi * t) * ‖v‖ ^ 2))
    calc
      |harmonicQuadratic x y v| * Real.exp (-(Real.pi * t) * ‖v‖ ^ 2) ≤
          (C * ‖v‖ ^ 2) * Real.exp (-(Real.pi * t) * ‖v‖ ^ 2) := by
        gcongr
      _ = C * (‖v‖ ^ 2 * Real.exp (-(Real.pi * t) * ‖v‖ ^ 2)) := by ring

end SRG266.Lattice
