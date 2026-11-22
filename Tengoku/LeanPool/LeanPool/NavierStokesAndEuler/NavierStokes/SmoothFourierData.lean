/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Tengoku.Seed.Analysis.Fourier.AddCircleMulti
import Tengoku.Seed.Analysis.Calculus.Deriv.Prod
import Tengoku.Seed.Analysis.PSeries
public import Tengoku.Seed.Analysis.Fourier.AddCircle
import Tengoku.Seed.Analysis.Calculus.SmoothSeries
import Tengoku.Seed.MeasureTheory.Integral.Prod
public import Tengoku.Seed.Analysis.Real.Sqrt
import Tengoku.Seed.NumberTheory.Real.Irrational
namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool
namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fourier coefficients of actual smooth periodic functions

Coefficients are defined by actual unit-interval integrals. Their decay is
derived from integration by parts and bounds for actual coordinate derivatives.
-/

section

/-!
# Smooth Fourier series and directional inversion on the two-dimensional torus

We work on the universal cover `ℝ × ℝ`, with frequencies in `ℤ × ℤ`.
Rapid coefficients have summable polynomially weighted norms of every order.
-/

section

/-!
# Diophantine bounds for the manuscript's graph directions

For every nonzero integer frequency `(m,n)`, the directions
`v_r = (1, 1 - sqrt 2)` and `v_t = (sqrt 2 - 1, 1)` have symbols bounded
below by `(1/6)/(1 + sqrt (m^2+n^2))`. The proof multiplies each quadratic
integer by its conjugate, proves that the resulting integer is nonzero using
irrationality of `sqrt 2`, and bounds the conjugate explicitly.
-/

@[expose] public section

noncomputable section

namespace NavierStokes.DiophantineGraph

/-- Quadratic form, given by `(p : ℝ) + Real.sqrt 2 * (q : ℝ)`. -/
def quadraticForm (p q : ℤ) : ℝ := (p : ℝ) + Real.sqrt 2 * (q : ℝ)

/-- Integer norm, given by `p ^ 2 - 2 * q ^ 2`. -/
def integerNorm (p q : ℤ) : ℤ := p ^ 2 - 2 * q ^ 2

/--
@isnad1 id=eq.0h0v.s5.cf4d3864bf7d from=translated src=- shape=424e5f08 vocab=2d61703d
-/
theorem sqrt_two_square : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
  Real.sq_sqrt (by norm_num)

/--
@isnad1 id=le.0h0v.s4.5a7d98024410 from=translated src=- shape=3c26ae4f vocab=75e1f5d6
-/
theorem sqrt_two_le_two : Real.sqrt 2 ≤ (2 : ℝ) := by
  nlinarith [sqrt_two_square, Real.sqrt_nonneg (2 : ℝ)]

/--
@isnad1 id=ne.1h2v.s5.b45466f580e0 from=translated src=- shape=100f4671 vocab=5e3696a4
-/
theorem quadraticForm_ne_zero (p q : ℤ) (hpq : p ≠ 0 ∨ q ≠ 0) :
    quadraticForm p q ≠ 0 := by
  by_cases hq : q = 0
  · have hp : p ≠ 0 := hpq.resolve_right (not_not.mpr hq)
    simpa [quadraticForm, hq] using hp
  · exact ((irrational_sqrt_two.mul_intCast hq).intCast_add p).ne_zero

/--
@isnad1 id=eq.0h2v.s4.fa9825235118 from=translated src=- shape=1cade4f9 vocab=002c756f
-/
theorem conjugate_product (p q : ℤ) :
    quadraticForm p q * quadraticForm p (-q) = (integerNorm p q : ℝ) := by
  simp only [quadraticForm, integerNorm, Int.cast_neg, Int.cast_sub,
    Int.cast_pow, Int.cast_mul, Int.cast_ofNat]
  nlinarith [congrArg (fun x : ℝ => x * (q : ℝ) ^ 2) sqrt_two_square]

/--
@isnad1 id=ne.1h2v.s5.784f2b9ce41e from=translated src=- shape=31a09a72 vocab=f83f33b3
-/
theorem integerNorm_ne_zero (p q : ℤ) (hpq : p ≠ 0 ∨ q ≠ 0) :
    integerNorm p q ≠ 0 := by
  have hconj : p ≠ 0 ∨ -q ≠ 0 := by
    rcases hpq with hp | hq
    · exact Or.inl hp
    · exact Or.inr (neg_ne_zero.mpr hq)
  have hprod := mul_ne_zero (quadraticForm_ne_zero p q hpq)
    (quadraticForm_ne_zero p (-q) hconj)
  intro hz
  apply hprod
  rw [conjugate_product, hz, Int.cast_zero]

/-- The nonzero algebraic norm is an integer, so its absolute value is at least one.
@isnad1 id=le.1h2v.s5.e3995c37c294 from=translated src=- shape=078d5946 vocab=a8f186c7
-/
theorem conjugate_product_lower (p q : ℤ) (hpq : p ≠ 0 ∨ q ≠ 0) :
    1 ≤ |quadraticForm p q| * |quadraticForm p (-q)| := by
  have hi : (1 : ℤ) ≤ |integerNorm p q| :=
    Int.add_one_le_iff.mpr (abs_pos.mpr (integerNorm_ne_zero p q hpq))
  have hr : (1 : ℝ) ≤ |(integerNorm p q : ℝ)| := by exact_mod_cast hi
  rw [← conjugate_product, abs_mul] at hr
  exact hr

/-- Radial symbol, given by `quadraticForm (m + n) (-n)`. -/
def radialSymbol (m n : ℤ) : ℝ := quadraticForm (m + n) (-n)

/-- Time symbol, given by `quadraticForm (n - m) m`. -/
def timeSymbol (m n : ℤ) : ℝ := quadraticForm (n - m) m

/-- Radial conjugate, given by `quadraticForm (m + n) n`. -/
def radialConjugate (m n : ℤ) : ℝ := quadraticForm (m + n) n

/-- Time conjugate, given by `quadraticForm (n - m) (-m)`. -/
def timeConjugate (m n : ℤ) : ℝ := quadraticForm (n - m) (-m)

/--
@isnad1 id=eq.0h2v.s5.4a34d6b9f373 from=translated src=- shape=a3f75dba vocab=00548c79
-/
theorem radialSymbol_formula (m n : ℤ) :
    radialSymbol m n = (m : ℝ) + (1 - Real.sqrt 2) * (n : ℝ) := by
  simp only [radialSymbol, quadraticForm, Int.cast_add, Int.cast_neg]
  ring

/--
@isnad1 id=eq.0h2v.s5.539d818fe3a1 from=translated src=- shape=3977c9ff vocab=82b69b32
-/
theorem timeSymbol_formula (m n : ℤ) :
    timeSymbol m n = (Real.sqrt 2 - 1) * (m : ℝ) + (n : ℝ) := by
  simp only [timeSymbol, quadraticForm, Int.cast_sub]
  ring

/--
@isnad1 id=eq.0h2v.s5.ed3b3b8e2901 from=translated src=- shape=6fb8678c vocab=78e3003b
-/
theorem radialConjugate_formula (m n : ℤ) :
    radialConjugate m n = (m : ℝ) + (1 + Real.sqrt 2) * (n : ℝ) := by
  simp only [radialConjugate, quadraticForm, Int.cast_add]
  ring

/--
@isnad1 id=eq.0h2v.s5.5515387a3d8e from=translated src=- shape=abc4e637 vocab=d1fd504b
-/
theorem timeConjugate_formula (m n : ℤ) :
    timeConjugate m n = (n : ℝ) - (1 + Real.sqrt 2) * (m : ℝ) := by
  simp only [timeConjugate, quadraticForm, Int.cast_sub, Int.cast_neg]
  ring

/--
@isnad1 id=le.1h2v.s5.3ef4c20d27e6 from=translated src=- shape=9cd949f9 vocab=7e1af756
-/
theorem radial_product_lower (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    1 ≤ |radialSymbol m n| * |radialConjugate m n| := by
  have hpq : m + n ≠ 0 ∨ -n ≠ 0 := by
    by_cases hn : n = 0
    · left
      simpa [hn] using hmn.resolve_right (not_not.mpr hn)
    · exact Or.inr (neg_ne_zero.mpr hn)
  simpa only [radialSymbol, radialConjugate, neg_neg] using
    conjugate_product_lower (m + n) (-n) hpq

/--
@isnad1 id=le.1h2v.s5.1d6a65a2cb57 from=translated src=- shape=9cd949f9 vocab=efd4d00a
-/
theorem time_product_lower (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    1 ≤ |timeSymbol m n| * |timeConjugate m n| := by
  have hpq : n - m ≠ 0 ∨ m ≠ 0 := by
    by_cases hm : m = 0
    · left
      simpa [hm] using hmn.resolve_left (not_not.mpr hm)
    · exact Or.inr hm
  exact conjugate_product_lower (n - m) m hpq

/-- Frequency L1, given by `|(m : ℝ)| + |(n : ℝ)|`. -/
def frequencyL1 (m n : ℤ) : ℝ := |(m : ℝ)| + |(n : ℝ)|

/-- This is the usual Euclidean length of the integer frequency. -/
def frequencyLength (m n : ℤ) : ℝ := Real.sqrt ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)

/--
@isnad1 id=le.0h2v.s4.c5f828775304 from=translated src=- shape=5ffe46ab vocab=3f701cd9
-/
theorem frequencyL1_nonneg (m n : ℤ) : 0 ≤ frequencyL1 m n := by
  unfold frequencyL1
  positivity

/--
@isnad1 id=le.0h2v.s4.85baffe2f2f4 from=translated src=- shape=5ffe46ab vocab=7a66577c
-/
theorem frequencyLength_nonneg (m n : ℤ) : 0 ≤ frequencyLength m n :=
  Real.sqrt_nonneg _

/--
@isnad1 id=le.0h2v.s5.2eaf0dedf554 from=translated src=- shape=4ba8bac3 vocab=d8a5cc68
-/
theorem radialConjugate_upper (m n : ℤ) :
    |radialConjugate m n| ≤ 3 * frequencyL1 m n := by
  rw [radialConjugate_formula]
  calc
    |(m : ℝ) + (1 + Real.sqrt 2) * (n : ℝ)| ≤
        |(m : ℝ)| + |(1 + Real.sqrt 2) * (n : ℝ)| := abs_add_le _ _
    _ = |(m : ℝ)| + (1 + Real.sqrt 2) * |(n : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + Real.sqrt 2)]
    _ ≤ 3 * frequencyL1 m n := by
      unfold frequencyL1
      nlinarith [mul_le_mul_of_nonneg_right sqrt_two_le_two (abs_nonneg (n : ℝ)),
        abs_nonneg (m : ℝ)]

/--
@isnad1 id=le.0h2v.s5.f9932fa61ee7 from=translated src=- shape=4ba8bac3 vocab=053efa17
-/
theorem timeConjugate_upper (m n : ℤ) :
    |timeConjugate m n| ≤ 3 * frequencyL1 m n := by
  rw [timeConjugate_formula]
  calc
    |(n : ℝ) - (1 + Real.sqrt 2) * (m : ℝ)| ≤
        |(n : ℝ)| + |(1 + Real.sqrt 2) * (m : ℝ)| := abs_sub _ _
    _ = |(n : ℝ)| + (1 + Real.sqrt 2) * |(m : ℝ)| := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + Real.sqrt 2)]
    _ ≤ 3 * frequencyL1 m n := by
      unfold frequencyL1
      nlinarith [mul_le_mul_of_nonneg_right sqrt_two_le_two (abs_nonneg (m : ℝ)),
        abs_nonneg (n : ℝ)]

/--
@isnad1 id=le.0h2v.s4.2645cc7f04d7 from=translated src=- shape=019f50d6 vocab=46278fe4
-/
theorem frequencyL1_le_twice_length (m n : ℤ) :
    frequencyL1 m n ≤ 2 * frequencyLength m n := by
  have hs : frequencyLength m n ^ 2 = (m : ℝ) ^ 2 + (n : ℝ) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hm : |(m : ℝ)| ≤ frequencyLength m n := by
    apply (sq_le_sq₀ (abs_nonneg _) (frequencyLength_nonneg m n)).mp
    rw [sq_abs, hs]
    nlinarith [sq_nonneg (n : ℝ)]
  have hn : |(n : ℝ)| ≤ frequencyLength m n := by
    apply (sq_le_sq₀ (abs_nonneg _) (frequencyLength_nonneg m n)).mp
    rw [sq_abs, hs]
    nlinarith [sq_nonneg (m : ℝ)]
  unfold frequencyL1
  linarith

/--
@isnad1 id=le.3h3v.s6.9b531daf7a9c from=translated src=- shape=d5ecae9b vocab=3fd12985
-/
theorem lower_of_conjugate_bound {a b D : ℝ} (hprod : 1 ≤ |a| * |b|)
    (hD : 0 < D) (hb : |b| ≤ D) : 1 / D ≤ |a| := by
  apply (div_le_iff₀ hD).mpr
  exact hprod.trans (mul_le_mul_of_nonneg_left hb (abs_nonneg a))

/-- Explicit Diophantine bound for `v_r = (1,1-sqrt 2)` in the L1 length.
@isnad1 id=le.1h2v.s6.44ea1298d13b from=translated src=- shape=78c5d046 vocab=e0226bb6
-/
theorem radial_diophantine_l1 (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    (1 / 3 : ℝ) / (1 + frequencyL1 m n) ≤ |radialSymbol m n| := by
  rw [div_div]
  apply lower_of_conjugate_bound (radial_product_lower m n hmn)
  · have := frequencyL1_nonneg m n
    positivity
  · have := radialConjugate_upper m n
    linarith

/-- Explicit Diophantine bound for `v_t = (sqrt 2-1,1)` in the L1 length.
@isnad1 id=le.1h2v.s6.58eae3494ac1 from=translated src=- shape=78c5d046 vocab=4faecdae
-/
theorem time_diophantine_l1 (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    (1 / 3 : ℝ) / (1 + frequencyL1 m n) ≤ |timeSymbol m n| := by
  rw [div_div]
  apply lower_of_conjugate_bound (time_product_lower m n hmn)
  · have := frequencyL1_nonneg m n
    positivity
  · have := timeConjugate_upper m n
    linarith

/-- The manuscript's estimate with an explicit constant and Euclidean length.
@isnad1 id=le.1h2v.s6.5f8bad990082 from=translated src=- shape=78c5d046 vocab=aba1609f
-/
theorem radial_diophantine (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    (1 / 6 : ℝ) / (1 + frequencyLength m n) ≤ |radialSymbol m n| := by
  rw [div_div]
  apply lower_of_conjugate_bound (radial_product_lower m n hmn)
  · have := frequencyLength_nonneg m n
    positivity
  · have := radialConjugate_upper m n
    have := frequencyL1_le_twice_length m n
    linarith

/-- The manuscript's estimate for the second graph direction.
@isnad1 id=le.1h2v.s6.146a626b6340 from=translated src=- shape=78c5d046 vocab=938f991c
-/
theorem time_diophantine (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    (1 / 6 : ℝ) / (1 + frequencyLength m n) ≤ |timeSymbol m n| := by
  rw [div_div]
  apply lower_of_conjugate_bound (time_product_lower m n hmn)
  · have := frequencyLength_nonneg m n
    positivity
  · have := timeConjugate_upper m n
    have := frequencyL1_le_twice_length m n
    linarith

/--
@isnad1 id=ne.1h2v.s5.69cf727f2f92 from=translated src=- shape=100f4671 vocab=143b2140
-/
theorem radialSymbol_ne_zero (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    radialSymbol m n ≠ 0 := by
  intro hz
  have h := radial_product_lower m n hmn
  norm_num [hz] at h

/--
@isnad1 id=ne.1h2v.s5.5ad60319eda4 from=translated src=- shape=100f4671 vocab=2f668ab8
-/
theorem timeSymbol_ne_zero (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    timeSymbol m n ≠ 0 := by
  intro hz
  have h := time_product_lower m n hmn
  norm_num [hz] at h

/-- The radial inverse Fourier multiplier grows at most linearly in frequency.
@isnad1 id=le.1h2v.s6.db7957a649b6 from=translated src=- shape=349d35a0 vocab=4ff4e830
-/
theorem radial_reciprocal_bound (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    |1 / radialSymbol m n| ≤ 6 * (1 + frequencyLength m n) := by
  rw [abs_div, abs_one]
  apply (div_le_iff₀ (abs_pos.mpr (radialSymbol_ne_zero m n hmn))).mpr
  have hb : |radialConjugate m n| ≤ 6 * (1 + frequencyLength m n) := by
    have := radialConjugate_upper m n
    have := frequencyL1_le_twice_length m n
    linarith
  calc
    1 ≤ |radialSymbol m n| * |radialConjugate m n| := radial_product_lower m n hmn
    _ ≤ |radialSymbol m n| * (6 * (1 + frequencyLength m n)) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

/-- The temporal inverse Fourier multiplier grows at most linearly in frequency.
@isnad1 id=le.1h2v.s6.451363e65b7c from=translated src=- shape=349d35a0 vocab=0793a02d
-/
theorem time_reciprocal_bound (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) :
    |1 / timeSymbol m n| ≤ 6 * (1 + frequencyLength m n) := by
  rw [abs_div, abs_one]
  apply (div_le_iff₀ (abs_pos.mpr (timeSymbol_ne_zero m n hmn))).mpr
  have hb : |timeConjugate m n| ≤ 6 * (1 + frequencyLength m n) := by
    have := timeConjugate_upper m n
    have := frequencyL1_le_twice_length m n
    linarith
  calc
    1 ≤ |timeSymbol m n| * |timeConjugate m n| := time_product_lower m n hmn
    _ ≤ |timeSymbol m n| * (6 * (1 + frequencyLength m n)) :=
      mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by ring

/-- Repeated radial inversion has the corresponding finite polynomial loss.
@isnad1 id=le.1h3v.s6.22cc648978cc from=translated src=- shape=62518f23 vocab=8092cd83
-/
theorem radial_inverse_power_bound (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) (p : ℕ) :
    |1 / radialSymbol m n| ^ p ≤ (6 * (1 + frequencyLength m n)) ^ p := by
  exact pow_le_pow_left₀ (abs_nonneg _) (radial_reciprocal_bound m n hmn) p

/-- Repeated temporal inversion has the corresponding finite polynomial loss.
@isnad1 id=le.1h3v.s6.e43c35b4bc1e from=translated src=- shape=62518f23 vocab=ca3d75e4
-/
theorem time_inverse_power_bound (m n : ℤ) (hmn : m ≠ 0 ∨ n ≠ 0) (p : ℕ) :
    |1 / timeSymbol m n| ^ p ≤ (6 * (1 + frequencyLength m n)) ^ p := by
  exact pow_le_pow_left₀ (abs_nonneg _) (time_reciprocal_bound m n hmn) p

/-- Both estimates packaged for a nonzero integer vector.
@isnad1 id=and.1h1v.s7.8af201f6192f from=translated src=- shape=0946d57b vocab=cb90e527
-/
theorem graph_directions_diophantine (k : ℤ × ℤ) (hk : k ≠ 0) :
    (1 / 6 : ℝ) / (1 + frequencyLength k.1 k.2) ≤
        |(k.1 : ℝ) + (1 - Real.sqrt 2) * (k.2 : ℝ)| ∧
      (1 / 6 : ℝ) / (1 + frequencyLength k.1 k.2) ≤
        |(Real.sqrt 2 - 1) * (k.1 : ℝ) + (k.2 : ℝ)| := by
  have hmn : k.1 ≠ 0 ∨ k.2 ≠ 0 := by
    by_cases hm : k.1 = 0
    · right
      intro hn
      exact hk (Prod.ext hm hn)
    · exact Or.inl hm
  constructor
  · simpa only [radialSymbol_formula] using radial_diophantine k.1 k.2 hmn
  · simpa only [timeSymbol_formula] using time_diophantine k.1 k.2 hmn

/-- The integer matrix `[[3,1],[1,5]]` acting on a frequency. -/
def coveringFrequency (k : ℤ × ℤ) : ℤ × ℤ :=
  (3 * k.1 + k.2, k.1 + 5 * k.2)

/--
@isnad1 id=injectiv.0h0v.s3.97047aff7f83 from=translated src=- shape=31244855 vocab=fb5a59c1
-/
theorem coveringFrequency_injective : Function.Injective coveringFrequency := by
  intro k l hkl
  have h₁ := congrArg Prod.fst hkl
  have h₂ := congrArg Prod.snd hkl
  simp only [coveringFrequency] at h₁ h₂
  apply Prod.ext <;> linarith

/--
@isnad1 id=ne.1h1v.s5.6560cd5c87e1 from=translated src=- shape=429dfbad vocab=9928dff9
-/
theorem coveringFrequency_ne_zero (k : ℤ × ℤ) (hk : k ≠ 0) :
    coveringFrequency k ≠ 0 := by
  intro hz
  apply hk
  apply coveringFrequency_injective
  simpa [coveringFrequency] using hz

/-- The radial symbol scales by the smaller eigenvalue of the covering matrix.
@isnad1 id=eq.0h1v.s5.af5b6136912f from=translated src=- shape=b776de6e vocab=fcc8b1f7
-/
theorem radial_symbol_covering (k : ℤ × ℤ) :
    radialSymbol (coveringFrequency k).1 (coveringFrequency k).2 =
      (4 - Real.sqrt 2) * radialSymbol k.1 k.2 := by
  simp only [coveringFrequency, radialSymbol_formula, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat]
  nlinarith [congrArg (fun x : ℝ => x * (k.2 : ℝ)) sqrt_two_square]

/-- The temporal symbol scales by the larger eigenvalue of the covering matrix.
@isnad1 id=eq.0h1v.s5.c5ac168804bd from=translated src=- shape=b776de6e vocab=d45abe8a
-/
theorem time_symbol_covering (k : ℤ × ℤ) :
    timeSymbol (coveringFrequency k).1 (coveringFrequency k).2 =
      (4 + Real.sqrt 2) * timeSymbol k.1 k.2 := by
  simp only [coveringFrequency, timeSymbol_formula, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat]
  nlinarith [congrArg (fun x : ℝ => x * (k.1 : ℝ)) sqrt_two_square]

/--
@isnad1 id=and.0h0v.s6.37bee058a2b0 from=translated src=- shape=3a02ad2e vocab=bc491239
-/
theorem covering_eigenvalues_gt_one :
    1 < 4 - Real.sqrt 2 ∧ 1 < 4 + Real.sqrt 2 := by
  constructor <;> nlinarith [sqrt_two_le_two, Real.sqrt_nonneg (2 : ℝ)]

end NavierStokes.DiophantineGraph

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.TorusInverse

open scoped BigOperators Topology ContDiff

/-- Frequency: an abbreviation for `ℤ × ℤ`. -/
abbrev Frequency := ℤ × ℤ
/-- Plane: an abbreviation for `ℝ × ℝ`. -/
abbrev Plane := ℝ × ℝ

/-- Weight, given by `1 + |(k.1 : ℝ)| + |(k.2 : ℝ)|`. -/
def weight (k : Frequency) : ℝ := 1 + |(k.1 : ℝ)| + |(k.2 : ℝ)|

/--
@isnad1 id=lt.0h1v.s3.2170fc879f6c from=translated src=- shape=b9369acb vocab=16d2d36f
-/
theorem weight_pos (k : Frequency) : 0 < weight k := by
  unfold weight
  positivity

/-- Polynomially weighted absolute summability of every order. -/
def Rapid (a : Frequency → ℂ) : Prop :=
  ∀ p : ℕ, Summable (fun k => weight k ^ p * ‖a k‖)

/--
@isnad1 id=summable.1h1v.s4.29e2b93f05da from=translated src=- shape=664ae3b2 vocab=cc000e1a
-/
theorem Rapid.summable_norm {a : Frequency → ℂ} (ha : Rapid a) :
    Summable (fun k => ‖a k‖) := by
  simpa using ha 0

/--
@isnad1 id=rapid.2h3v.s5.bfda7ee0c306 from=translated src=- shape=2d22426b vocab=b310df38
-/
theorem Rapid.mul_linear {a b : Frequency → ℂ} (ha : Rapid a) (C : ℝ)
    (hb : ∀ k, ‖b k‖ ≤ C * weight k) : Rapid (fun k => b k * a k) := by
  intro p
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (weight_pos k).le _) (norm_nonneg _)) _
    ((ha (p + 1)).mul_left C)
  intro k
  calc
    weight k ^ p * ‖b k * a k‖ = weight k ^ p * (‖b k‖ * ‖a k‖) := by rw [norm_mul]
    _ ≤ weight k ^ p * ((C * weight k) * ‖a k‖) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (weight_pos k).le _)
      exact mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _)
    _ = C * (weight k ^ (p + 1) * ‖a k‖) := by rw [pow_succ]; ring

/-- Omega, given by `2 * Real.pi * Complex.I`. -/
def omega : ℂ := 2 * Real.pi * Complex.I

/-- Freq X, given by `omega * (k.1 : ℂ)`. -/
def freqX (k : Frequency) : ℂ := omega * (k.1 : ℂ)
/-- Freq Y, given by `omega * (k.2 : ℂ)`. -/
def freqY (k : Frequency) : ℂ := omega * (k.2 : ℂ)

/-- Dx, given by `ContinuousLinearMap.fst ℝ ℝ ℝ`. -/
def dx : Plane →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
/-- Dy, given by `ContinuousLinearMap.snd ℝ ℝ ℝ`. -/
def dy : Plane →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ

/-- Lift X, given by `ContinuousLinearMap.smulRightL ℝ Plane ℂ dx`. -/
def liftX : ℂ →L[ℝ] (Plane →L[ℝ] ℂ) := ContinuousLinearMap.smulRightL ℝ Plane ℂ dx
/-- Lift Y, given by `ContinuousLinearMap.smulRightL ℝ Plane ℂ dy`. -/
def liftY : ℂ →L[ℝ] (Plane →L[ℝ] ℂ) := ContinuousLinearMap.smulRightL ℝ Plane ℂ dy

/--
@isnad1 id=eq.0h2v.s10.d8ad80fbcf38 from=translated src=- shape=1b55859c vocab=1f791687
-/
@[simp] theorem liftX_apply (c : ℂ) (x : Plane) : liftX c x = x.1 • c := rfl
/--
@isnad1 id=eq.0h2v.s10.f32e19fe663f from=translated src=- shape=1b55859c vocab=55c66ee4
-/
@[simp] theorem liftY_apply (c : ℂ) (x : Plane) : liftY c x = x.2 • c := rfl

/-- Phase, given by `liftX (freqX k) + liftY (freqY k)`. -/
def phase (k : Frequency) : Plane →L[ℝ] ℂ := liftX (freqX k) + liftY (freqY k)

/-- Mode, given by `Complex.exp (phase k x)`. -/
def mode (k : Frequency) (x : Plane) : ℂ := Complex.exp (phase k x)

/--
@isnad1 id=eq.0h2v.s7.34f546f95fc9 from=translated src=- shape=97a4de90 vocab=77eeda8e
-/
theorem phase_formula (k : Frequency) (x : Plane) :
    phase k x = omega * ((k.1 : ℂ) * (x.1 : ℂ) + (k.2 : ℂ) * (x.2 : ℂ)) := by
  simp only [phase, freqX, freqY, add_apply,
    liftX_apply, liftY_apply, Complex.real_smul]
  ring

/--
@isnad1 id=eq.0h2v.s4.e32a023ecc40 from=translated src=- shape=2f019d02 vocab=e53a6b06
-/
theorem norm_mode (k : Frequency) (x : Plane) : ‖mode k x‖ = 1 := by
  rw [mode, Complex.norm_exp, phase_formula]
  simp [omega, Complex.mul_re, Complex.mul_im]

/--
@isnad1 id=continuo.0h1v.s5.915492749aa1 from=translated src=- shape=7000f90d vocab=6313df21
-/
theorem continuous_mode (k : Frequency) : Continuous (mode k) :=
  Complex.continuous_exp.comp (phase k).continuous

/-- Deriv X, given by `freqX k * a k`. -/
def derivX (a : Frequency → ℂ) (k : Frequency) : ℂ := freqX k * a k
/-- Deriv Y, given by `freqY k * a k`. -/
def derivY (a : Frequency → ℂ) (k : Frequency) : ℂ := freqY k * a k

/--
@isnad1 id=le.0h1v.s4.c7945ef966cb from=translated src=- shape=d9f6a7ea vocab=b33ed273
-/
theorem norm_freqX_le (k : Frequency) : ‖freqX k‖ ≤ ‖omega‖ * weight k := by
  rw [freqX, norm_mul, Complex.norm_intCast]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold weight
  have := abs_nonneg (k.2 : ℝ)
  linarith

/--
@isnad1 id=le.0h1v.s4.3eb6ea15653f from=translated src=- shape=d9f6a7ea vocab=d7834f85
-/
theorem norm_freqY_le (k : Frequency) : ‖freqY k‖ ≤ ‖omega‖ * weight k := by
  rw [freqY, norm_mul, Complex.norm_intCast]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  unfold weight
  have := abs_nonneg (k.1 : ℝ)
  linarith

/--
@isnad1 id=rapid.1h1v.s3.d3a51f13e31d from=translated src=- shape=b6154235 vocab=33fdde5c
-/
theorem Rapid.derivX {a : Frequency → ℂ} (ha : Rapid a) : Rapid (derivX a) :=
  ha.mul_linear ‖omega‖ norm_freqX_le

/--
@isnad1 id=rapid.1h1v.s3.47baad136a9b from=translated src=- shape=b6154235 vocab=ae876eb3
-/
theorem Rapid.derivY {a : Frequency → ℂ} (ha : Rapid a) : Rapid (derivY a) :=
  ha.mul_linear ‖omega‖ norm_freqY_le

/-- Series, given by `∑' k, a k * mode k x`. -/
def series (a : Frequency → ℂ) (x : Plane) : ℂ := ∑' k, a k * mode k x

/--
@isnad1 id=summable.1h2v.s5.2d30b8c1b431 from=translated src=- shape=3ed12820 vocab=c010d94a
-/
theorem summable_terms {a : Frequency → ℂ} (ha : Rapid a) (x : Plane) :
    Summable (fun k => a k * mode k x) := by
  apply Summable.of_norm
  simpa only [norm_mul, norm_mode, mul_one] using ha.summable_norm

/--
@isnad1 id=continuo.1h1v.s5.e7f7671eb7c4 from=translated src=- shape=0540daae vocab=1c475abf
-/
theorem continuous_series {a : Frequency → ℂ} (ha : Rapid a) : Continuous (series a) := by
  apply continuous_tsum (fun k => continuous_const.fun_mul (continuous_mode k)) ha.summable_norm
  intro k x
  simp only [norm_mul, norm_mode, mul_one, le_refl]

/-- Term derivative, given by `liftX (derivX a k * mode k x) + liftY (derivY a k * mode k x)`. -/
def termDeriv (a : Frequency → ℂ) (k : Frequency) (x : Plane) : Plane →L[ℝ] ℂ :=
  liftX (derivX a k * mode k x) + liftY (derivY a k * mode k x)

/--
@isnad1 id=hasfderi.0h3v.s6.f22b98d19f3b from=translated src=- shape=6e988d9f vocab=08c12949
-/
theorem hasFDerivAt_term (a : Frequency → ℂ) (k : Frequency) (x : Plane) :
    HasFDerivAt (fun y => a k * mode k y) (termDeriv a k x) x := by
  have h := ((phase k).hasFDerivAt (x := x)).cexp.const_mul (a k)
  have hd : termDeriv a k x = a k • (Complex.exp (phase k x) • phase k) := by
    apply ContinuousLinearMap.ext
    intro y
    simp only [termDeriv, phase, derivX, derivY, liftX_apply, liftY_apply,
      add_apply, smul_apply,
      Complex.real_smul, smul_eq_mul, mode]
    ring
  simpa only [mode, hd] using h

/-- Derivative majorant, given by `‖liftX‖ * ‖derivX a k‖ + ‖liftY‖ * ‖derivY a k‖`. -/
def derivativeMajorant (a : Frequency → ℂ) (k : Frequency) : ℝ :=
  ‖liftX‖ * ‖derivX a k‖ + ‖liftY‖ * ‖derivY a k‖

/--
@isnad1 id=summable.1h1v.s4.75a65b78476b from=translated src=- shape=609b8b17 vocab=3e92ae61
-/
theorem summable_derivativeMajorant {a : Frequency → ℂ} (ha : Rapid a) :
    Summable (derivativeMajorant a) :=
  (ha.derivX.summable_norm.mul_left ‖liftX‖).add
    (ha.derivY.summable_norm.mul_left ‖liftY‖)

/--
@isnad1 id=le.0h3v.s7.a7801a24f42c from=translated src=- shape=abd0d9ee vocab=5d4b9841
-/
theorem norm_termDeriv_le (a : Frequency → ℂ) (k : Frequency) (x : Plane) :
    ‖termDeriv a k x‖ ≤ derivativeMajorant a k := by
  apply (norm_add_le _ _).trans
  apply add_le_add
  · simpa only [norm_mul, norm_mode, mul_one] using
      liftX.le_opNorm (derivX a k * mode k x)
  · simpa only [norm_mul, norm_mode, mul_one] using
      liftY.le_opNorm (derivY a k * mode k x)

/--
@isnad1 id=summable.1h2v.s8.c3f85c116a38 from=translated src=- shape=b623ffb2 vocab=9f2dbcc9
-/
theorem summable_termDeriv {a : Frequency → ℂ} (ha : Rapid a) (x : Plane) :
    Summable (fun k => termDeriv a k x) :=
  Summable.of_norm_bounded (summable_derivativeMajorant ha) (fun k => norm_termDeriv_le a k x)

/--
@isnad1 id=hasfderi.1h2v.s8.a92b4254cf9a from=translated src=- shape=7c01b3bf vocab=c65111a8
-/
theorem hasFDerivAt_series {a : Frequency → ℂ} (ha : Rapid a) (x : Plane) :
    HasFDerivAt (series a) (∑' k, termDeriv a k x) x := by
  exact hasFDerivAt_tsum (summable_derivativeMajorant ha) (hasFDerivAt_term a)
    (norm_termDeriv_le a) (summable_terms ha (0 : Plane)) x

/--
@isnad1 id=eq.1h2v.s11.266922b891c2 from=translated src=- shape=8209f8cc vocab=da095121
-/
theorem fderiv_series {a : Frequency → ℂ} (ha : Rapid a) (x : Plane) :
    fderiv ℝ (series a) x = liftX (series (derivX a) x) + liftY (series (derivY a) x) := by
  rw [(hasFDerivAt_series ha x).fderiv]
  have hx := liftX.summable (summable_terms ha.derivX x)
  have hy := liftY.summable (summable_terms ha.derivY x)
  rw [show (fun k => termDeriv a k x) =
    (fun k => liftX (derivX a k * mode k x) + liftY (derivY a k * mode k x)) from rfl]
  rw [Summable.tsum_add hx hy, ← liftX.map_tsum (summable_terms ha.derivX x),
    ← liftY.map_tsum (summable_terms ha.derivY x)]
  rfl

/-- Smoothness is proved from summability and termwise differentiation.
@isnad1 id=contdiff.1h2v.s6.55a2efae41c8 from=translated src=- shape=9f0191cb vocab=bec83831
-/
theorem contDiff_series_nat (p : ℕ) {a : Frequency → ℂ} (ha : Rapid a) :
    ContDiff ℝ p (series a) := by
  induction p generalizing a with
  | zero => exact contDiff_zero.mpr (continuous_series ha)
  | succ p ih =>
    rw [show ((p + 1 : ℕ) : WithTop ℕ∞) = (p : WithTop ℕ∞) + 1 by simp,
      contDiff_succ_iff_fderiv]
    refine ⟨(fun x => (hasFDerivAt_series ha x).differentiableAt), ?_, ?_⟩
    · simp
    · have heq : fderiv ℝ (series a) =
          (fun x => liftX (series (derivX a) x) + liftY (series (derivY a) x)) :=
        funext (fderiv_series ha)
      rw [heq]
      exact (liftX.contDiff.comp (ih ha.derivX)).add (liftY.contDiff.comp (ih ha.derivY))

/--
@isnad1 id=contdiff.1h1v.s6.c723b8918c15 from=translated src=- shape=c73f30dd vocab=42046f1f
-/
theorem contDiff_series {a : Frequency → ℂ} (ha : Rapid a) :
    ContDiff ℝ ∞ (series a) :=
  contDiff_infty.mpr (fun p => contDiff_series_nat p ha)

/-- Direction data for torus inverse. -/
inductive Direction
  | radial
  | temporal
  deriving DecidableEq

/-- Vector as an element of `Direction → Plane | .radial => (1, 1 - Real.sqrt 2) | .temporal =>
(Real.sqrt 2 - 1, 1)`. -/
def vector : Direction → Plane
  | .radial => (1, 1 - Real.sqrt 2)
  | .temporal => (Real.sqrt 2 - 1, 1)

/-- Symbol as an element of `Direction → Frequency → ℝ | .radial, k =>
DiophantineGraph.radialSymbol k.1 k.2 | .temporal, k => DiophantineGraph.timeSymbol k.1
k.2`. -/
def symbol : Direction → Frequency → ℝ
  | .radial, k => DiophantineGraph.radialSymbol k.1 k.2
  | .temporal, k => DiophantineGraph.timeSymbol k.1 k.2

/--
@isnad1 id=or.1h1v.s5.b91bd833a4bf from=translated src=- shape=c53da899 vocab=22e06738
-/
theorem pair_nonzero {k : Frequency} (hk : k ≠ 0) : k.1 ≠ 0 ∨ k.2 ≠ 0 := by
  by_cases h₁ : k.1 = 0
  · right
    intro h₂
    exact hk (Prod.ext h₁ h₂)
  · exact Or.inl h₁

/--
@isnad1 id=eq.0h2v.s5.fd60c31db0ab from=translated src=- shape=f0672143 vocab=7d08491c
-/
theorem symbol_formula (d : Direction) (k : Frequency) :
    symbol d k = (k.1 : ℝ) * (vector d).1 + (k.2 : ℝ) * (vector d).2 := by
  cases d <;> simp only [symbol, vector, DiophantineGraph.radialSymbol_formula,
    DiophantineGraph.timeSymbol_formula] <;> ring

/--
@isnad1 id=ne.1h2v.s5.7aaf14609d78 from=translated src=- shape=01861076 vocab=890e2d45
-/
theorem symbol_ne_zero (d : Direction) {k : Frequency} (hk : k ≠ 0) : symbol d k ≠ 0 := by
  cases d
  · exact DiophantineGraph.radialSymbol_ne_zero k.1 k.2 (pair_nonzero hk)
  · exact DiophantineGraph.timeSymbol_ne_zero k.1 k.2 (pair_nonzero hk)

/--
@isnad1 id=le.0h1v.s4.5e772d949bc1 from=translated src=- shape=6551cedc vocab=ec0eed21
-/
theorem length_le_weight (k : Frequency) :
    1 + DiophantineGraph.frequencyLength k.1 k.2 ≤ weight k := by
  have hs := DiophantineGraph.frequencyLength_nonneg k.1 k.2
  have hsq : DiophantineGraph.frequencyLength k.1 k.2 ^ 2 =
      (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2 := Real.sq_sqrt (by positivity)
  have ht : DiophantineGraph.frequencyLength k.1 k.2 ≤
      |(k.1 : ℝ)| + |(k.2 : ℝ)| := by
    apply (sq_le_sq₀ hs (by positivity)).mp
    rw [hsq]
    nlinarith [sq_abs (k.1 : ℝ), sq_abs (k.2 : ℝ),
      mul_nonneg (abs_nonneg (k.1 : ℝ)) (abs_nonneg (k.2 : ℝ))]
  unfold weight
  linarith

/--
@isnad1 id=le.1h2v.s6.2135d7613c16 from=translated src=- shape=62b60eb5 vocab=c2e6a27d
-/
theorem reciprocal_symbol_bound (d : Direction) {k : Frequency} (hk : k ≠ 0) :
    |1 / symbol d k| ≤ 6 * weight k := by
  have hb : |1 / symbol d k| ≤
      6 * (1 + DiophantineGraph.frequencyLength k.1 k.2) := by
    cases d
    · exact DiophantineGraph.radial_reciprocal_bound k.1 k.2 (pair_nonzero hk)
    · exact DiophantineGraph.time_reciprocal_bound k.1 k.2 (pair_nonzero hk)
  exact hb.trans (mul_le_mul_of_nonneg_left (length_le_weight k) (by norm_num))

/--
@isnad1 id=ne.0h0v.s3.f472843d6a25 from=translated src=- shape=ffdda526 vocab=a306946c
-/
theorem omega_ne_zero : omega ≠ 0 := by
  unfold omega
  exact mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

/-- Multiplier, given by `(omega * (symbol d k : ℂ))⁻¹`. -/
def multiplier (d : Direction) (k : Frequency) : ℂ := (omega * (symbol d k : ℂ))⁻¹
/-- Inverse coefficient, given by `multiplier d k * a k`. -/
def inverseCoeff (d : Direction) (a : Frequency → ℂ) (k : Frequency) : ℂ :=
  multiplier d k * a k

/--
@isnad1 id=eq.0h1v.s4.1475121a4d69 from=translated src=- shape=59ae2d96 vocab=890e2d45
-/
@[simp] theorem symbol_zero (d : Direction) : symbol d 0 = 0 := by
  cases d <;> simp [symbol, DiophantineGraph.radialSymbol,
    DiophantineGraph.timeSymbol, DiophantineGraph.quadraticForm]

/--
@isnad1 id=eq.0h2v.s5.2dcda46e85c2 from=translated src=- shape=52603019 vocab=ee88b620
-/
@[simp] theorem inverseCoeff_zero (d : Direction) (a : Frequency → ℂ) :
    inverseCoeff d a 0 = 0 := by
  simp [inverseCoeff, multiplier]

/--
@isnad1 id=le.0h2v.s5.0d6b0c50b48b from=translated src=- shape=e557369b vocab=36f76dde
-/
theorem norm_multiplier_le (d : Direction) (k : Frequency) :
    ‖multiplier d k‖ ≤ (6 * ‖omega⁻¹‖) * weight k := by
  by_cases hk : k = 0
  · subst k
    simp only [multiplier, symbol_zero, Complex.ofReal_zero, mul_zero, inv_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (weight_pos _).le
  · have h := reciprocal_symbol_bound d hk
    calc
      ‖multiplier d k‖ = ‖omega⁻¹‖ * |1 / symbol d k| := by
        simp [multiplier, Complex.norm_real, Real.norm_eq_abs,
          abs_inv, one_div, mul_inv_rev, mul_comm]
      _ ≤ ‖omega⁻¹‖ * (6 * weight k) := mul_le_mul_of_nonneg_left h (norm_nonneg _)
      _ = _ := by ring

/--
@isnad1 id=rapid.1h2v.s3.fc7957de7944 from=translated src=- shape=b7d05ace vocab=a2073d3b
-/
theorem Rapid.inverseCoeff {a : Frequency → ℂ} (ha : Rapid a) (d : Direction) :
    Rapid (inverseCoeff d a) := ha.mul_linear (6 * ‖omega⁻¹‖) (norm_multiplier_le d)

/-- The coefficient estimate loses one polynomial frequency weight.
@isnad1 id=le.0h4v.s6.4c9a93216c69 from=translated src=- shape=a05b6edc vocab=4a9f0e0e
-/
theorem inverseCoeff_weighted_bound (d : Direction) (a : Frequency → ℂ)
    (p : ℕ) (k : Frequency) :
    weight k ^ p * ‖inverseCoeff d a k‖ ≤
      (6 * ‖omega⁻¹‖) * (weight k ^ (p + 1) * ‖a k‖) := by
  unfold inverseCoeff
  rw [norm_mul]
  calc
    weight k ^ p * (‖multiplier d k‖ * ‖a k‖) ≤
        weight k ^ p * (((6 * ‖omega⁻¹‖) * weight k) * ‖a k‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (norm_multiplier_le d k) (norm_nonneg _))
        (pow_nonneg (weight_pos k).le p)
    _ = _ := by rw [pow_succ]; ring

/--
@isnad1 id=eq.1h3v.s6.049c7bb23bdc from=translated src=- shape=0c197c95 vocab=c0736460
-/
theorem coefficient_cancel (d : Direction) {a : Frequency → ℂ} (hzero : a 0 = 0)
    (k : Frequency) : omega * (symbol d k : ℂ) * inverseCoeff d a k = a k := by
  by_cases hk : k = 0
  · simp [hk, hzero]
  · have hd : omega * (symbol d k : ℂ) ≠ 0 :=
      mul_ne_zero omega_ne_zero (Complex.ofReal_ne_zero.mpr (symbol_ne_zero d hk))
    change (omega * (symbol d k : ℂ)) * ((omega * (symbol d k : ℂ))⁻¹ * a k) = a k
    rw [← mul_assoc, mul_inv_cancel₀ hd, one_mul]

/-- Directional inverse, given by `series (inverseCoeff d a)`. -/
def directionalInverse (d : Direction) (a : Frequency → ℂ) : Plane → ℂ :=
  series (inverseCoeff d a)

/--
@isnad1 id=contdiff.1h2v.s6.e3f3ed098e0a from=translated src=- shape=add63ec2 vocab=2e7a265b
-/
theorem contDiff_directionalInverse (d : Direction) {a : Frequency → ℂ} (ha : Rapid a) :
    ContDiff ℝ ∞ (directionalInverse d a) := contDiff_series (ha.inverseCoeff d)

/--
@isnad1 id=eq.1h4v.s7.ee83877a6f9e from=translated src=- shape=a272311f vocab=88c96e81
-/
theorem termDeriv_direction (d : Direction) {a : Frequency → ℂ} (hzero : a 0 = 0)
    (k : Frequency) (x : Plane) :
    termDeriv (inverseCoeff d a) k x (vector d) = a k * mode k x := by
  have hs : (symbol d k : ℂ) = (k.1 : ℂ) * ((vector d).1 : ℂ) +
      (k.2 : ℂ) * ((vector d).2 : ℂ) := by
    exact_mod_cast symbol_formula d k
  calc
    termDeriv (inverseCoeff d a) k x (vector d) =
        (omega * (symbol d k : ℂ) * inverseCoeff d a k) * mode k x := by
      rw [hs]
      simp only [termDeriv, add_apply, liftX_apply, liftY_apply,
        derivX, derivY, freqX, freqY, Complex.real_smul]
      ring
    _ = a k * mode k x := by rw [coefficient_cancel d hzero k]

/-- The genuine Fréchet derivative of the smooth inverse solves the equation.
@isnad1 id=eq.2h3v.s8.fe6d483fa644 from=translated src=- shape=edc15ea8 vocab=0c57d1a4
-/
theorem directionalInverse_solves (d : Direction) {a : Frequency → ℂ}
    (ha : Rapid a) (hzero : a 0 = 0) (x : Plane) :
    fderiv ℝ (directionalInverse d a) x (vector d) = series a x := by
  unfold directionalInverse
  rw [(hasFDerivAt_series (ha.inverseCoeff d) x).fderiv]
  calc
    (∑' k, termDeriv (inverseCoeff d a) k x) (vector d) =
        ∑' k, termDeriv (inverseCoeff d a) k x (vector d) :=
      (ContinuousLinearMap.apply ℝ ℂ (vector d)).map_tsum
        (summable_termDeriv (ha.inverseCoeff d) x)
    _ = series a x := tsum_congr (fun k => termDeriv_direction d hzero k x)

/-! ## Descent to the torus and actual Haar means -/

open MeasureTheory
/--
@isnad1 id=fact.0h0v.s4.1bbad66aac21 from=translated src=- shape=3a68cc91 vocab=2163b268
-/
local instance instTorusInverse1 : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

/-- Torus: an abbreviation for `UnitAddCircle × UnitAddCircle`. -/
abbrev Torus := UnitAddCircle × UnitAddCircle

/-- Torus measure as an element of `Measure Torus`. -/
def torusMeasure : Measure Torus :=
  (AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle

instance : IsProbabilityMeasure torusMeasure := by
  unfold torusMeasure
  infer_instance

/-- Torus mode, bundling `toFun`, `continuous_toFun`. -/
def torusMode (k : Frequency) : C(Torus, ℂ) where
  toFun z := fourier k.1 z.1 * fourier k.2 z.2
  continuous_toFun := ((fourier k.1).continuous.comp continuous_fst).mul
    ((fourier k.2).continuous.comp continuous_snd)

/--
@isnad1 id=eq.0h2v.s7.ebf90ecb1941 from=translated src=- shape=0db9eb06 vocab=a5392ee3
-/
theorem norm_torusMode (k : Frequency) (z : Torus) : ‖torusMode k z‖ = 1 := by
  simp [torusMode, fourier_apply, Circle.norm_coe]

/-- Torus series, given by `∑' k, a k * torusMode k z`. -/
def torusSeries (a : Frequency → ℂ) (z : Torus) : ℂ := ∑' k, a k * torusMode k z

/--
@isnad1 id=eq.0h2v.s7.54637cba6a9b from=translated src=- shape=1b182ce0 vocab=73e56ded
-/
theorem mode_eq_torusMode (k : Frequency) (x : Plane) :
    mode k x = torusMode k ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle)) := by
  change Complex.exp (phase k x) =
    fourier k.1 (x.1 : UnitAddCircle) * fourier k.2 (x.2 : UnitAddCircle)
  rw [phase_formula, fourier_coe_apply, fourier_coe_apply, ← Complex.exp_add]
  congr 1
  simp only [Complex.ofReal_one, div_one, omega]
  ring

/--
@isnad1 id=eq.0h2v.s5.cceaa3eb520e from=translated src=- shape=eee98095 vocab=b0baeb67
-/
theorem series_eq_torusSeries (a : Frequency → ℂ) (x : Plane) :
    series a x = torusSeries a ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle)) :=
  tsum_congr (fun k => congrArg (fun z => a k * z) (mode_eq_torusMode k x))

/--
@isnad1 id=eq.0h1v.s7.32e70e6043b4 from=translated src=- shape=9b9a1b2b vocab=d40951a0
-/
theorem circle_int_eq_zero (m : ℤ) : (((m : ℝ) : UnitAddCircle)) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨m, by simp⟩

/-- Integer translation invariance is actual descent to `(ℝ/ℤ)²`.
@isnad1 id=eq.0h4v.s5.6ffa34865d55 from=translated src=- shape=f0c370b1 vocab=610c769b
-/
theorem series_periodic (a : Frequency → ℂ) (x : Plane) (m n : ℤ) :
    series a (x.1 + m, x.2 + n) = series a x := by
  rw [series_eq_torusSeries, series_eq_torusSeries]
  simp only [AddCircle.coe_add, circle_int_eq_zero, add_zero]

/--
@isnad1 id=continuo.1h1v.s6.764cacd36827 from=translated src=- shape=0540daae vocab=1cc35bcb
-/
theorem continuous_torusSeries {a : Frequency → ℂ} (ha : Rapid a) :
    Continuous (torusSeries a) := by
  apply continuous_tsum (fun k => continuous_const.fun_mul (torusMode k).continuous)
      ha.summable_norm
  intro k z
  simp only [norm_mul, norm_torusMode, mul_one, le_refl]

/--
@isnad1 id=eq.0h1v.s7.5c0fca0ae013 from=translated src=- shape=251f47d1 vocab=ee7f06ea
-/
theorem integral_fourier (n : ℤ) :
    (∫ z : UnitAddCircle, fourier n z ∂AddCircle.haarAddCircle) =
      if n = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (orthonormal_fourier (T := (1 : ℝ)))) 0 n
  rw [ContinuousMap.inner_toLp] at h
  simpa [fourier_zero, eq_comm] using h

/--
@isnad1 id=eq.0h1v.s7.d8670940f7e0 from=translated src=- shape=79a6e711 vocab=ccdae5d5
-/
theorem integral_torusMode (k : Frequency) :
    (∫ z, torusMode k z ∂torusMeasure) = if k = 0 then 1 else 0 := by
  change (∫ z : Torus, fourier k.1 z.1 * fourier k.2 z.2
    ∂(AddCircle.haarAddCircle : Measure UnitAddCircle).prod AddCircle.haarAddCircle) = _
  rw [integral_prod_mul, integral_fourier, integral_fourier]
  by_cases h₁ : k.1 = 0 <;> by_cases h₂ : k.2 = 0 <;>
    simp [h₁, h₂, Prod.ext_iff]

/--
@isnad1 id=integrab.0h2v.s7.ff651130c6dc from=translated src=- shape=1159867d vocab=8c7f0ab4
-/
theorem integrable_torusTerm (a : Frequency → ℂ) (k : Frequency) :
    Integrable (fun z => a k * torusMode k z) torusMeasure := by
  apply (integrable_const (‖a k‖ : ℝ)).mono'
    (continuous_const.fun_mul (torusMode k).continuous).aestronglyMeasurable
  filter_upwards with z
  simp only [norm_mul, norm_torusMode, mul_one, le_refl]

/-- The zeroth coefficient equals the actual normalized Haar integral.
@isnad1 id=eq.1h1v.s6.94f1f65331c6 from=translated src=- shape=d05a84fa vocab=5fd2319a
-/
theorem integral_torusSeries {a : Frequency → ℂ} (ha : Rapid a) :
    (∫ z, torusSeries a z ∂torusMeasure) = a 0 := by
  have hsum : Summable (fun k => ∫ z, ‖a k * torusMode k z‖ ∂torusMeasure) := by
    simpa only [norm_mul, norm_torusMode, mul_one, integral_const,
      probReal_univ, one_smul] using ha.summable_norm
  unfold torusSeries
  rw [← integral_tsum_of_summable_integral_norm (integrable_torusTerm a) hsum]
  simp only [integral_const_mul, integral_torusMode]
  simp only [mul_ite, mul_one, mul_zero]
  rw [tsum_eq_single (0 : Frequency) (fun i hi => by simp [hi])]
  simp

/-- Weighted absolute Fourier coefficient seminorm. -/
def coeffSeminorm (p : ℕ) (a : Frequency → ℂ) : ℝ :=
  ∑' k, weight k ^ p * ‖a k‖

/--
@isnad1 id=le.1h3v.s5.b604d78014f8 from=translated src=- shape=b63fa775 vocab=7d05e7c8
-/
theorem inverseCoeff_seminorm_le (d : Direction) {a : Frequency → ℂ}
    (ha : Rapid a) (p : ℕ) :
    coeffSeminorm p (inverseCoeff d a) ≤ (6 * ‖omega⁻¹‖) * coeffSeminorm (p + 1) a := by
  have h := (ha.inverseCoeff d p).tsum_le_tsum (inverseCoeff_weighted_bound d a p)
    ((ha (p + 1)).mul_left (6 * ‖omega⁻¹‖))
  simpa only [coeffSeminorm, tsum_mul_left] using h

/--
@isnad1 id=le.1h2v.s4.14dd5112c9f9 from=translated src=- shape=a849f6d5 vocab=cb03bc6c
-/
theorem norm_series_le {a : Frequency → ℂ} (ha : Rapid a) (x : Plane) :
    ‖series a x‖ ≤ coeffSeminorm 0 a := by
  simpa only [series, coeffSeminorm, pow_zero, one_mul, norm_mul, norm_mode, mul_one] using
    norm_tsum_le_tsum_norm (summable_terms ha x).norm

/--
@isnad1 id=le.1h3v.s5.049c6d6e45a2 from=translated src=- shape=f0fab313 vocab=aa93fca9
-/
theorem norm_directionalInverse_le (d : Direction) {a : Frequency → ℂ}
    (ha : Rapid a) (x : Plane) :
    ‖directionalInverse d a x‖ ≤ (6 * ‖omega⁻¹‖) * coeffSeminorm 1 a := by
  exact (norm_series_le (ha.inverseCoeff d) x).trans (inverseCoeff_seminorm_le d ha 0)

/-- Coordinate coefficient, with branches according to `j`. -/
def coordinateCoeff (j : Bool) (a : Frequency → ℂ) : Frequency → ℂ :=
  if j then derivY a else derivX a

/-- Coordinate partial, given by `fderiv ℝ f x (if j then (0, 1) else (1, 0))`. -/
def coordinatePartial (j : Bool) (f : Plane → ℂ) (x : Plane) : ℂ :=
  fderiv ℝ f x (if j then (0, 1) else (1, 0))

/-- Coefficient word as an element of `js, a => coordinateCoeff j (coefficientWord js a)`. -/
def coefficientWord : List Bool → (Frequency → ℂ) → Frequency → ℂ
  | [], a => a
  | j :: js, a => coordinateCoeff j (coefficientWord js a)

/-- Derivative word as an element of `js, f => coordinatePartial j (derivativeWord js f)`. -/
def derivativeWord : List Bool → (Plane → ℂ) → Plane → ℂ
  | [], f => f
  | j :: js, f => coordinatePartial j (derivativeWord js f)

/--
@isnad1 id=rapid.1h2v.s3.bd457acb7b2c from=translated src=- shape=b7d05ace vocab=f3ea18b5
-/
theorem Rapid.coordinateCoeff {a : Frequency → ℂ} (ha : Rapid a) (j : Bool) :
    Rapid (coordinateCoeff j a) := by
  cases j
  · exact ha.derivX
  · exact ha.derivY

/--
@isnad1 id=rapid.1h2v.s3.7031b43cb696 from=translated src=- shape=bfe2fbc8 vocab=69618d93
-/
theorem Rapid.coefficientWord {a : Frequency → ℂ} (ha : Rapid a) (w : List Bool) :
    Rapid (coefficientWord w a) := by
  induction w with
  | nil => exact ha
  | cons j js ih => exact ih.coordinateCoeff j

/--
@isnad1 id=eq.1h2v.s4.c31cb510d62a from=translated src=- shape=1ba9ea67 vocab=e3cde883
-/
theorem coordinatePartial_series (j : Bool) {a : Frequency → ℂ} (ha : Rapid a) :
    coordinatePartial j (series a) = series (coordinateCoeff j a) := by
  funext x
  cases j <;> simp [coordinatePartial, coordinateCoeff, fderiv_series ha,
    liftX_apply, liftY_apply]

/--
@isnad1 id=eq.1h2v.s4.f75181dae492 from=translated src=- shape=225dc232 vocab=c109a6cf
-/
theorem derivativeWord_series (w : List Bool) {a : Frequency → ℂ} (ha : Rapid a) :
    derivativeWord w (series a) = series (coefficientWord w a) := by
  induction w with
  | nil => rfl
  | cons j js ih =>
    simp only [derivativeWord, coefficientWord, ih]
    exact coordinatePartial_series j (ha.coefficientWord js)

/--
@isnad1 id=le.0h3v.s5.4c677d5c2417 from=translated src=- shape=9945e4e2 vocab=b92aa2e0
-/
theorem norm_coordinateCoeff_le (j : Bool) (a : Frequency → ℂ) (k : Frequency) :
    ‖coordinateCoeff j a k‖ ≤ (‖omega‖ * weight k) * ‖a k‖ := by
  cases j
  · exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (norm_freqX_le k) (norm_nonneg _))
  · exact (norm_mul _ _).le.trans (mul_le_mul_of_nonneg_right (norm_freqY_le k) (norm_nonneg _))

/--
@isnad1 id=le.0h3v.s5.0e5566a524a4 from=translated src=- shape=9958b51c vocab=bb6656fe
-/
theorem norm_coefficientWord_le (w : List Bool) (a : Frequency → ℂ) (k : Frequency) :
    ‖coefficientWord w a k‖ ≤ (‖omega‖ * weight k) ^ w.length * ‖a k‖ := by
  induction w with
  | nil => simp [coefficientWord]
  | cons j js ih =>
    calc
      ‖coefficientWord (j :: js) a k‖ ≤
          (‖omega‖ * weight k) * ‖coefficientWord js a k‖ := norm_coordinateCoeff_le _ _ _
      _ ≤ (‖omega‖ * weight k) * ((‖omega‖ * weight k) ^ js.length * ‖a k‖) :=
        mul_le_mul_of_nonneg_left ih (mul_nonneg (norm_nonneg _) (weight_pos k).le)
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

/-- A uniform bound for every actual mixed coordinate derivative of the inverse.
@isnad1 id=le.1h4v.s6.305d5130ad8b from=translated src=- shape=34f9c944 vocab=92c128ac
-/
theorem inverse_derivativeWord_bound (d : Direction) {a : Frequency → ℂ} (ha : Rapid a)
    (w : List Bool) (x : Plane) :
    ‖derivativeWord w (directionalInverse d a) x‖ ≤
      ((6 * ‖omega⁻¹‖) * ‖omega‖ ^ w.length) * coeffSeminorm (w.length + 1) a := by
  have hr := (ha.inverseCoeff d).coefficientWord w
  change ‖derivativeWord w (series (inverseCoeff d a)) x‖ ≤ _
  rw [derivativeWord_series w (ha.inverseCoeff d)]
  apply (norm_series_le hr x).trans
  have hb : ∀ k, ‖coefficientWord w (inverseCoeff d a) k‖ ≤
      ((6 * ‖omega⁻¹‖) * ‖omega‖ ^ w.length) * (weight k ^ (w.length + 1) * ‖a k‖) := by
    intro k
    calc
      ‖coefficientWord w (inverseCoeff d a) k‖ ≤
          (‖omega‖ * weight k) ^ w.length * ‖inverseCoeff d a k‖ := norm_coefficientWord_le _ _ _
      _ ≤ (‖omega‖ * weight k) ^ w.length * (((6 * ‖omega⁻¹‖) * weight k) * ‖a k‖) := by
        apply mul_le_mul_of_nonneg_left _
          (pow_nonneg (mul_nonneg (norm_nonneg _) (weight_pos k).le) _)
        exact (norm_mul _ _).le.trans
          (mul_le_mul_of_nonneg_right (norm_multiplier_le d k) (norm_nonneg _))
      _ = _ := by rw [mul_pow, pow_succ]; ring
  have hs := hr.summable_norm.tsum_le_tsum hb
    ((ha (w.length + 1)).mul_left ((6 * ‖omega⁻¹‖) * ‖omega‖ ^ w.length))
  simpa only [coeffSeminorm, pow_zero, one_mul, tsum_mul_left] using hs

/-! ## Parameters and support -/

/-- Inversion uses only the torus variable and preserves support in every
external parameter. No nonvanishing or convergence hypothesis is needed here.
@isnad1 id=eq.2h6v.s6.52967dab656b from=translated src=- shape=119a1b72 vocab=f6a40d4c
-/
theorem inverse_preserves_parameter_support {P : Type*} (d : Direction)
    (a : P → Frequency → ℂ) (S : Set P)
    (hsupport : ∀ p, p ∉ S → ∀ k, a p k = 0) :
    ∀ p, p ∉ S → ∀ x, directionalInverse d (a p) x = 0 := by
  intro p hp x
  simp [directionalInverse, series, inverseCoeff, hsupport p hp]

/-- The constructed directional inverse has zero normalized Haar mean.
@isnad1 id=eq.1h2v.s6.b0e93ea3eadc from=translated src=- shape=839cb4b3 vocab=52343a94
-/
theorem inverse_zero_mean (d : Direction) {a : Frequency → ℂ} (ha : Rapid a) :
    (∫ z, torusSeries (inverseCoeff d a) z ∂torusMeasure) = 0 := by
  rw [integral_torusSeries (ha.inverseCoeff d), inverseCoeff_zero]

/--
@isnad1 id=eq.0h5v.s5.0acaec2c2cdd from=translated src=- shape=bd0a969c vocab=70389fe8
-/
theorem directionalInverse_periodic (d : Direction) (a : Frequency → ℂ)
    (x : Plane) (m n : ℤ) :
    directionalInverse d a (x.1 + m, x.2 + n) = directionalInverse d a x :=
  series_periodic (inverseCoeff d a) x m n

/-- A zero-average rapidly convergent Fourier series on the actual torus has
a zero-average inverse whose universal-cover lift is smooth and solves the
directional equation. Both manuscript directions are covered.
@isnad1 id=ex.2h2v.s9.b174c6e007ea from=translated src=- shape=55706be0 vocab=10ba5096
-/
theorem zero_mean_series_has_smooth_inverse (d : Direction) {a : Frequency → ℂ}
    (ha : Rapid a) (hmean : (∫ z, torusSeries a z ∂torusMeasure) = 0) :
    ∃ u : Torus → ℂ, Continuous u ∧ (∫ z, u z ∂torusMeasure) = 0 ∧
      ContDiff ℝ ∞ (fun x : Plane => u ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle))) ∧
      ∀ x : Plane,
        fderiv ℝ (fun y : Plane => u ((y.1 : UnitAddCircle), (y.2 : UnitAddCircle)))
          x (vector d) = series a x := by
  have hzero : a 0 = 0 := by rwa [integral_torusSeries ha] at hmean
  have hpull : (fun x : Plane =>
      torusSeries (inverseCoeff d a) ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle))) =
      directionalInverse d a := by
    funext x
    exact (series_eq_torusSeries (inverseCoeff d a) x).symm
  refine ⟨torusSeries (inverseCoeff d a), continuous_torusSeries (ha.inverseCoeff d),
    inverse_zero_mean d ha, ?_, ?_⟩
  · rw [hpull]
    exact contDiff_directionalInverse d ha
  · rw [hpull]
    exact directionalInverse_solves d ha hzero

end NavierStokes.TorusInverse

end
end

end

@[expose] public section

noncomputable section

namespace NavierStokes.SmoothFourierData

open Set Function MeasureTheory TorusInverse
open scoped BigOperators ContDiff Interval Topology

/--
@isnad1 id=fact.0h0v.s4.1bbad66aac21 from=translated src=- shape=3a68cc91 vocab=2163b268
-/
local instance instSmoothFourierData1 : Fact ((0 : ℝ) < 1) := ⟨by norm_num⟩

/-- The actual unit-period Fourier coefficient of a function on the line. -/
def unitCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn (show (0 : ℝ) < 1 by norm_num) f n

/--
@isnad1 id=eq.0h2v.s7.e8809775963e from=translated src=- shape=827864cc vocab=e99ba7d9
-/
theorem unitCoeff_eq_integral (f : ℝ → ℂ) (n : ℤ) :
    unitCoeff f n = ∫ x in (0 : ℝ)..1, fourier (-n) (x : UnitAddCircle) * f x := by
  have h := fourierCoeffOn_eq_integral f n (show (0 : ℝ) < 1 by norm_num)
  simpa [unitCoeff, fourier_coe_apply, smul_eq_mul] using h

/--
@isnad1 id=eq.0h3v.s5.89f3744f9ef7 from=translated src=- shape=0dbce600 vocab=cd59e604
-/
theorem unitCoeff_const_mul (f : ℝ → ℂ) (c : ℂ) (n : ℤ) :
    unitCoeff (fun x => c * f x) n = c * unitCoeff f n :=
  fourierCoeffOn.const_mul f c n (show (0 : ℝ) < 1 by norm_num)

/--
@isnad1 id=le.1h3v.s5.a626711a638a from=translated src=- shape=fd764c3c vocab=8c2de39e
-/
theorem unitCoeff_norm_le {f : ℝ → ℂ} {C : ℝ} (n : ℤ)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ C) : ‖unitCoeff f n‖ ≤ C := by
  rw [unitCoeff_eq_integral]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := C) (f := fun x => fourier (-n) (x : UnitAddCircle) * f x)
    (fun x hx => by
      have hx' : x ∈ Icc (0 : ℝ) 1 := by
        simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using uIoc_subset_uIcc hx
      simpa only [norm_mul, fourier_apply, Circle.norm_coe, one_mul] using hb x hx')
  simpa only [sub_zero, abs_one, mul_one] using h

/-- The boundary term cancels because the actual endpoint values agree.
@isnad1 id=eq.4h3v.s7.c92b023848b3 from=translated src=- shape=9b0cddeb vocab=b23bc559
-/
theorem unitCoeff_of_hasDerivAt {f f' : ℝ → ℂ} {n : ℤ} (hn : n ≠ 0)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f') (hp : f 1 = f 0) :
    unitCoeff f n = (omega * (n : ℂ))⁻¹ * unitCoeff f' n := by
  have h := fourierCoeffOn_of_hasDerivAt (show (0 : ℝ) < 1 by norm_num) hn
    (fun x _ => hd x) (hc.intervalIntegrable 0 1)
  have hden : -2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) = -(omega * (n : ℂ)) := by
    unfold omega
    ring
  simpa only [unitCoeff, hp, sub_self, mul_zero, sub_zero, Complex.ofReal_one,
    Complex.ofReal_zero, one_mul, zero_sub, hden, one_div, inv_neg, neg_mul_neg] using h

/-- Unit-periodicity in both coordinates, expressed on the universal cover. -/
def UnitPeriodic (f : Plane → ℂ) : Prop :=
  ∀ z : Plane, ∀ k : Frequency, f (z + ((k.1 : ℝ), (k.2 : ℝ))) = f z

/-- The genuine first coordinate derivative. -/
noncomputable def partialX (f : Plane → ℂ) (z : Plane) : ℂ := fderiv ℝ f z (1, 0)

/-- X jet, given by `partialX^[p] f`. -/
noncomputable def xJet (p : ℕ) (f : Plane → ℂ) : Plane → ℂ := partialX^[p] f

/--
@isnad1 id=eq.0h1v.s4.efffd6640b82 from=translated src=- shape=cd525ae8 vocab=4fcaa45d
-/
@[simp] theorem xJet_zero (f : Plane → ℂ) : xJet 0 f = f := rfl

/--
@isnad1 id=eq.0h2v.s4.776f930726a6 from=translated src=- shape=390829ef vocab=1c8e9a88
-/
theorem xJet_succ (p : ℕ) (f : Plane → ℂ) : xJet (p + 1) f = partialX (xJet p f) := by
  exact Function.iterate_succ_apply' partialX p f

/--
@isnad1 id=contdiff.1h1v.s7.3305cc3d285b from=translated src=- shape=e9f00064 vocab=15faf97d
-/
theorem partialX_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (partialX f) :=
  (ContinuousLinearMap.apply ℝ ℂ (1, 0)).contDiff.comp
    (hf.fderiv_right (by simp))

/--
@isnad1 id=contdiff.1h2v.s7.c493d4ab418a from=translated src=- shape=2f53c79d vocab=3fcd1d40
-/
theorem xJet_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (p : ℕ) :
    ContDiff ℝ ∞ (xJet p f) := by
  induction p with
  | zero => exact hf
  | succ p ih => rw [xJet_succ]; exact partialX_smooth ih

/--
@isnad1 id=unitperi.1h1v.s3.0d5b32553bc0 from=translated src=- shape=b6154235 vocab=c7aa6819
-/
theorem partialX_periodic {f : Plane → ℂ} (hf : UnitPeriodic f) :
    UnitPeriodic (partialX f) := by
  intro z k
  have hfun : (fun w : Plane => f (w + ((k.1 : ℝ), (k.2 : ℝ)))) = f := funext fun w => hf w k
  have h := congrArg (fun g : Plane → ℂ => fderiv ℝ g z) hfun
  rw [fderiv_comp_add_right] at h
  exact congrArg (fun L : Plane →L[ℝ] ℂ => L (1, 0)) h

/--
@isnad1 id=unitperi.1h2v.s3.8b36e427205a from=translated src=- shape=b7d05ace vocab=44757edb
-/
theorem xJet_periodic {f : Plane → ℂ} (hf : UnitPeriodic f) (p : ℕ) :
    UnitPeriodic (xJet p f) := by
  induction p with
  | zero => exact hf
  | succ p ih => rw [xJet_succ]; exact partialX_periodic ih

/--
@isnad1 id=hasderiv.1h3v.s7.fa6bca7b0a5a from=translated src=- shape=d3340351 vocab=e5e24184
-/
theorem hasDerivAt_slice {f : Plane → ℂ} {x y : ℝ}
    (hf : DifferentiableAt ℝ f (x, y)) :
    HasDerivAt (fun t => f (t, y)) (partialX f (x, y)) x := by
  exact hf.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))

/-- The actual two-dimensional Fourier coefficient, with the first coordinate integrated first. -/
def coefficient (f : Plane → ℂ) (k : Frequency) : ℂ :=
  unitCoeff (fun y => unitCoeff (fun x => f (x, y)) k.1) k.2

/--
@isnad1 id=le.1h3v.s6.939518dcee7e from=translated src=- shape=9772c1d5 vocab=d3da3e13
-/
theorem coefficient_norm_le {f : Plane → ℂ} {C : ℝ} (k : Frequency)
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f (x, y)‖ ≤ C) :
    ‖coefficient f k‖ ≤ C := by
  apply unitCoeff_norm_le
  intro y hy
  exact unitCoeff_norm_le k.1 (fun x hx => hb x hx y hy)

/--
@isnad1 id=eq.3h2v.s6.588615f73202 from=translated src=- shape=2532330d vocab=c0a2b0d4
-/
theorem coefficient_partialX {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.1 ≠ 0) :
    coefficient f k = (omega * (k.1 : ℂ))⁻¹ * coefficient (partialX f) k := by
  have heq : (fun y => unitCoeff (fun x => f (x, y)) k.1) =
      (fun y => (omega * (k.1 : ℂ))⁻¹ * unitCoeff (fun x => partialX f (x, y)) k.1) := by
    funext y
    apply unitCoeff_of_hasDerivAt hk
    · intro x
      exact hasDerivAt_slice ((hf.differentiable (by simp)) (x, y))
    · exact (partialX_smooth hf).continuous.comp (continuous_id.prodMk continuous_const)
    · simpa using hp (0, y) (1, 0)
  unfold coefficient
  rw [heq, unitCoeff_const_mul]

/-- Repeated Fourier integration by parts in the first coordinate.
@isnad1 id=eq.3h3v.s7.3a2f945e3bbd from=translated src=- shape=8ef03e03 vocab=90c189a5
-/
theorem coefficient_xJet {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.1 ≠ 0) (p : ℕ) :
    coefficient f k = (omega * (k.1 : ℂ))⁻¹ ^ p * coefficient (xJet p f) k := by
  induction p with
  | zero => simp only [pow_zero, one_mul, xJet_zero]
  | succ p ih =>
      rw [ih, coefficient_partialX (xJet_smooth hf p) (xJet_periodic hp p) hk,
        xJet_succ, pow_succ, mul_assoc]

/-- A coefficient-decay estimate obtained from a bound on an actual derivative.
@isnad1 id=le.4h4v.s7.8934b527b12c from=translated src=- shape=34e954ce vocab=0b4e00d5
-/
theorem coefficient_decay_first {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.1 ≠ 0) (p : ℕ) {C : ℝ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖xJet p f (x, y)‖ ≤ C) :
    ‖coefficient f k‖ ≤ ‖(omega * (k.1 : ℂ))⁻¹‖ ^ p * C := by
  rw [coefficient_xJet hf hp hk p, norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (coefficient_norm_le k hb) (pow_nonneg (norm_nonneg _) p)

/-- The negative Fourier character on the unit square. -/
def kernel (k : Frequency) (z : Plane) : ℂ :=
  fourier (-k.1) (z.1 : UnitAddCircle) * fourier (-k.2) (z.2 : UnitAddCircle)

/--
@isnad1 id=continuo.0h1v.s5.0dc77db3128d from=translated src=- shape=7000f90d vocab=c6686ed0
-/
theorem kernel_continuous (k : Frequency) : Continuous (kernel k) :=
  (((fourier (-k.1)).continuous.comp (AddCircle.continuous_mk' 1)).comp continuous_fst).mul
    (((fourier (-k.2)).continuous.comp (AddCircle.continuous_mk' 1)).comp continuous_snd)

/--
@isnad1 id=eq.0h2v.s6.d637f0f3a345 from=translated src=- shape=15b8323d vocab=5960aaa0
-/
theorem coefficient_eq_doubleIntegral (f : Plane → ℂ) (k : Frequency) :
    coefficient f k = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, kernel k (x, y) * f (x, y) := by
  unfold coefficient
  rw [unitCoeff_eq_integral]
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  rw [unitCoeff_eq_integral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  unfold kernel
  ring

/--
@isnad1 id=eq.1h1v.s7.171160d4a7d6 from=translated src=- shape=a318a0ea vocab=b4e8ae20
-/
theorem integral_square_swap {f : Plane → ℂ} (hf : Continuous f) :
    (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y)) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f (x, y) := by
  simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply (integral_integral_swap ?_).symm
  change Integrable f ((volume.restrict (Ioc (0 : ℝ) 1)).prod
    (volume.restrict (Ioc (0 : ℝ) 1)))
  rw [Measure.prod_restrict]
  exact (hf.continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- Swap function, defined pointwise by `f (z.2, z.1)`. -/
noncomputable def swapFunction (f : Plane → ℂ) : Plane → ℂ := fun z => f (z.2, z.1)

/--
@isnad1 id=contdiff.1h1v.s7.440405667c12 from=translated src=- shape=e9f00064 vocab=5250b21d
-/
theorem swapFunction_smooth {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (swapFunction f) := hf.comp (contDiff_snd.prodMk contDiff_fst)

/--
@isnad1 id=unitperi.1h1v.s3.1b299364b8d1 from=translated src=- shape=b6154235 vocab=c51f0011
-/
theorem swapFunction_periodic {f : Plane → ℂ} (hp : UnitPeriodic f) :
    UnitPeriodic (swapFunction f) := by
  intro z k
  exact hp (z.2, z.1) (k.2, k.1)

/--
@isnad1 id=eq.1h2v.s5.4c288f8e31a0 from=translated src=- shape=938d4fc5 vocab=f9b78f2b
-/
theorem coefficient_swap {f : Plane → ℂ} (hf : Continuous f) (k : Frequency) :
    coefficient f k = coefficient (swapFunction f) (k.2, k.1) := by
  rw [coefficient_eq_doubleIntegral, coefficient_eq_doubleIntegral,
    integral_square_swap ((kernel_continuous k).fun_mul hf)]
  apply intervalIntegral.integral_congr
  intro x _
  apply intervalIntegral.integral_congr
  intro y _
  unfold kernel swapFunction
  ring

/--
@isnad1 id=le.4h4v.s7.d182a6c1f63d from=translated src=- shape=d9eb58fb vocab=888bead2
-/
theorem coefficient_decay_second {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.2 ≠ 0) (p : ℕ) {C : ℝ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet p (swapFunction f) (x, y)‖ ≤ C) :
    ‖coefficient f k‖ ≤ ‖(omega * (k.2 : ℂ))⁻¹‖ ^ p * C := by
  rw [coefficient_swap hf.continuous k]
  exact coefficient_decay_first (swapFunction_smooth hf) (swapFunction_periodic hp) hk p hb

/--
@isnad1 id=le.0h0v.s3.cc7000f1264f from=translated src=- shape=7164367e vocab=f8f712a7
-/
theorem norm_omega_ge_one : 1 ≤ ‖omega‖ := by
  have hnorm : ‖omega‖ = 2 * Real.pi := by
    simp [omega, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hnorm]
  linarith [Real.two_le_pi]

/-- Multiplying by the first frequency power is controlled by the actual derivative norm.
@isnad1 id=le.4h4v.s7.2a2174fc758c from=translated src=- shape=5db3b076 vocab=a6466fcf
-/
theorem coefficient_first_moment {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) {k : Frequency} (hk : k.1 ≠ 0) (p : ℕ) {C : ℝ}
    (hb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖xJet p f (x, y)‖ ≤ C) :
    |(k.1 : ℝ)| ^ p * ‖coefficient f k‖ ≤ C := by
  have hsymbol : omega * (k.1 : ℂ) ≠ 0 :=
    mul_ne_zero omega_ne_zero (by exact_mod_cast hk)
  have hident : (omega * (k.1 : ℂ)) ^ p * coefficient f k = coefficient (xJet p f) k := by
    rw [coefficient_xJet hf hp hk p, ← mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hsymbol, one_pow, one_mul]
  have hn := congrArg norm hident
  simp only [norm_mul, norm_pow, Complex.norm_intCast] at hn
  have hfreq : |(k.1 : ℝ)| ≤ ‖omega‖ * |(k.1 : ℝ)| := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right norm_omega_ge_one (abs_nonneg (k.1 : ℝ))
  calc
    |(k.1 : ℝ)| ^ p * ‖coefficient f k‖ ≤
        (‖omega‖ * |(k.1 : ℝ)|) ^ p * ‖coefficient f k‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hfreq p) (norm_nonneg _)
    _ = ‖coefficient (xJet p f) k‖ := hn
    _ ≤ C := coefficient_norm_le k hb

/--
@isnad1 id=ne.2h1v.s5.eaca063703f9 from=translated src=- shape=146a209a vocab=990bb817
-/
theorem dominant_coordinate_ne_zero {k : Frequency} (hk : k ≠ 0)
    (hdom : |(k.2 : ℝ)| ≤ |(k.1 : ℝ)|) : k.1 ≠ 0 := by
  intro hzero
  have hsecond : (k.2 : ℝ) = 0 := abs_eq_zero.mp
    (le_antisymm (by simpa [hzero] using hdom) (abs_nonneg _))
  exact hk (Prod.ext hzero (by exact_mod_cast hsecond))

/--
@isnad1 id=le.2h1v.s6.dc7ca638829e from=translated src=- shape=bd69740e vocab=92b85347
-/
theorem weight_le_dominant {k : Frequency} (hk : k.1 ≠ 0)
    (hdom : |(k.2 : ℝ)| ≤ |(k.1 : ℝ)|) : weight k ≤ 3 * |(k.1 : ℝ)| := by
  have hi : (1 : ℤ) ≤ |k.1| := Int.add_one_le_iff.mpr (abs_pos.mpr hk)
  have hr : (1 : ℝ) ≤ |(k.1 : ℝ)| := by exact_mod_cast hi
  unfold weight
  linarith

/--
@isnad1 id=le.4h4v.s7.d4154808bced from=translated src=- shape=f049edc7 vocab=0e684d12
-/
theorem weight_moment_of_dominant {k : Frequency} {p : ℕ} {A C : ℝ}
    (hk : k.1 ≠ 0) (hdom : |(k.2 : ℝ)| ≤ |(k.1 : ℝ)|) (hA : 0 ≤ A)
    (hb : |(k.1 : ℝ)| ^ p * A ≤ C) : weight k ^ p * A ≤ 3 ^ p * C := by
  calc
    weight k ^ p * A ≤ (3 * |(k.1 : ℝ)|) ^ p * A :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (weight_pos k).le (weight_le_dominant hk hdom) p) hA
    _ = 3 ^ p * (|(k.1 : ℝ)| ^ p * A) := by rw [mul_pow]; ring
    _ ≤ 3 ^ p * C := mul_le_mul_of_nonneg_left hb (by positivity)

/-- Finite derivative loss: a p-th frequency moment uses only the values and
the p-th pure derivative in each coordinate on the unit square.
@isnad1 id=le.5h4v.s8.3886c58ce92d from=translated src=- shape=c47aaf82 vocab=2cf2ed0d
-/
theorem coefficient_polynomial_bound {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (p : ℕ) {C : ℝ}
    (hzero : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f (x, y)‖ ≤ C)
    (hfirst : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖xJet p f (x, y)‖ ≤ C)
    (hsecond : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet p (swapFunction f) (x, y)‖ ≤ C) (k : Frequency) :
    weight k ^ p * ‖coefficient f k‖ ≤ 3 ^ p * C := by
  by_cases hk : k = 0
  · subst k
    have hC : 0 ≤ C := (norm_nonneg _).trans (hzero 0 (by norm_num) 0 (by norm_num))
    simp only [weight, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, abs_zero, add_zero,
      one_pow, one_mul]
    exact (coefficient_norm_le 0 hzero).trans
      (le_mul_of_one_le_left hC (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)))
  rcases le_total |(k.2 : ℝ)| |(k.1 : ℝ)| with hdom | hdom
  · have hne := dominant_coordinate_ne_zero hk hdom
    exact weight_moment_of_dominant hne hdom (norm_nonneg _)
      (coefficient_first_moment hf hp hne p hfirst)
  · have hswap : (k.2, k.1) ≠ (0 : Frequency) := by
      intro h
      exact hk (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))
    have hne := dominant_coordinate_ne_zero hswap hdom
    have h := weight_moment_of_dominant hne hdom
      (norm_nonneg (coefficient (swapFunction f) (k.2, k.1)))
      (coefficient_first_moment (swapFunction_smooth hf) (swapFunction_periodic hp) hne p hsecond)
    rw [← coefficient_swap hf.continuous k] at h
    have hw : weight (k.2, k.1) = weight k := by unfold weight; dsimp; ring
    simpa only [hw] using h

/-- Smoothness on the compact unit square supplies the derivative bounds;
no coefficient-decay hypothesis is used.
@isnad1 id=ex.2h2v.s6.49ce92bdb1fe from=translated src=- shape=264afa99 vocab=34d570fe
-/
theorem exists_coefficient_polynomial_bound {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (p : ℕ) :
    ∃ C : ℝ, ∀ k : Frequency, weight k ^ p * ‖coefficient f k‖ ≤ C := by
  have hc : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨A, hA⟩ := hc.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuousOn (xJet_smooth hf p).continuous.continuousOn
  obtain ⟨D, hD⟩ := hc.exists_bound_of_continuousOn
    (xJet_smooth (swapFunction_smooth hf) p).continuous.continuousOn
  let C := max A (max B D)
  refine ⟨3 ^ p * C, coefficient_polynomial_bound hf hp p ?_ ?_ ?_⟩
  · intro x hx y hy
    exact (hA (x, y) ⟨hx, hy⟩).trans (le_max_left _ _)
  · intro x hx y hy
    exact (hB (x, y) ⟨hx, hy⟩).trans ((le_max_left B D).trans (le_max_right _ _))
  · intro x hx y hy
    exact (hD (x, y) ⟨hx, hy⟩).trans ((le_max_right B D).trans (le_max_right _ _))

/--
@isnad1 id=summable.0h0v.s5.b042d3ace9d1 from=translated src=- shape=8a43977f vocab=fd0d1486
-/
theorem summable_integer_weight_inv_two :
    Summable (fun n : ℤ => ((1 + |(n : ℝ)|) ^ 2)⁻¹) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by decide)
  have hNat : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have h : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
      (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr hbase
    simpa only [Nat.cast_add, Nat.cast_one] using h
  apply Summable.of_nat_of_neg
  · simpa only [Int.cast_natCast, Nat.abs_cast, add_comm, one_div] using hNat
  · simpa only [Int.cast_neg, Int.cast_natCast, abs_neg,
      Nat.abs_cast, add_comm, one_div] using hNat

/--
@isnad1 id=le.0h1v.s6.58d01eee8cfe from=translated src=- shape=d7019e19 vocab=99b62a80
-/
theorem weight_inv_four_le_product (k : Frequency) :
    (weight k ^ 4)⁻¹ ≤ ((1 + |(k.1 : ℝ)|) ^ 2)⁻¹ * ((1 + |(k.2 : ℝ)|) ^ 2)⁻¹ := by
  have hfirst : 1 + |(k.1 : ℝ)| ≤ weight k := by
    unfold weight
    linarith [abs_nonneg (k.2 : ℝ)]
  have hsecond : 1 + |(k.2 : ℝ)| ≤ weight k := by
    unfold weight
    linarith [abs_nonneg (k.1 : ℝ)]
  have hproduct : (1 + |(k.1 : ℝ)|) ^ 2 * (1 + |(k.2 : ℝ)|) ^ 2 ≤ weight k ^ 4 := by
    calc
      _ ≤ (weight k ^ 2) * (weight k ^ 2) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hfirst 2)
          (pow_le_pow_left₀ (by positivity) hsecond 2) (sq_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have h := one_div_le_one_div_of_le (by positivity :
    0 < (1 + |(k.1 : ℝ)|) ^ 2 * (1 + |(k.2 : ℝ)|) ^ 2) hproduct
  simpa only [one_div, mul_inv_rev, mul_comm] using h

/--
@isnad1 id=summable.0h0v.s5.629cd2ebb101 from=translated src=- shape=91d6ed2d vocab=ef838119
-/
theorem summable_weight_inv_four : Summable (fun k : Frequency => (weight k ^ 4)⁻¹) := by
  have hprod := summable_integer_weight_inv_two.mul_of_nonneg
    summable_integer_weight_inv_two (fun n => by positivity) (fun n => by positivity)
  exact Summable.of_nonneg_of_le (fun k => inv_nonneg.mpr (pow_nonneg (weight_pos k).le _))
    weight_inv_four_le_product hprod

/-- Every smooth unit-periodic function has all weighted absolute Fourier moments.
For the p-th moment the proof uses p+4 derivatives and a summable lattice majorant.
@isnad1 id=rapid.2h1v.s6.f41ce4dc102c from=translated src=- shape=5551351c vocab=d0d2e96f
-/
theorem rapid_coefficient {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f) :
    Rapid (coefficient f) := by
  intro p
  obtain ⟨C, hC⟩ := exists_coefficient_polynomial_bound hf hp (p + 4)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (weight_pos k).le _) (norm_nonneg _)) _
    (summable_weight_inv_four.mul_left C)
  intro k
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos (weight_pos k) 4)).mpr
  calc
    (weight k ^ p * ‖coefficient f k‖) * weight k ^ 4 =
        weight k ^ (p + 4) * ‖coefficient f k‖ := by rw [pow_add]; ring
    _ ≤ C := hC k

/-- A quantitative finite-loss estimate for the exact seminorm used by
`TorusInverse`. The lattice constant is finite by `summable_weight_inv_four`.
@isnad1 id=le.5h3v.s8.39217bdfdba0 from=translated src=- shape=812e57c4 vocab=59cd7cca
-/
theorem coefficient_seminorm_bound {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (p : ℕ) {C : ℝ}
    (hzero : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, ‖f (x, y)‖ ≤ C)
    (hfirst : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet (p + 4) f (x, y)‖ ≤ C)
    (hsecond : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖xJet (p + 4) (swapFunction f) (x, y)‖ ≤ C) :
    coeffSeminorm p (coefficient f) ≤
      (3 ^ (p + 4) * C) * ∑' k : Frequency, (weight k ^ 4)⁻¹ := by
  have hb (k : Frequency) : weight k ^ p * ‖coefficient f k‖ ≤
      (3 ^ (p + 4) * C) * (weight k ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (weight_pos k) 4)).mpr
    calc
      (weight k ^ p * ‖coefficient f k‖) * weight k ^ 4 =
          weight k ^ (p + 4) * ‖coefficient f k‖ := by rw [pow_add]; ring
      _ ≤ 3 ^ (p + 4) * C := coefficient_polynomial_bound hf hp (p + 4) hzero hfirst hsecond k
  have h := (rapid_coefficient hf hp p).tsum_le_tsum hb
    (summable_weight_inv_four.mul_left (3 ^ (p + 4) * C))
  simpa only [coeffSeminorm, tsum_mul_left] using h

/-! ## Identification with the actual torus Fourier coefficients -/

/-- Torus lift, given by `f ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle))`. -/
noncomputable def torusLift (f : Torus → ℂ) (x : Plane) : ℂ :=
  f ((x.1 : UnitAddCircle), (x.2 : UnitAddCircle))

/--
@isnad1 id=unitperi.0h1v.s2.2c0aa5c9f333 from=translated src=- shape=723ef0fc vocab=42f1d096
-/
theorem torusLift_periodic (f : Torus → ℂ) : UnitPeriodic (torusLift f) := by
  intro z k
  simp [torusLift]

/-- Torus coefficient, given by `∫ z, torusMode (-k) z * f z ∂torusMeasure`. -/
def torusCoefficient (f : Torus → ℂ) (k : Frequency) : ℂ :=
  ∫ z, torusMode (-k) z * f z ∂torusMeasure

/--
@isnad1 id=eq.0h2v.s5.bc8b44c7783f from=translated src=- shape=7f26d1ce vocab=435b2674
-/
theorem unitCoeff_torusLift (f : UnitAddCircle → ℂ) (n : ℤ) :
    unitCoeff (fun x : ℝ => f (x : UnitAddCircle)) n = fourierCoeff f n := by
  rw [unitCoeff_eq_integral, fourierCoeff_eq_intervalIntegral f n 0]
  simp only [one_div_one, zero_add, one_smul, smul_eq_mul]

/--
@isnad1 id=integrab.0h2v.s8.ef8a929cfea5 from=translated src=- shape=d439b8d5 vocab=28c0491a
-/
theorem torusCoefficient_integrable (f : C(Torus, ℂ)) (k : Frequency) :
    Integrable (fun z => torusMode (-k) z * f z) torusMeasure := by
  apply (integrable_const (‖f‖ : ℝ)).mono'
    ((torusMode (-k)).continuous.fun_mul f.continuous).aestronglyMeasurable
  filter_upwards with z
  simpa only [norm_mul, norm_torusMode, one_mul] using f.norm_coe_le_norm z

/--
@isnad1 id=eq.0h2v.s8.38bae07b718b from=translated src=- shape=244ca50b vocab=61784b68
-/
theorem coefficient_lift_eq_torus (f : C(Torus, ℂ)) (k : Frequency) :
    coefficient (torusLift f) k = torusCoefficient f k := by
  change unitCoeff (fun y => unitCoeff
    (fun x => f ((x : UnitAddCircle), (y : UnitAddCircle))) k.1) k.2 = _
  have hinner : (fun y : ℝ => unitCoeff
      (fun x => f ((x : UnitAddCircle), (y : UnitAddCircle))) k.1) =
      (fun y : ℝ => fourierCoeff (fun x : UnitAddCircle => f (x, (y : UnitAddCircle))) k.1) := by
    funext y
    exact unitCoeff_torusLift (fun x : UnitAddCircle => f (x, (y : UnitAddCircle))) k.1
  rw [hinner, unitCoeff_torusLift
    (fun y : UnitAddCircle => fourierCoeff (fun x : UnitAddCircle => f (x, y)) k.1) k.2]
  unfold fourierCoeff torusCoefficient
  rw [show torusMeasure = (AddCircle.haarAddCircle : Measure UnitAddCircle).prod
    AddCircle.haarAddCircle from rfl,
    integral_prod_symm _ (torusCoefficient_integrable f k)]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [torusMode, ContinuousMap.coe_mk, Prod.fst_neg, Prod.snd_neg]
  ring

/-- The same continuous function on Mathlib's native finite-product torus. -/
noncomputable def nativeFunction (f : C(Torus, ℂ)) : C(UnitAddTorus (Fin 2), ℂ) where
  toFun z := f (z 0, z 1)
  continuous_toFun := f.continuous.comp ((continuous_apply 0).prodMk (continuous_apply 1))

/--
@isnad1 id=eq.0h2v.s8.690ce2000fdd from=translated src=- shape=ed7a4bef vocab=a5ed9fad
-/
theorem native_mode_eq (k : Fin 2 → ℤ) (z : UnitAddTorus (Fin 2)) :
    UnitAddTorus.mFourier k z = torusMode (k 0, k 1) (z 0, z 1) := by
  simp [UnitAddTorus.mFourier, torusMode, Fin.prod_univ_two]

/--
@isnad1 id=eq.0h2v.s8.09f0da3d731b from=translated src=- shape=bb183047 vocab=8f020aa4
-/
theorem native_coefficient_eq (f : C(Torus, ℂ)) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (nativeFunction f) k = torusCoefficient f (k 0, k 1) := by
  have h := (measurePreserving_finTwoArrow
    (AddCircle.haarAddCircle : Measure UnitAddCircle)).integral_comp'
      (fun z : Torus => torusMode (-(k 0, k 1)) z * f z)
  simp only [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourier, torusMode, torusCoefficient,
    torusMeasure, nativeFunction, Fin.prod_univ_two, smul_eq_mul,
    MeasureTheory.volume_pi,
    MeasurableEquiv.finTwoArrow, MeasurableEquiv.piFinTwo_apply] at h ⊢
  exact h

/-- Genuine Fourier reconstruction: summability is derived from smoothness.
@isnad1 id=eq.1h2v.s9.2c0edce8c8d8 from=translated src=- shape=078cf091 vocab=9493472b
-/
theorem torusSeries_coefficient (f : C(Torus, ℂ))
    (hf : ContDiff ℝ ∞ (torusLift f)) (z : Torus) :
    torusSeries (coefficient (torusLift f)) z = f z := by
  have ha := rapid_coefficient hf (torusLift_periodic f)
  have hc (k : Fin 2 → ℤ) : UnitAddTorus.mFourierCoeff (nativeFunction f) k =
      coefficient (torusLift f) (k 0, k 1) := by
    rw [native_coefficient_eq, coefficient_lift_eq_torus]
  have hsum : Summable (UnitAddTorus.mFourierCoeff (nativeFunction f)) := by
    have hcoef : Summable (coefficient (torusLift f)) := Summable.of_norm ha.summable_norm
    have h := hcoef.comp_injective (finTwoArrowEquiv ℤ).injective
    have heq : UnitAddTorus.mFourierCoeff (nativeFunction f) =
        (fun k : Fin 2 → ℤ => coefficient (torusLift f) (k 0, k 1)) := funext hc
    rw [heq]
    exact h
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hsum ![z.1, z.2]
  simp_rw [hc] at h
  have hnative : HasSum (fun k : Fin 2 → ℤ =>
      coefficient (torusLift f) (k 0, k 1) * torusMode (k 0, k 1) z) (f z) := by
    simpa [hc, native_mode_eq, nativeFunction, smul_eq_mul] using h
  have hpairs : HasSum (fun k : Frequency =>
      coefficient (torusLift f) k * torusMode k z) (f z) :=
    (finTwoArrowEquiv ℤ).hasSum_iff.mp hnative
  exact hpairs.tsum_eq

/--
@isnad1 id=eq.1h2v.s9.63fe21399408 from=translated src=- shape=72b2f77a vocab=c68dd1c7
-/
theorem series_coefficient_lift (f : C(Torus, ℂ))
    (hf : ContDiff ℝ ∞ (torusLift f)) (x : Plane) :
    series (coefficient (torusLift f)) x = torusLift f x := by
  rw [series_eq_torusSeries]
  exact torusSeries_coefficient f hf _

/--
@isnad1 id=eq.0h1v.s8.d3106952a617 from=translated src=- shape=d04f7156 vocab=45c4380c
-/
theorem coefficient_zero_eq_mean (f : C(Torus, ℂ)) :
    coefficient (torusLift f) 0 = ∫ z, f z ∂torusMeasure := by
  rw [coefficient_lift_eq_torus]
  simp [torusCoefficient, torusMode]

/-- The constructed inverse now solves the equation for an arbitrary smooth
zero-mean torus function, not only for a preassigned coefficient sequence.
@isnad1 id=eq.2h3v.s10.2a14429a4a5f from=translated src=- shape=ec6f7acb vocab=a8e49f35
-/
theorem inverse_solves_smooth_torus (d : Direction) (f : C(Torus, ℂ))
    (hf : ContDiff ℝ ∞ (torusLift f)) (hmean : (∫ z, f z ∂torusMeasure) = 0) (x : Plane) :
    fderiv ℝ (directionalInverse d (coefficient (torusLift f))) x (vector d) =
      torusLift f x := by
  have ha := rapid_coefficient hf (torusLift_periodic f)
  have hz : coefficient (torusLift f) 0 = 0 := by rw [coefficient_zero_eq_mean, hmean]
  rw [directionalInverse_solves d ha hz, series_coefficient_lift f hf]

/-! ## Descent of an arbitrary periodic function on the plane -/

/--
@isnad1 id=periodic.1h2v.s4.828b615259d2 from=translated src=- shape=bfc88543 vocab=546397c7
-/
theorem unitPeriodic_first {f : Plane → ℂ} (hp : UnitPeriodic f) (y : ℝ) :
    Periodic (fun x => f (x, y)) 1 := by
  intro x
  simpa using hp (x, y) (1, 0)

/--
@isnad1 id=periodic.1h2v.s4.1a1873ebfe6f from=translated src=- shape=c108a5ea vocab=546397c7
-/
theorem unitPeriodic_second {f : Plane → ℂ} (hp : UnitPeriodic f) (x : ℝ) :
    Periodic (fun y => f (x, y)) 1 := by
  intro y
  simpa using hp (x, y) (0, 1)

/-- First lift, given by `(unitPeriodic_first hp y).lift z`. -/
noncomputable def firstLift (f : Plane → ℂ) (hp : UnitPeriodic f)
    (z : UnitAddCircle) (y : ℝ) : ℂ :=
  (unitPeriodic_first hp y).lift z

/--
@isnad1 id=periodic.1h2v.s4.1bc68e363dcd from=translated src=- shape=8a7842a8 vocab=8178fe1b
-/
theorem firstLift_periodic (f : Plane → ℂ) (hp : UnitPeriodic f) (z : UnitAddCircle) :
    Periodic (firstLift f hp z) 1 := by
  intro y
  refine Quotient.inductionOn' z (fun x => ?_)
  change f (x, y + 1) = f (x, y)
  exact unitPeriodic_second hp x y

/-- Descend, given by `(firstLift_periodic f hp z.1).lift z.2`. -/
noncomputable def descend (f : Plane → ℂ) (hp : UnitPeriodic f) (z : Torus) : ℂ :=
  (firstLift_periodic f hp z.1).lift z.2

/--
@isnad1 id=eq.1h3v.s5.539ef57e0328 from=translated src=- shape=6aa9e46a vocab=7676ef56
-/
@[simp] theorem descend_coe (f : Plane → ℂ) (hp : UnitPeriodic f) (x y : ℝ) :
    descend f hp ((x : UnitAddCircle), (y : UnitAddCircle)) = f (x, y) := rfl

/--
@isnad1 id=continuo.2h1v.s6.21a7ebfb09a4 from=translated src=- shape=40fc8d0f vocab=c6b6e608
-/
theorem descend_continuous {f : Plane → ℂ} (hf : Continuous f) (hp : UnitPeriodic f) :
    Continuous (descend f hp) := by
  have hq : IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle)) :=
    QuotientAddGroup.isOpenQuotientMap_mk
  apply (hq.prodMap hq).isQuotientMap.continuous_iff.mpr
  exact hf

/-- Descend continuous, bundling `toFun`, `continuous_toFun`. -/
noncomputable def descendContinuous (f : Plane → ℂ) (hf : Continuous f)
    (hp : UnitPeriodic f) : C(Torus, ℂ) where
  toFun := descend f hp
  continuous_toFun := descend_continuous hf hp

/--
@isnad1 id=eq.2h1v.s7.5a4a5c8f323c from=translated src=- shape=4721c6ce vocab=0b9b099b
-/
@[simp] theorem torusLift_descendContinuous (f : Plane → ℂ) (hf : Continuous f)
    (hp : UnitPeriodic f) : torusLift (descendContinuous f hf hp) = f := rfl

/-- Pointwise reconstruction for an arbitrary actual smooth unit-periodic
function on the plane; neither rapid decay nor reconstruction is a premise.
@isnad1 id=eq.2h2v.s6.29a9be751f0e from=translated src=- shape=a9b597ad vocab=297df81f
-/
theorem series_coefficient {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) (x : Plane) : series (coefficient f) x = f x := by
  have h := series_coefficient_lift (descendContinuous f hf.continuous hp)
    (show ContDiff ℝ ∞ (torusLift (descendContinuous f hf.continuous hp)) from hf) x
  exact h

/--
@isnad1 id=eq.0h1v.s6.d588f865d27a from=translated src=- shape=685fb1f1 vocab=b0f1f0e7
-/
theorem coefficient_zero_eq_integral (f : Plane → ℂ) :
    coefficient f 0 = ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y) := by
  rw [coefficient_eq_doubleIntegral]
  simp [kernel]

/-- The final coefficient bridge to the existing inverse construction.
@isnad1 id=and.2h1v.s6.193bfdef212b from=translated src=- shape=a5bad568 vocab=969bc4bf
-/
theorem smooth_periodic_fourier_data {f : Plane → ℂ} (hf : ContDiff ℝ ∞ f)
    (hp : UnitPeriodic f) : Rapid (coefficient f) ∧ series (coefficient f) = f :=
  ⟨rapid_coefficient hf hp, funext (series_coefficient hf hp)⟩

/--
@isnad1 id=eq.3h3v.s9.b40cfc356fca from=translated src=- shape=a5e03a22 vocab=303ab92f
-/
theorem inverse_solves_smooth_periodic (d : Direction) {f : Plane → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : UnitPeriodic f)
    (hmean : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, f (x, y)) = 0) (x : Plane) :
    fderiv ℝ (directionalInverse d (coefficient f)) x (vector d) = f x := by
  have hz : coefficient f 0 = 0 := by rw [coefficient_zero_eq_integral, hmean]
  rw [directionalInverse_solves d (rapid_coefficient hf hp) hz, series_coefficient hf hp]

end NavierStokes.SmoothFourierData
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
