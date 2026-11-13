import Tengoku.Nlalib.NLAlib.Polynomial.FunctionApproximation.ChebyshevTensor
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.Complex
import Tengoku.Seed.Tactic.FieldSimp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit positive Jackson damping

The damping coefficients used for normal-matrix spectral density estimation
are normalized autocorrelations of a finite sine vector. This description
supplies positivity without assuming an approximation theorem.
Source: Musco--Musco--Shah--Urschel--West, arXiv:2605.31430v2, equation (2.12).
Atlas: `tensor-chebyshev-kernel-measure` (partial).
-/

noncomputable section

open Real Finset

namespace NLAlib

/-- The angle in the explicit Jackson damping formula.-/
def chebyshevJacksonAngle (M : ℕ) : ℝ := π / (M + 2)

/-- The explicit Jackson damping coefficient, with its continuous trigonometric formula.-/
def chebyshevJacksonDamping (M j : ℕ) : ℝ :=
  (((M + 2 : ℝ) - j) * cos ((j : ℝ) * chebyshevJacksonAngle M) +
    sin ((j : ℝ) * chebyshevJacksonAngle M) * cot (chebyshevJacksonAngle M)) / (M + 2)

/-- The finite sine vector whose autocorrelation gives Jackson damping.-/
def chebyshevJacksonSineWeight (M l : ℕ) : ℝ :=
  sin (((l + 1 : ℕ) : ℝ) * chebyshevJacksonAngle M)

/--
@isnad1 id=lt.0h1v.s3.bcec9c9c475a from=translated src=- shape=b9369acb vocab=ddf655a9
-/
theorem chebyshevJacksonAngle_pos (M : ℕ) : 0 < chebyshevJacksonAngle M :=
  div_pos pi_pos (by positivity)

/--
@isnad1 id=lt.0h1v.s3.a33ad4183004 from=translated src=- shape=f0bb1bdd vocab=f0f473ed
-/
theorem chebyshevJacksonAngle_lt_pi (M : ℕ) : chebyshevJacksonAngle M < π := by
  unfold chebyshevJacksonAngle
  rw [div_lt_iff₀ (show (0 : ℝ) < M + 2 by positivity)]
  nlinarith [show (0 : ℝ) ≤ M from Nat.cast_nonneg M, pi_pos]

/--
@isnad1 id=le.1h1v.s5.d7298c61385a from=translated src=- shape=57bba0c1 vocab=712a01df
-/
theorem chebyshevJacksonAngle_le_pi_div_three {M : ℕ} (hM : 1 ≤ M) :
    chebyshevJacksonAngle M ≤ π / 3 := by
  unfold chebyshevJacksonAngle
  apply div_le_div_of_nonneg_left pi_pos.le (by norm_num)
  exact_mod_cast (by omega : 3 ≤ M + 2)

/--
@isnad1 id=eq.0h1v.s5.1fb24a561ec4 from=translated src=- shape=ea2afee9 vocab=8fcbdae3
-/
theorem chebyshevJacksonAngle_mul (M : ℕ) : (M + 2 : ℝ) * chebyshevJacksonAngle M = π := by
  unfold chebyshevJacksonAngle
  field_simp

/--
@isnad1 id=lt.0h1v.s3.09b3a34fb6b6 from=translated src=- shape=25e12683 vocab=915c8303
-/
theorem sin_chebyshevJacksonAngle_pos (M : ℕ) : 0 < sin (chebyshevJacksonAngle M) :=
  sin_pos_of_pos_of_lt_pi (chebyshevJacksonAngle_pos M) (chebyshevJacksonAngle_lt_pi M)

/-- The exact sine autocorrelation identity, including the vanishing next frequency.
@isnad1 id=eq.1h2v.s7.10d196085082 from=translated src=- shape=8d93a587 vocab=5b742b55
-/
theorem sum_chebyshevJacksonSineWeight_mul (M j : ℕ) (hj : j ≤ M + 1) :
    2 * (∑ l ∈ range (M + 1 - j),
      chebyshevJacksonSineWeight M l * chebyshevJacksonSineWeight M (l + j)) =
      ((M + 2 : ℝ) - j) * cos ((j : ℝ) * chebyshevJacksonAngle M) +
        sin ((j : ℝ) * chebyshevJacksonAngle M) * cot (chebyshevJacksonAngle M) := by
  let θ := chebyshevJacksonAngle M
  let n := M + 1 - j
  have hn : (n : ℝ) = (M : ℝ) + 1 - j := by
    dsimp [n]
    rw [Nat.cast_sub hj]
    push_cast
    ring
  have hN : (M + 2 : ℝ) * θ = π := chebyshevJacksonAngle_mul M
  have hs : sin θ ≠ 0 := (sin_chebyshevJacksonAngle_pos M).ne'
  have hcos := Real.sin_mul_sum_cos n (2 * θ) (((j : ℝ) + 2) * θ)
  have h1 : 2 * θ / 2 = θ := by ring
  have h2 : (n : ℝ) * (2 * θ) / 2 = (n : ℝ) * θ := by ring
  have h3 : ((n : ℝ) - 1) * (2 * θ) / 2 + ((j : ℝ) + 2) * θ = π := by
    rw [hn]
    nlinarith [hN]
  have h4 : (n : ℝ) * θ = π - ((j : ℝ) + 1) * θ := by
    rw [hn]
    nlinarith [hN]
  rw [h1, h2, h3, h4, sin_pi_sub, cos_pi, mul_neg_one] at hcos
  have hprod (l : ℕ) :
      2 * (chebyshevJacksonSineWeight M l * chebyshevJacksonSineWeight M (l + j)) =
        cos ((j : ℝ) * θ) - cos (2 * θ * (l : ℝ) + ((j : ℝ) + 2) * θ) := by
    have ha : (j : ℝ) * θ = (((l + j + 1 : ℕ) : ℝ) * θ) - (((l + 1 : ℕ) : ℝ) * θ) := by
      push_cast
      ring
    have hb : 2 * θ * (l : ℝ) + ((j : ℝ) + 2) * θ =
        (((l + j + 1 : ℕ) : ℝ) * θ) + (((l + 1 : ℕ) : ℝ) * θ) := by push_cast; ring
    rw [ha, hb, cos_sub, cos_add]
    dsimp [chebyshevJacksonSineWeight, θ]
    ring
  have hsum : 2 * (∑ l ∈ range n,
      chebyshevJacksonSineWeight M l * chebyshevJacksonSineWeight M (l + j)) =
      (n : ℝ) * cos ((j : ℝ) * θ) -
        ∑ l ∈ range n, cos (2 * θ * (l : ℝ) + ((j : ℝ) + 2) * θ) := by
    rw [mul_sum]
    simp_rw [hprod]
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have hadd : sin (((j : ℝ) + 1) * θ) =
      sin ((j : ℝ) * θ) * cos θ + cos ((j : ℝ) * θ) * sin θ := by
    rw [add_mul, one_mul, sin_add]
  change 2 * (∑ l ∈ range n,
      chebyshevJacksonSineWeight M l * chebyshevJacksonSineWeight M (l + j)) =
      ((M + 2 : ℝ) - j) * cos ((j : ℝ) * θ) + sin ((j : ℝ) * θ) * cot θ
  rw [hsum, cot_eq_cos_div_sin]
  apply (mul_left_cancel₀ hs)
  have hcos' : sin θ * (∑ l ∈ range n, cos (2 * θ * (l : ℝ) + ((j : ℝ) + 2) * θ)) =
      -(sin ((j : ℝ) * θ) * cos θ + cos ((j : ℝ) * θ) * sin θ) := hcos.trans (congrArg Neg.neg hadd)
  rw [mul_sub, hcos', hn]
  field_simp [hs]
  ring

/-- The displayed closed damping formula is its normalized sine autocorrelation.
@isnad1 id=eq.1h2v.s6.17b44bcdf076 from=translated src=- shape=fe3e436e vocab=79e91256
-/
theorem chebyshevJacksonDamping_eq_autocorrelation (M j : ℕ) (hj : j ≤ M + 1) :
    chebyshevJacksonDamping M j = (2 / (M + 2 : ℝ)) *
      ∑ l ∈ range (M + 1 - j), chebyshevJacksonSineWeight M l * chebyshevJacksonSineWeight M (l + j) := by
  rw [chebyshevJacksonDamping, ← sum_chebyshevJacksonSineWeight_mul M j hj]
  ring

/-- The zeroth Jackson damping coefficient preserves constants exactly.
@isnad1 id=eq.0h1v.s4.79ed8d00b5f4 from=translated src=- shape=8fc7241c vocab=dbb71a5b
-/
@[simp] theorem chebyshevJacksonDamping_zero (M : ℕ) : chebyshevJacksonDamping M 0 = 1 := by
  have hN : (M + 2 : ℝ) ≠ 0 := by positivity
  simp [chebyshevJacksonDamping, hN]

/-- The next frequency after the cutoff has zero sine autocorrelation.
@isnad1 id=eq.0h1v.s4.dae246412e56 from=translated src=- shape=c2460743 vocab=4aca90d3
-/
@[simp] theorem chebyshevJacksonDamping_succ (M : ℕ) : chebyshevJacksonDamping M (M + 1) = 0 := by
  rw [chebyshevJacksonDamping_eq_autocorrelation M (M + 1) le_rfl]
  simp

/-- The finite sine vector has the exact squared normalization `(M+2)/2`.
@isnad1 id=eq.0h1v.s6.f42dd17f365a from=translated src=- shape=a5ae98b8 vocab=6699e2a2
-/
theorem sum_chebyshevJacksonSineWeight_sq (M : ℕ) :
    (∑ l ∈ range (M + 1), chebyshevJacksonSineWeight M l ^ 2) = (M + 2 : ℝ) / 2 := by
  have h := sum_chebyshevJacksonSineWeight_mul M 0 (by omega)
  simp only [Nat.sub_zero, add_zero, Nat.cast_zero, zero_mul, cos_zero, mul_one,
    sin_zero, sub_zero] at h
  simp_rw [← sq] at h
  linarith

/-- Every weight in the finite Jackson sine vector is nonnegative.
@isnad1 id=le.1h2v.s4.998abdd26a93 from=translated src=- shape=7c81aa35 vocab=d0ab8705
-/
theorem chebyshevJacksonSineWeight_nonneg {M l : ℕ} (hl : l ≤ M) :
    0 ≤ chebyshevJacksonSineWeight M l := by
  apply sin_nonneg_of_nonneg_of_le_pi (by
    exact mul_nonneg (by positivity) (chebyshevJacksonAngle_pos M).le)
  have h : ((l + 1 : ℕ) : ℝ) ≤ M + 2 := by exact_mod_cast (by omega : l + 1 ≤ M + 2)
  exact (mul_le_mul_of_nonneg_right h (chebyshevJacksonAngle_pos M).le).trans_eq
    (chebyshevJacksonAngle_mul M)

/-- The exact Jackson damping coefficients are nonnegative, including the next zero mode.
@isnad1 id=le.1h2v.s5.18aa6bc91d6e from=translated src=- shape=0fa7259f vocab=88719c1b
-/
theorem chebyshevJacksonDamping_nonneg {M j : ℕ} (hj : j ≤ M + 1) :
    0 ≤ chebyshevJacksonDamping M j := by
  rw [chebyshevJacksonDamping_eq_autocorrelation M j hj]
  apply mul_nonneg (by positivity)
  apply sum_nonneg
  intro l hl
  have hlt := mem_range.mp hl
  exact mul_nonneg (chebyshevJacksonSineWeight_nonneg (by omega))
    (chebyshevJacksonSineWeight_nonneg (by omega))

/-- The first damping coefficient is the cosine of the Jackson angle.
@isnad1 id=eq.0h1v.s3.e2db71f0be7d from=translated src=- shape=e372e3f4 vocab=e1eaca6c
-/
@[simp] theorem chebyshevJacksonDamping_one (M : ℕ) :
    chebyshevJacksonDamping M 1 = cos (chebyshevJacksonAngle M) := by
  have hs := (sin_chebyshevJacksonAngle_pos M).ne'
  simp only [chebyshevJacksonDamping, Nat.cast_one, one_mul, cot_eq_cos_div_sin]
  field_simp [hs]
  ring

/-- The second coefficient has a simple formula also valid at the first cutoff,
where the second frequency is zero.
@isnad1 id=eq.0h1v.s6.53f560b200dd from=translated src=- shape=8db3f022 vocab=135ceb46
-/
theorem chebyshevJacksonDamping_two (M : ℕ) :
    chebyshevJacksonDamping M 2 =
      (((M : ℝ) + 1) * cos (2 * chebyshevJacksonAngle M) + 1) / (M + 2) := by
  have hs := (sin_chebyshevJacksonAngle_pos M).ne'
  simp only [chebyshevJacksonDamping, Nat.cast_ofNat, sin_two_mul, cos_two_mul,
    cot_eq_cos_div_sin]
  field_simp [hs]
  ring

end NLAlib
