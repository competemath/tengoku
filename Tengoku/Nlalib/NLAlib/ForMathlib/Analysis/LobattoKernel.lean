import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.DirichletKernelBounds
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite cardinal kernel for Chebyshev extrema

The endpoint-half cosine kernel is a trigonometric cardinal kernel on `2n` equally spaced
angles. Source: focused polynomial-approximation rederivations, Theorem `thm:lobatto`.
-/

noncomputable section

open Real Finset

namespace NLAlib

/-- The endpoint-half finite cosine kernel for the Chebyshev extrema grid.
Source: focused rederivations, Theorem `thm:lobatto`.-/
def lobattoKernel (n : ℕ) (t : ℝ) : ℝ :=
  (1 + 2 * ∑ k ∈ range (n - 1), cos ((k + 1 : ℕ) * t) + cos ((n : ℝ) * t)) / (2 * n)

/-- The Lobatto kernel is the average of two consecutive Dirichlet kernels.
Source: the endpoint-half cosine sum.
@isnad1 id=eq.1h2v.s6.e13571db5e0f from=translated src=- shape=dada1e69 vocab=7936cdb8
-/
theorem lobattoKernel_eq_dirichlet {n : ℕ} (hn : 0 < n) (t : ℝ) :
    lobattoKernel n t =
      (dirichletCircleKernel (n - 1) (t : AddCircle (2 * π)) +
        dirichletCircleKernel n (t : AddCircle (2 * π))) / (4 * n) := by
  rw [dirichletCircleKernel_coe, dirichletCircleKernel_coe]
  have heq : n = (n - 1) + 1 := (Nat.sub_add_cancel hn).symm
  nth_rw 3 [heq]
  rw [sum_range_succ]
  dsimp [lobattoKernel]
  rw [Nat.sub_add_cancel hn]
  ring

/-- A globally valid sine-multiplied closed form of the finite Lobatto kernel.
Source: the finite Dirichlet sine telescope.
@isnad1 id=eq.1h2v.s6.940cd84b11b6 from=translated src=- shape=226285e6 vocab=5b2d9072
-/
theorem sin_half_mul_lobattoKernel {n : ℕ} (hn : 0 < n) (t : ℝ) :
    sin (t / 2) * lobattoKernel n t = sin ((n : ℝ) * t) * cos (t / 2) / (2 * n) := by
  rw [lobattoKernel_eq_dirichlet hn, ← mul_div_assoc, mul_add,
    sin_half_mul_dirichletCircleKernel_coe, sin_half_mul_dirichletCircleKernel_coe]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
  rw [hcast, show ((n : ℝ) - 1 + 1 / 2) * t = (n : ℝ) * t - t / 2 by ring,
    show ((n : ℝ) + 1 / 2) * t = (n : ℝ) * t + t / 2 by ring,
    sin_sub, sin_add]
  ring

/-- The Lobatto cardinal kernel has the cotangent closed form away from removable points.
Source: focused rederivations, Theorem `thm:lobatto`.
@isnad1 id=eq.2h2v.s6.9329ceec2571 from=translated src=- shape=d220522e vocab=cd2ed01e
-/
theorem lobattoKernel_eq_sin_cot {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : sin (t / 2) ≠ 0) :
    lobattoKernel n t = sin ((n : ℝ) * t) * Real.cot (t / 2) / (2 * n) := by
  have h := sin_half_mul_lobattoKernel hn t
  rw [Real.cot_eq_cos_div_sin]
  apply (mul_left_cancel₀ ht)
  calc
    sin (t / 2) * lobattoKernel n t = _ := h
    _ = _ := by field_simp

/-- The finite Lobatto cardinal kernel is even.
Source: evenness of each cosine term.
@isnad1 id=eq.0h2v.s3.25cff5062675 from=translated src=- shape=5a76020b vocab=a2c49179
-/
@[simp] theorem lobattoKernel_neg (n : ℕ) (t : ℝ) : lobattoKernel n (-t) = lobattoKernel n t := by
  simp [lobattoKernel, mul_neg]

/-- The removable value of the Lobatto kernel at zero is one.
Source: the finite cosine sum.
@isnad1 id=eq.1h1v.s4.db2edb30bbe7 from=translated src=- shape=41c8c002 vocab=2921aa94
-/
@[simp] theorem lobattoKernel_zero {n : ℕ} (hn : 0 < n) : lobattoKernel n 0 = 1 := by
  simp only [lobattoKernel, mul_zero, cos_zero, sum_const, card_range, nsmul_eq_mul, mul_one]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; norm_num
  rw [hcast]
  field_simp
  ring

/-- The finite cardinal kernel has period `2π`.
Source: integral cosine frequencies.
@isnad1 id=periodic.0h1v.s4.b16d4238b0cb from=translated src=- shape=3393a3a1 vocab=051e522e
-/
theorem lobattoKernel_periodic (n : ℕ) : Function.Periodic (lobattoKernel n) (2 * π) := by
  intro t
  simp only [lobattoKernel, mul_add]
  simp_rw [cos_add_nat_mul_two_pi]

/-- Every other point of the `2n`-angle grid is a zero of the cardinal kernel.
Source: its sine-multiplied closed form.
@isnad1 id=eq.3h2v.s6.082942adcf13 from=translated src=- shape=ebcc3c5a vocab=971b1d0c
-/
theorem lobattoKernel_grid_zero {n k : ℕ} (hn : 0 < n) (hk0 : 0 < k) (hk : k < 2 * n) :
    lobattoKernel n ((k : ℝ) * π / n) = 0 := by
  have hn0 : (0 : ℝ) < n := by positivity
  have hk0' : (0 : ℝ) < k := by positivity
  have hk' : (k : ℝ) < 2 * n := by exact_mod_cast hk
  have ha : 0 < (k : ℝ) * π / n / 2 := by positivity
  have hb : (k : ℝ) * π / n / 2 < π := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2), div_lt_iff₀ hn0]
    nlinarith [pi_pos]
  have hs : sin ((k : ℝ) * π / n / 2) ≠ 0 := (sin_pos_of_pos_of_lt_pi ha hb).ne'
  rw [lobattoKernel_eq_sin_cot hn hs]
  rw [show (n : ℝ) * ((k : ℝ) * π / n) = (k : ℝ) * π by field_simp,
    sin_nat_mul_pi, zero_mul, zero_div]

end NLAlib
