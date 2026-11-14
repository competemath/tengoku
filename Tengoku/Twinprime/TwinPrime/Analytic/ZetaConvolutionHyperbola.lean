import Tengoku.Twinprime.TwinPrime.Analytic.ComplexHyperbola

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The main term in a zeta convolution

The finite hyperbola identity isolates the reciprocal coefficient sum and
retains its error relative to any proposed main coefficient. No convergence
or identification of that coefficient is assumed here.
-/

noncomputable section

open Finset ArithmeticFunction

namespace TwinPrime.Analytic

theorem complexArithmeticSummatory_zeta (x : ℝ) :
    complexArithmeticSummatory (ArithmeticFunction.zeta : ArithmeticFunction ℂ) x =
      (⌊x⌋₊ : ℂ) := by
  unfold complexArithmeticSummatory
  have h : (∑ n ∈ Ioc 0 ⌊x⌋₊, (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) =
      ∑ _n ∈ Ioc 0 ⌊x⌋₊, (1 : ℂ) := by
    apply sum_congr rfl
    intro n hn
    simp [ArithmeticFunction.zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp hn).1)]
  rw [h]
  simp

theorem norm_natFloor_sub_self_le_one (x : ℝ) (hx : 0 ≤ x) :
    ‖(⌊x⌋₊ : ℂ) - (x : ℂ)‖ ≤ 1 := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by have := Nat.lt_floor_add_one x; linarith, by have := Nat.floor_le hx; linarith⟩

/-- Replacing the zeta partial sum by its real endpoint costs only the
absolute coefficient mass of the outer finite sum.-/
theorem norm_zeta_hyperbola_head_sub_reciprocal_le (f : ArithmeticFunction ℂ)
    (x : ℝ) (hx : 0 ≤ x) (Y : ℕ) :
    ‖(∑ k ∈ Ioc 0 Y, f k * complexArithmeticSummatory
        (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (x / k)) -
      (x : ℂ) * (∑ k ∈ Ioc 0 Y, f k / (k : ℂ))‖ ≤
      ∑ k ∈ Ioc 0 Y, ‖f k‖ := by
  have heq : (∑ k ∈ Ioc 0 Y, f k * complexArithmeticSummatory
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (x / k)) -
        (x : ℂ) * (∑ k ∈ Ioc 0 Y, f k / (k : ℂ)) =
      ∑ k ∈ Ioc 0 Y, f k * ((⌊x / k⌋₊ : ℂ) - ((x / k : ℝ) : ℂ)) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    rw [complexArithmeticSummatory_zeta, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  rw [heq]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro k _
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_natFloor_sub_self_le_one _ (by positivity))

/-- A finite zeta-convolution main-term bound retaining the actual reciprocal
head error. The proposed coefficient `L` is arbitrary.-/
theorem norm_zeta_convolution_sub_main_le_hyperbola (f : ArithmeticFunction ℂ)
    (L : ℂ) (x y z : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hyz : y * z = x) :
    ‖complexArithmeticSummatory (f * ArithmeticFunction.zeta) x - (x : ℂ) * L‖ ≤
      (∑ k ∈ Ioc 0 ⌊y⌋₊, ‖f k‖) +
        ‖∑ d ∈ Ioc 0 ⌊z⌋₊, complexArithmeticSummatory f (x / d)‖ +
        (⌊z⌋₊ : ℝ) * ‖complexArithmeticSummatory f y‖ +
        x * ‖(∑ k ∈ Ioc 0 ⌊y⌋₊, f k / (k : ℂ)) - L‖ := by
  let A := ∑ k ∈ Ioc 0 ⌊y⌋₊, f k * complexArithmeticSummatory
    (ArithmeticFunction.zeta : ArithmeticFunction ℂ) (x / k)
  let B := ∑ d ∈ Ioc 0 ⌊z⌋₊, complexArithmeticSummatory f (x / d)
  let H := ∑ k ∈ Ioc 0 ⌊y⌋₊, f k / (k : ℂ)
  let O := complexArithmeticSummatory f y * (⌊z⌋₊ : ℂ)
  have hsplit : complexArithmeticSummatory (f * ArithmeticFunction.zeta) x = A + B - O := by
    rw [complexArithmeticSummatory_convolution_hyperbola f ArithmeticFunction.zeta x y z hx hy hz hyz]
    congr 2
    · apply sum_congr rfl
      intro d hd
      simp [ArithmeticFunction.zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp hd).1)]
    · rw [complexArithmeticSummatory_zeta]
  rw [hsplit]
  have hdecomp : A + B - O - (x : ℂ) * L =
      ((A - (x : ℂ) * H) + B - O) + (x : ℂ) * (H - L) := by ring
  rw [hdecomp]
  have hnorm : ‖((A - (x : ℂ) * H) + B - O) + (x : ℂ) * (H - L)‖ ≤
      ‖A - (x : ℂ) * H‖ + ‖B‖ + ‖O‖ + ‖(x : ℂ) * (H - L)‖ := by
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
  apply hnorm.trans
  have hhead := norm_zeta_hyperbola_head_sub_reciprocal_le f x (by linarith) ⌊y⌋₊
  have hO : ‖O‖ = (⌊z⌋₊ : ℝ) * ‖complexArithmeticSummatory f y‖ := by
    simp only [O, norm_mul, Complex.norm_natCast]
    ring
  have htail : ‖(x : ℂ) * (H - L)‖ = x * ‖H - L‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x)]
  rw [hO, htail]
  exact add_le_add (add_le_add (add_le_add hhead le_rfl) le_rfl) le_rfl

end TwinPrime.Analytic
