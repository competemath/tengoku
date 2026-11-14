import Tengoku.Twinprime.TwinPrime.Analytic.SmoothedSiegelWalfisz
import Tengoku.Twinprime.TwinPrime.Analytic.SiegelWalfisz

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Centered finite unsmoothing

Forward differences of the integrated smoothed error recover the sharp
centered sum, with explicit short-interval and principal-main-term errors.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

def centeredRealCharacterPsi {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  (∑ n ∈ Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) -
    if χ = 1 then (x : ℂ) else 0

theorem centeredRealCharacterPsi_natCast {q : ℕ} (T : ℕ) (χ : DirichletCharacter ℂ q) :
    centeredRealCharacterPsi (T : ℝ) χ = centeredCharacterPsi T χ := by
  have hI : Icc 1 T = Ioc 0 T := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  simp only [centeredRealCharacterPsi, Nat.floor_natCast, centeredCharacterPsi,
    characterPsi, hI, Complex.ofReal_natCast]

theorem integrated_mangoldt_character_eq_centered {q : ℕ}
    (χ : DirichletCharacter ℂ q) (x : ℝ) (hx : x ≠ 0) :
    integratedWeightedPartialSum (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ n) x =
      (x : ℂ) * (centeredWeightedCharacterSum x χ + if χ = 1 then (x : ℂ) / 2 else 0) := by
  rw [integratedWeightedPartialSum_eq_mul_weightedPartialSum _ x hx]
  simp only [centeredWeightedCharacterSum, sub_add_cancel]
  congr 2
  funext n
  exact mul_comm _ _

theorem norm_centeredRealCharacterPsi_le_smoothed {q : ℕ}
    (χ : DirichletCharacter ℂ q) (x h : ℝ) (hx : 0 < x) (hh : 0 < h)
    (hxh : 1 ≤ x + h) :
    ‖centeredRealCharacterPsi x χ‖ ≤
      ((x + h) * ‖centeredWeightedCharacterSum (x + h) χ‖ +
        x * ‖centeredWeightedCharacterSum x χ‖) / h +
      (h + 1) * Real.log (x + h) + h / 2 := by
  let a : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ n
  let D := (integratedWeightedPartialSum a (x + h) - integratedWeightedPartialSum a x) / (h : ℂ)
  let S := ∑ n ∈ Icc 1 ⌊x⌋₊, a n
  let E := (((x + h : ℝ) : ℂ) * centeredWeightedCharacterSum (x + h) χ -
    (x : ℂ) * centeredWeightedCharacterSum x χ) / (h : ℂ)
  let R : ℂ := if χ = 1 then (h : ℂ) / 2 else 0
  have hhC : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh.ne'
  have hy : 0 < x + h := by linarith
  have heq : centeredRealCharacterPsi x χ = -(D - S) + (E + R) := by
    dsimp only [D, S, E, R, a, centeredRealCharacterPsi]
    rw [integrated_mangoldt_character_eq_centered χ (x + h) hy.ne',
      integrated_mangoldt_character_eq_centered χ x hx.ne']
    split_ifs <;> push_cast <;> field_simp <;> ring
  have hD : ‖D - S‖ ≤ (h + 1) * Real.log (x + h) :=
    norm_mangoldt_character_forward_difference_sub_sum_le χ x h hx.le hh hxh
  have hE : ‖E‖ ≤ ((x + h) * ‖centeredWeightedCharacterSum (x + h) χ‖ +
      x * ‖centeredWeightedCharacterSum x χ‖) / h := by
    dsimp only [E]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    apply div_le_div_of_nonneg_right _ hh.le
    apply (norm_sub_le _ _).trans
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy, abs_of_pos hx]
    exact le_rfl
  have hR : ‖R‖ ≤ h / 2 := by
    dsimp only [R]
    split_ifs
    · norm_num [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    · simp only [norm_zero]
      positivity
  rw [heq]
  have hn := (norm_add_le (-(D - S)) (E + R)).trans
    (_root_.add_le_add (by simpa only [norm_neg] using hD)
      ((norm_add_le E R).trans (_root_.add_le_add hE hR)))
  linarith

/-- Two smoothed estimates with exponent `2*A+4` suffice. The short
interval has length `x / (log x)^(A+2)`, which is at least one here.-/
theorem norm_centeredRealCharacterPsi_le_of_two_smoothed {q : ℕ}
    (χ : DirichletCharacter ℂ q) (A C x : ℝ) (hA : 0 < A) (hC : 0 < C)
    (hx : 1 ≤ x) (hlog : 1 ≤ Real.log x)
    (hpow : (Real.log x) ^ (A + 2) ≤ x)
    (hfirst : ‖centeredWeightedCharacterSum x χ‖ ≤ C * x / (Real.log x) ^ (2 * A + 4))
    (hsecond : ‖centeredWeightedCharacterSum (x + x / (Real.log x) ^ (A + 2)) χ‖ ≤
      C * (x + x / (Real.log x) ^ (A + 2)) /
        (Real.log (x + x / (Real.log x) ^ (A + 2))) ^ (2 * A + 4)) :
    ‖centeredRealCharacterPsi x χ‖ ≤ (5 * C + 5) * x / (Real.log x) ^ A := by
  let L := Real.log x
  let P := L ^ (A + 2)
  let h := x / P
  let y := x + h
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ L := hlog
  have hL0 : 0 < L := by linarith
  have hP : 0 < P := Real.rpow_pos_of_pos hL0 _
  have hP1 : 1 ≤ P := Real.one_le_rpow hL (by linarith)
  have hh : 0 < h := div_pos hx0 hP
  have hh1 : 1 ≤ h := (le_div_iff₀ hP).mpr (by simpa using hpow)
  have hhx : h ≤ x := (div_le_self hx0.le hP1)
  have hxy : x ≤ y := by dsimp [y]; linarith
  have hy2 : y ≤ 2 * x := by dsimp [y]; linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  have hlogs : L ≤ Real.log y := Real.log_le_log hx0 hxy
  have hlogy : Real.log y ≤ 2 * L := by
    have hb := Real.log_le_log hy0 hy2
    rw [Real.log_mul (by norm_num) hx0.ne'] at hb
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    dsimp [L] at hL ⊢
    linarith
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  have hLP : 0 < L ^ (2 * A + 4) := Real.rpow_pos_of_pos hL0 _
  have hLPsq : L ^ (2 * A + 4) = P ^ 2 := by
    dsimp [P]
    rw [← Real.rpow_two (L ^ (A + 2)), ← Real.rpow_mul hL0.le]
    congr 1
    ring
  have hhl : h * L ≤ x / L ^ A := by
    calc
      _ = x / L ^ (A + 1) := by
        dsimp [h, P]
        rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_two, Real.rpow_one]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_left hx0.le hLA
        (Real.rpow_le_rpow_of_exponent_le hL (by linarith))
  have hhR : h ≤ x / L ^ A :=
    (le_mul_of_one_le_right hh.le hL).trans hhl
  have hsecond' : ‖centeredWeightedCharacterSum y χ‖ ≤ C * y / L ^ (2 * A + 4) := by
    apply hsecond.trans
    exact div_le_div_of_nonneg_left (by positivity) hLP
      (Real.rpow_le_rpow hL0.le hlogs (by linarith))
  have hnumerator : y * ‖centeredWeightedCharacterSum y χ‖ +
      x * ‖centeredWeightedCharacterSum x χ‖ ≤ 5 * C * x ^ 2 / L ^ (2 * A + 4) := by
    calc
      _ ≤ y * (C * y / L ^ (2 * A + 4)) + x * (C * x / L ^ (2 * A + 4)) := by
        gcongr
      _ = C * (y ^ 2 + x ^ 2) / L ^ (2 * A + 4) := by ring
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ hLP.le
        have hs : y ^ 2 + x ^ 2 ≤ 5 * x ^ 2 := by nlinarith
        nlinarith
  have herr : (y * ‖centeredWeightedCharacterSum y χ‖ +
      x * ‖centeredWeightedCharacterSum x χ‖) / h ≤ 5 * C * h := by
    apply (div_le_div_of_nonneg_right hnumerator hh.le).trans_eq
    rw [hLPsq]
    dsimp [h]
    field_simp
  have hshort : (h + 1) * Real.log y ≤ 4 * (x / L ^ A) := by
    calc
      _ ≤ (2 * h) * (2 * L) := by gcongr <;> linarith
      _ = 4 * (h * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hhl (by norm_num)
  have hmain : h / 2 ≤ x / L ^ A := by linarith
  have htotal := norm_centeredRealCharacterPsi_le_smoothed χ x h hx0 hh (hx.trans hxy)
  change ‖_‖ ≤ (y * ‖centeredWeightedCharacterSum y χ‖ +
    x * ‖centeredWeightedCharacterSum x χ‖) / h + (h + 1) * Real.log y + h / 2 at htotal
  have herr' := herr.trans (mul_le_mul_of_nonneg_left hhR (by positivity : 0 ≤ 5 * C))
  have he : (5 * C + 5) * x / L ^ A = 5 * C * (x / L ^ A) + 4 * (x / L ^ A) + x / L ^ A := by ring
  change ‖_‖ ≤ (5 * C + 5) * x / L ^ A
  rw [he]
  linarith

end TwinPrime.Analytic
