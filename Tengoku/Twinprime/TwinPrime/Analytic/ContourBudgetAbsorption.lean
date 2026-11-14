import Tengoku.Twinprime.TwinPrime.Analytic.ContourParameterBounds
import Tengoku.Twinprime.TwinPrime.Analytic.SmoothedPrincipalContour

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Absorption of the three contour errors

The principal budget dominates both right-line tails. At the chosen
right line and polylogarithmic height, its three terms are bounded by
two negative powers of the logarithm and a square-root exponential.
-/

noncomputable section

open Filter
open scoped Topology

namespace TwinPrime.Analytic

theorem smoothedPrincipalContourBudget_eq (x a c H M : ℝ) (hH : H ≠ 0) :
    smoothedPrincipalContourBudget x a c H M =
      x ^ c * (mangoldtDirichletMass c + 1 / (c - 1)) / (Real.pi * H) +
      ((1 + (a ^ 2)⁻¹) / 2) * x ^ a * M +
      (c - a) * x ^ c * M / (Real.pi * H ^ 2) := by
  unfold smoothedPrincipalContourBudget
  have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

theorem smoothedPrincipalContourBudget_le_three_errors
    (x K k C δ M : ℝ) (hx : 1 < x) (hlog : 8 ≤ Real.log x)
    (hC : 0 < C) (hδ : 0 < δ) (hδu : δ ≤ 1 / 16)
    (hwidth : k * (Real.log x) ^ (-(1 / 2 : ℝ)) ≤ δ)
    (hM : 0 ≤ M) (hMb : M ≤ C * Real.log x) :
    smoothedPrincipalContourBudget x (1 - δ) (1 + 1 / Real.log x) ((Real.log x) ^ K) M ≤
      42 * Real.exp 1 * x * (Real.log x) ^ (1 - K) +
      3 * C * x * Real.log x * Real.exp (-k * (Real.log x) ^ (1 / 2 : ℝ)) +
      C * Real.exp 1 * x * (Real.log x) ^ (1 - 2 * K) := by
  let L := Real.log x
  let c := 1 + 1 / L
  let a := 1 - δ
  let H := L ^ K
  have hx0 : 0 < x := by linarith
  have hL : 8 ≤ L := hlog
  have hL0 : 0 < L := by linarith
  have hH : 0 < H := Real.rpow_pos_of_pos hL0 K
  have ha : (1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hc : 1 < c := by
    dsimp [c]
    have hi : 0 < 1 / L := by positivity
    linarith
  have hca0 : 0 ≤ c - a := by dsimp [a]; linarith
  have hca : c - a ≤ 1 := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) hL
    dsimp [c, a]
    linarith
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hxc : x ^ c = Real.exp 1 * x := rpow_one_add_inv_log x hx
  have hxa : x ^ a ≤ x * Real.exp (-k * L ^ (1 / 2 : ℝ)) :=
    rpow_one_sub_le_of_width x k δ hx hwidth
  have hmass : mangoldtDirichletMass c + 1 / (c - 1) ≤ 42 * L := by
    have hm := mangoldtMass_right_line_le x hlog
    have he : 1 / (c - 1) = L := by dsimp [c]; rw [add_sub_cancel_left, one_div_one_div]
    rw [he]
    change mangoldtDirichletMass c ≤ L + 40 at hm
    linarith
  have hpower (b : ℝ) : L / L ^ b = L ^ (1 - b) := by
    rw [Real.rpow_sub hL0, Real.rpow_one]
  have hHsq : H ^ 2 = L ^ (2 * K) := by
    dsimp [H]
    rw [← Real.rpow_two (L ^ K), ← Real.rpow_mul hL0.le]
    congr 1
    ring
  have htail : x ^ c * (mangoldtDirichletMass c + 1 / (c - 1)) / (Real.pi * H) ≤
      42 * Real.exp 1 * x * L ^ (1 - K) := by
    calc
      _ ≤ x ^ c * (42 * L) / (Real.pi * H) := by gcongr
      _ ≤ x ^ c * (42 * L) / H :=
        div_le_div_of_nonneg_left (by positivity) hH
          (by nlinarith [mul_le_mul_of_nonneg_right hpi hH.le])
      _ = 42 * Real.exp 1 * x * (L / L ^ K) := by rw [hxc]; dsimp [H]; ring
      _ = _ := by rw [hpower]
  have hfactor : (1 + (a ^ 2)⁻¹) / 2 ≤ 3 := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 4)
      (show (1 / 4 : ℝ) ≤ a ^ 2 by nlinarith)
    norm_num only [one_div, inv_div, inv_one, one_mul] at hi
    linarith
  have hvert : ((1 + (a ^ 2)⁻¹) / 2) * x ^ a * M ≤
      3 * C * x * L * Real.exp (-k * L ^ (1 / 2 : ℝ)) := by
    calc
      _ ≤ 3 * (x * Real.exp (-k * L ^ (1 / 2 : ℝ))) * (C * L) := by gcongr
      _ = _ := by ring
  have hhorizontal : (c - a) * x ^ c * M / (Real.pi * H ^ 2) ≤
      C * Real.exp 1 * x * L ^ (1 - 2 * K) := by
    calc
      _ ≤ x ^ c * (C * L) / (Real.pi * H ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hm := mul_le_mul (mul_le_mul_of_nonneg_right hca (Real.rpow_nonneg hx0.le c))
          hMb hM (by positivity : 0 ≤ 1 * x ^ c)
        simpa only [one_mul] using hm
      _ ≤ x ^ c * (C * L) / H ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (by nlinarith [mul_le_mul_of_nonneg_right hpi (sq_nonneg H)])
      _ = C * Real.exp 1 * x * (L / L ^ (2 * K)) := by rw [hxc, hHsq]; ring
      _ = _ := by rw [hpower]
  change smoothedPrincipalContourBudget x a c H M ≤ _
  rw [smoothedPrincipalContourBudget_eq x a c H M hH.ne']
  change _ ≤ 42 * Real.exp 1 * x * L ^ (1 - K) +
    3 * C * x * L * Real.exp (-k * L ^ (1 / 2 : ℝ)) +
    C * Real.exp 1 * x * L ^ (1 - 2 * K)
  linarith

def contourAbsorptionConstant (C : ℝ) : ℝ := 42 * Real.exp 1 + 3 * C + C * Real.exp 1

theorem contourAbsorptionConstant_pos (C : ℝ) (hC : 0 < C) :
    0 < contourAbsorptionConstant C := by
  unfold contourAbsorptionConstant
  positivity

/-- A common threshold works for every admissible width and norm budget.-/
theorem eventually_smoothedPrincipalContourBudget_le (A k C : ℝ)
    (hA : 0 < A) (hk : 0 < k) (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop, ∀ δ M : ℝ,
      0 < δ → δ ≤ 1 / 16 →
      k * (Real.log x) ^ (-(1 / 2 : ℝ)) ≤ δ →
      0 ≤ M → M ≤ C * Real.log x →
        smoothedPrincipalContourBudget x (1 - δ) (1 + 1 / Real.log x)
          ((Real.log x) ^ (A + 2)) M ≤
            contourAbsorptionConstant C * x / (Real.log x) ^ A := by
  have hexp := Real.tendsto_log_atTop.eventually
    (eventually_mul_exp_neg_sqrt_le_rpow A k hk)
  filter_upwards [hexp, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (8 : ℝ))] with x hExp hx hlog
  intro δ M hδ hδu hw hM hMb
  have hL : 1 ≤ Real.log x := by linarith
  have hx0 : 0 < x := by linarith
  have hlow : (Real.log x) ^ (1 - (A + 2)) ≤ (Real.log x) ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hhigh : (Real.log x) ^ (1 - 2 * (A + 2)) ≤ (Real.log x) ^ (-A) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have htail := mul_le_mul_of_nonneg_left hlow
    (by positivity : 0 ≤ 42 * Real.exp 1 * x)
  have hhorizontal := mul_le_mul_of_nonneg_left hhigh
    (by positivity : 0 ≤ C * Real.exp 1 * x)
  have hmiddle : 3 * C * x * Real.log x * Real.exp (-k * (Real.log x) ^ (1 / 2 : ℝ)) ≤
      (3 * C * x) * (Real.log x) ^ (-A) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hExp
      (by positivity : 0 ≤ 3 * C * x)
  have hb := smoothedPrincipalContourBudget_le_three_errors x (A + 2) k C δ M hx hlog hC
    hδ hδu hw hM hMb
  have he : contourAbsorptionConstant C * x / (Real.log x) ^ A =
      (42 * Real.exp 1 * x) * (Real.log x) ^ (-A) +
      (3 * C * x) * (Real.log x) ^ (-A) +
      (C * Real.exp 1 * x) * (Real.log x) ^ (-A) := by
    rw [Real.rpow_neg (by linarith : 0 ≤ Real.log x)]
    unfold contourAbsorptionConstant
    ring
  rw [he]
  linarith

theorem smoothedMangoldtContourBudget_le_principal (x a c H M : ℝ)
    (hx : 0 ≤ x) (hc : 1 < c) (hH : 0 < H) :
    smoothedMangoldtContourBudget x a c H M ≤ smoothedPrincipalContourBudget x a c H M := by
  unfold smoothedMangoldtContourBudget smoothedPrincipalContourBudget
  apply _root_.add_le_add
  · apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hx _)
    have hp : 0 ≤ 1 / (c - 1) := by positivity
    linarith
  · exact le_rfl

end TwinPrime.Analytic
