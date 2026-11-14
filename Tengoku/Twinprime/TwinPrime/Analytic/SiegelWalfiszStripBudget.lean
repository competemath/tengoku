import Tengoku.Twinprime.TwinPrime.Analytic.SiegelWalfiszStripWidth
import Tengoku.Twinprime.TwinPrime.Analytic.LogDerivativeStrip

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform logarithmic budgets on polylogarithmic rectangles

The proved evaluation width is at least a constant times `L^(-1/2)`.
The local logarithmic numerator is at most a constant times `L^(1/2)`.
Their product gives a bound proportional to `L`, uniformly over the
conductor family and with all constants fixed in advance.
-/

noncomputable section

open Filter

namespace TwinPrime.Analytic

def siegelWalfiszStripNumeratorConstant (B K : ℝ) : ℝ :=
  1 + Real.log 16 + Real.log 5 + 2 * (2 * B + K)

def siegelWalfiszStripBudgetConstant (B K d : ℝ) : ℝ :=
  siegelWalfiszStripNumeratorConstant B K *
    ((288 * (1 + Real.log 5 / Real.log (6 / 5))) +
      1 / (Real.log (6 / 5) * siegelWalfiszStripWidthConstant B K d))

/--
@isnad1 id=lt.2h2v.s5.72898dfedc5f from=translated src=- shape=6c67d60b vocab=fb1dbf77
-/
theorem siegelWalfiszStripNumeratorConstant_pos (B K : ℝ)
    (hB : 0 < B) (hK : 0 < K) : 0 < siegelWalfiszStripNumeratorConstant B K := by
  have h16 : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  unfold siegelWalfiszStripNumeratorConstant
  positivity

/--
@isnad1 id=lt.3h3v.s5.d5c33d12ca8c from=translated src=- shape=1b4cbc0d vocab=4b1c230b
-/
theorem siegelWalfiszStripBudgetConstant_pos (B K d : ℝ)
    (hB : 0 < B) (hK : 0 < K) (hd : 0 < d) :
    0 < siegelWalfiszStripBudgetConstant B K d := by
  have hA := siegelWalfiszStripNumeratorConstant_pos B K hB hK
  have hk := siegelWalfiszStripWidthConstant_pos B K d hB hK hd
  have h65 : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  unfold siegelWalfiszStripBudgetConstant
  positivity

/--
@isnad1 id=le.5h4v.s7.0c395adac9fa from=translated src=- shape=6c2a099f vocab=29c2edc5
-/
theorem primitiveStripLogNumerator_polylog_le (B K L : ℝ)
    (hB : 0 < B) (hK : 0 < K) (hL : 1 ≤ L)
    (q : ℕ) (hq : 1 ≤ q) (hqL : (q : ℝ) ≤ L ^ B) :
    1 + Real.log 16 + 2 * Real.log q + Real.log (L ^ K + 4) ≤
      siegelWalfiszStripNumeratorConstant B K * L ^ (1 / 2 : ℝ) := by
  have hL0 : 0 < L := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hhalf : 1 ≤ L ^ (1 / 2 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hLK : 1 ≤ L ^ K := Real.one_le_rpow hL hK.le
  have hlogq : Real.log q ≤ B * Real.log L := by
    calc
      _ ≤ Real.log (L ^ B) := Real.log_le_log hq0 hqL
      _ = _ := Real.log_rpow hL0 B
  have hheight : Real.log (L ^ K + 4) ≤ Real.log 5 + K * Real.log L := by
    calc
      _ ≤ Real.log (5 * L ^ K) := Real.log_le_log (by positivity) (by linarith)
      _ = _ := by
        rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hL0 K).ne', Real.log_rpow hL0]
  have hlogL : Real.log L ≤ 2 * L ^ (1 / 2 : ℝ) := by
    have h := Real.log_le_rpow_div hL0.le (by norm_num : (0 : ℝ) < 1 / 2)
    linarith
  have h16 : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have hsmall := mul_le_mul_of_nonneg_left hlogL (by positivity : 0 ≤ 2 * B + K)
  have hconstant := mul_le_mul_of_nonneg_left hhalf
    (by positivity : 0 ≤ 1 + Real.log 16 + Real.log 5)
  unfold siegelWalfiszStripNumeratorConstant
  nlinarith

/-- Pointwise control for every logarithmic variable at least one.
@isnad1 id=le.6h5v.s7.e4952c156c36 from=translated src=- shape=a45e8029 vocab=f4d47dbd
-/
theorem siegelWalfiszStripBudgetConstant_bound (B K d L : ℝ)
    (hB : 0 < B) (hK : 0 < K) (hd : 0 < d) (hL : 1 ≤ L)
    (q : ℕ) (hq : 1 ≤ q) (hqL : (q : ℝ) ≤ L ^ B) :
    primitiveStripLogDerivativeBudget q (L ^ K)
        (primitiveZeroFreeRectangleWidth (1 / (2 * B)) d q (L ^ K + 2) / 2) ≤
      siegelWalfiszStripBudgetConstant B K d * L := by
  let A := siegelWalfiszStripNumeratorConstant B K
  let k := siegelWalfiszStripWidthConstant B K d
  let R := L ^ (1 / 2 : ℝ)
  let δ := primitiveZeroFreeRectangleWidth (1 / (2 * B)) d q (L ^ K + 2) / 2
  let J := Real.log (6 / 5 : ℝ)
  let W := (288 * (1 + Real.log 5 / Real.log (6 / 5)) : ℝ)
  let N := Real.log 16 + 2 * Real.log q + Real.log (L ^ K + 4)
  have hA : 0 < A := siegelWalfiszStripNumeratorConstant_pos B K hB hK
  have hk : 0 < k := siegelWalfiszStripWidthConstant_pos B K d hB hK hd
  have hL0 : 0 < L := by linarith
  have hR : 0 < R := Real.rpow_pos_of_pos hL0 _
  have hR1 : 1 ≤ R := Real.one_le_rpow hL (by norm_num)
  have hRR : R * R = L := by
    dsimp [R]
    rw [← Real.rpow_add hL0]
    norm_num
  have hRL : R ≤ L := by nlinarith
  have hJ : 0 < J := Real.log_pos (by norm_num)
  have h5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hN : 1 + N ≤ A * R := by
    simpa [A, R, N, add_assoc] using primitiveStripLogNumerator_polylog_le B K L hB hK hL q hq hqL
  have hwidth : k / R ≤ δ := by
    have h := siegelWalfiszStripWidthConstant_mul_rpow_le B K d L hB hK hd hL q hq hqL
    simpa only [Real.rpow_neg hL0.le, div_eq_mul_inv, k, R, δ] using h
  have hδ : 0 < δ := (div_pos hk hR).trans_le hwidth
  have hinv : 1 / δ ≤ R / k := by
    have h := one_div_le_one_div_of_le (div_pos hk hR) hwidth
    simpa only [one_div_div, one_mul] using h
  have hsecond : N / J / δ ≤ A * L / (J * k) := by
    calc
      _ = (N / J) * (1 / δ) := by ring
      _ ≤ (A * R / J) * (R / k) :=
        mul_le_mul (div_le_div_of_nonneg_right (by linarith) hJ.le) hinv
          (by positivity) (by positivity)
      _ = A * L / (J * k) := by rw [← hRR]; ring
  have hfirst : W * (1 + N) ≤ W * A * L := by
    calc
      _ ≤ W * (A * R) := mul_le_mul_of_nonneg_left hN hW
      _ ≤ W * (A * L) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hRL hA.le) hW
      _ = _ := by ring
  have hbudget : primitiveStripLogDerivativeBudget q (L ^ K)
      (primitiveZeroFreeRectangleWidth (1 / (2 * B)) d q (L ^ K + 2) / 2) =
      W * (1 + N) + N / J / δ := by
    dsimp [primitiveStripLogDerivativeBudget, W, N, J, δ]
    ring
  rw [hbudget]
  have he : siegelWalfiszStripBudgetConstant B K d * L =
      W * A * L + A * L / (J * k) := by
    dsimp [siegelWalfiszStripBudgetConstant, W, A, J, k]
    ring
  rw [he]
  linarith

/--
@isnad1 id=ex.3h3v.s7.488dfd460338 from=translated src=- shape=91c6b437 vocab=c42ea38c
-/
theorem exists_siegelWalfisz_stripBudget_bound (B K d : ℝ)
    (hB : 0 < B) (hK : 0 < K) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop, ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ (Real.log x) ^ B →
        primitiveStripLogDerivativeBudget q ((Real.log x) ^ K)
            (primitiveZeroFreeRectangleWidth (1 / (2 * B)) d q ((Real.log x) ^ K + 2) / 2) ≤
          C * Real.log x := by
  refine ⟨siegelWalfiszStripBudgetConstant B K d,
    siegelWalfiszStripBudgetConstant_pos B K d hB hK hd, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with x hx
  intro q hq hqL
  exact siegelWalfiszStripBudgetConstant_bound B K d (Real.log x) hB hK hd hx q hq hqL

end TwinPrime.Analytic
