import Tengoku.Nlalib.NLAlib.Matrix.Factorizations.EliminationStep
import Tengoku.Nlalib.NLAlib.Matrix.Basic.PosSemidefTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The RPCholesky pivot law

`choleskyPivotProbability R i = Re rᵢᵢ / Re (tr R)`, the diagonal-over-trace pivot law of
randomly pivoted Cholesky (uniform at `tr R = 0`, so that it is a probability vector for every
`R`), over `[RCLike 𝕜]`. For a PSD residual the law is nonnegative and the expected residual
after one step is `R − R² / tr R` (`sum_choleskyPivotProbability_smul_eliminationStep_eq`), with
expected trace `tr R − tr(R²)/tr R` (`sum_choleskyPivotProbability_mul_re_trace_eliminationStep_eq`).
Chen–Epperly–Tropp–Webber 2023 (RPCholesky), Alg. 1 and Lemma 5.3.
Atlas: helpers for `rpcholesky`.
-/

noncomputable section
open scoped Matrix ComplexOrder
namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- The **RPCholesky pivot law** `Re rᵢᵢ / Re (tr R)`, uniform when `Re (tr R) = 0` (so it sums
to one for every `R`; for a PSD `R` the trace is real and vanishes only at `R = 0`).
CETW 2023, Alg. 1.-/
def choleskyPivotProbability (R : Matrix n n 𝕜) (i : n) : ℝ :=
  if RCLike.re R.trace = 0 then 1 / (Fintype.card n : ℝ)
  else RCLike.re (R i i) / RCLike.re R.trace

/-- The pivot law sums to one, including the absorbing zero state. CETW 2023, Alg. 1.
@isnad1 id=eq.0h3v.s5.43cef8de81de from=translated src=- shape=065a4c23 vocab=9d9fc411
-/
theorem sum_choleskyPivotProbability [Nonempty n] (R : Matrix n n 𝕜) :
    ∑ i, choleskyPivotProbability R i = 1 := by
  by_cases ht : RCLike.re R.trace = 0
  · simp only [choleskyPivotProbability, ite_eq_left ht, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    exact mul_one_div_cancel (by exact_mod_cast Fintype.card_ne_zero)
  · simp only [choleskyPivotProbability, ite_eq_right ht, ← Finset.sum_div]
    rw [show (∑ i, RCLike.re (R i i)) = RCLike.re R.trace by simp [Matrix.trace, map_sum]]
    exact div_self ht

/-- A PSD residual gives a nonnegative pivot law. CETW 2023, Alg. 1.
@isnad1 id=le.1h4v.s5.070bfd54a6b9 from=translated src=- shape=6e3d4adb vocab=5dfaadd7
-/
theorem choleskyPivotProbability_nonneg {R : Matrix n n 𝕜} (hR : R.PosSemidef) (i : n) :
    0 ≤ choleskyPivotProbability R i := by
  unfold choleskyPivotProbability
  split_ifs
  · positivity
  · exact div_nonneg (RCLike.nonneg_iff.mp hR.diag_nonneg).1 (re_trace_nonneg_of_posSemidef hR)

variable [DecidableEq n]

omit [DecidableEq n] in
/-- Multiplying the diagonal-over-trace pivot probability by the residual trace
recovers its diagonal, including the absorbing zero state. CETW 2023, Alg. 1.
@isnad1 id=eq.1h4v.s8.693dca9446d9 from=translated src=- shape=6bf00f32 vocab=3aa57ba2
-/
theorem choleskyPivotProbability_mul_re_trace {R : Matrix n n 𝕜}
    (hR : R.PosSemidef) (i : n) :
    choleskyPivotProbability R i * RCLike.re R.trace = RCLike.re (R i i) := by
  by_cases ht : RCLike.re R.trace = 0
  · have hz := (re_trace_eq_zero_iff_of_posSemidef hR).mp ht
    simp [hz, choleskyPivotProbability]
  · simp [choleskyPivotProbability, ht]

/-- **One-step mean of RPCholesky**: for a PSD residual with `tr R ≠ 0`, the pivot-law average of
the elimination step is `R − R² / tr R`. CETW 2023, Lemma 5.3.
@isnad1 id=eq.2h3v.s9.84cf94242cb8 from=translated src=- shape=f1e6f9fc vocab=5a8e25af
-/
theorem sum_choleskyPivotProbability_smul_eliminationStep_eq [Nonempty n]
    {R : Matrix n n 𝕜} (hR : R.PosSemidef) (ht : RCLike.re R.trace ≠ 0) :
    (∑ i, choleskyPivotProbability R i • eliminationStep R i) =
      R - (RCLike.re R.trace)⁻¹ • (R * R) := by
  have hdiag : ∀ i, ((RCLike.re (R i i) : ℝ) : 𝕜) = R i i := fun i =>
    (diag_eq_ofReal_re_of_posSemidef hR i).symm
  have hc : ∀ i j k, ((RCLike.re (R i i) / RCLike.re R.trace) : ℝ) •
      ((R i i)⁻¹ * (R j i * R i k)) = (RCLike.re R.trace)⁻¹ • (R j i * R i k) := by
    intro i j k
    by_cases hi : R i i = 0
    · rw [hi, apply_eq_zero_of_posSemidef_of_apply_self_eq_zero hR hi j]
      simp
    · rw [RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul, RCLike.ofReal_div,
        RCLike.ofReal_inv, hdiag]
      field_simp
  ext j k
  simp only [Matrix.sum_apply, Matrix.smul_apply, eliminationStep_apply, smul_sub,
    Finset.sum_sub_distrib, Matrix.sub_apply]
  have hp : ∑ i, choleskyPivotProbability R i • R j k = R j k := by
    rw [← Finset.sum_smul, sum_choleskyPivotProbability, one_smul]
  rw [hp]
  simp only [choleskyPivotProbability, ite_eq_right ht, hc, ← Finset.smul_sum, Matrix.mul_apply]

/-- **Expected trace after one RPCholesky step**: `tr R − tr(R²)/tr R` (real parts), also at the
absorbing zero state. CETW 2023, Lemma 5.3.
@isnad1 id=eq.1h3v.s9.3332e91f1024 from=translated src=- shape=26b8fbd6 vocab=a3bb58a5
-/
theorem sum_choleskyPivotProbability_mul_re_trace_eliminationStep_eq [Nonempty n]
    {R : Matrix n n 𝕜} (hR : R.PosSemidef) :
    (∑ i, choleskyPivotProbability R i * RCLike.re (eliminationStep R i).trace) =
      RCLike.re R.trace - RCLike.re (R * R).trace / RCLike.re R.trace := by
  by_cases ht : RCLike.re R.trace = 0
  · have hz : R = 0 := (re_trace_eq_zero_iff_of_posSemidef hR).mp ht
    rw [hz]
    simp
  · have h := congrArg (fun M : Matrix n n 𝕜 => RCLike.re M.trace)
      (sum_choleskyPivotProbability_smul_eliminationStep_eq hR ht)
    simpa only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_sub, map_sub, map_sum,
      RCLike.smul_re, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

end NLAlib
