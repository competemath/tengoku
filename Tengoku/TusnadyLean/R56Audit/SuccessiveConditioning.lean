import Tengoku.Seed.Probability.Process.Filtration
import Tengoku.Seed.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Successive conditioning and Markov's inequality (Step 3 of the proof of Lemma 2.6)

Auditor's supplement (not part of the audited archive).

Step 3 of the proof of Lemma 2.6 bounds `E e^{-tT}` for `T = Σ_{j<h} T_j`, and then the
probability that `T ≤ -λ`. It rests on two general facts, which are proved here.

* "So we can condition successively on `𝓕_{h-1}, 𝓕_{h-2}, …, 𝓕_0` and apply Step 2 each time.
  Multiplying the `h` bounds gives `E e^{-tT} ≤ exp(hnt²/(2M²))`." This is
  `integral_prod_le_of_condExp_le`: let `(ℱ_j)` be a filtration of a probability space, and
  let `W_0, …, W_{h-1}` be random variables with values in `[0, B]` such that `W_j` is
  `ℱ_{j+1}`-measurable and almost surely `E[W_j | ℱ_j] ≤ c_j`, with constants `c_j ≥ 0`;
  then `E[W_0 ⋯ W_{h-1}] ≤ c_0 ⋯ c_{h-1}`. In the manuscript `W_j = e^{-t T_j}`, the bound of
  Step 2 is `c_j = exp(nt²/(2M²))`, and the product of the factors is `e^{-tT}`.
* "By Markov's inequality, `Pr(T ≤ -λ) = Pr(e^{-tT} ≥ e^{tλ}) ≤ exp(-tλ + hnt²/(2M²))`". This
  is `measureReal_le_exp_mul_integral_exp_neg`: for `t > 0` and every real `a`,
  `Pr(Z ≤ a) = Pr(e^{-tZ} ≥ e^{-ta}) ≤ e^{ta} E e^{-tZ}`. The manuscript takes `Z = T` and
  `a = -λ`, and then uses the bound for `E e^{-tT}`.

The first fact is proved by induction on `h`. "For every `j`, the earlier terms
`T_0, …, T_{j-1}` are `𝓕_j`-measurable." Accordingly, the product of the first `h` factors is
`ℱ_h`-measurable (`stronglyMeasurable_prod_range`); it lies in `[0, B^h]`
(`prod_range_mem_Icc`), so it is integrable (`integrable_prod_range`). Conditioning on `ℱ_h`
and pulling this product out of the conditional expectation,

`E[W_0 ⋯ W_h] = E[W_0 ⋯ W_{h-1} · E[W_h | ℱ_h]] ≤ c_h · E[W_0 ⋯ W_{h-1}]`.

The factors are not assumed independent, and they need not be at most `c_j` pointwise: only
their conditional expectations are.

This file uses Mathlib only, not the archive.
-/

namespace R56Audit

open MeasureTheory

/-! ### Successive conditioning -/

/-- If each `W_j` is `ℱ_{j+1}`-measurable, then the product of the first `h` factors is
`ℱ_h`-measurable. "For every `j`, the earlier terms `T_0, …, T_{j-1}` are
`𝓕_j`-measurable."
@isnad1 id=strongly.1h5v.s6.343a8713ce1c from=translated src=- shape=b70e6bae vocab=7747a3b3
-/
lemma stronglyMeasurable_prod_range {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ℕ mΩ) (W : ℕ → Ω → ℝ) (h : ℕ)
    (hW : ∀ j < h, StronglyMeasurable[ℱ (j + 1)] (W j)) :
    StronglyMeasurable[ℱ h] (fun ω => ∏ j ∈ Finset.range h, W j ω) :=
  Finset.stronglyMeasurable_fun_prod _ fun j hj =>
    StronglyMeasurable.mono (hW j (Finset.mem_range.mp hj))
      (ℱ.mono (Nat.succ_le_of_lt (Finset.mem_range.mp hj)))

/-! ### Markov's inequality -/

/-- **Markov's inequality for `e^{-tZ}`.** If `t > 0` and `e^{-tZ}` is integrable, then for
every real `a`,

`Pr(Z ≤ a) = Pr(e^{-tZ} ≥ e^{-ta}) ≤ e^{ta} E e^{-tZ}`.

"By Markov's inequality, `Pr(T ≤ -λ) = Pr(e^{-tT} ≥ e^{tλ}) ≤ exp(-tλ + hnt²/(2M²))`": this
is the case `Z = T`, `a = -λ`, followed by the bound for `E e^{-tT}`. The measure need not be
finite, and neither `Z` nor the event is assumed measurable.
@isnad1 id=le.2h6v.s7.b23e76d2517f from=translated src=- shape=be2fe4be vocab=01164211
-/
theorem measureReal_le_exp_mul_integral_exp_neg {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (Z : Ω → ℝ) {t : ℝ} (ht : 0 < t)
    (hint : Integrable (fun ω => Real.exp (-t * Z ω)) μ) (a : ℝ) :
    μ.real {ω | Z ω ≤ a} ≤ Real.exp (t * a) * ∫ ω, Real.exp (-t * Z ω) ∂μ := by
  -- `Z ≤ a` if and only if `e^{-tZ} ≥ e^{-ta}`, since `t > 0`
  have hevent : {ω | Z ω ≤ a} = {ω | Real.exp (-t * a) ≤ Real.exp (-t * Z ω)} := by
    ext ω
    change Z ω ≤ a ↔ Real.exp (-t * a) ≤ Real.exp (-t * Z ω)
    rw [Real.exp_le_exp, neg_mul, neg_mul, neg_le_neg_iff, mul_le_mul_iff_right₀ ht]
  calc μ.real {ω | Z ω ≤ a}
      = μ.real {ω | Real.exp (-t * a) ≤ Real.exp (-t * Z ω)} := by rw [hevent]
    _ ≤ (∫ ω, Real.exp (-t * Z ω) ∂μ) / Real.exp (-t * a) :=
        -- Markov's inequality for the nonnegative function `e^{-tZ}` at the level `e^{-ta}`
        (le_div_iff₀' (Real.exp_pos _)).mpr (mul_meas_ge_le_integral_of_nonneg
          (Filter.Eventually.of_forall fun ω => (Real.exp_pos (-t * Z ω)).le) hint _)
    _ = Real.exp (t * a) * ∫ ω, Real.exp (-t * Z ω) ∂μ := by
        rw [neg_mul, Real.exp_neg, div_inv_eq_mul, mul_comm]

end R56Audit
