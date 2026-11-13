import Tengoku.Seed.MeasureTheory.Integral.Gamma
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Integral
import Tengoku.Seed.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Tengoku.Nlalib.NLAlib.Probability.SubGaussian.ExpSquare
import Tengoku.Nlalib.NLAlib.Probability.Rademacher.Core
import Tengoku.Seed.Analysis.InnerProductSpace.PiL2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Sub-Gaussian moments, Khintchine and the maximal inequality

For `ProbabilityTheory.HasSubgaussianMGF X c μ` (Mathlib's sub-Gaussian predicate):

* `measureReal_lt_abs_le_of_hasSubgaussianMGF`: `P(t < |X|) ≤ 2 e^{-t²/(2c)}`;
* `integral_abs_rpow_le_of_hasSubgaussianMGF`: `𝔼|X|^p ≤ p (2c)^{p/2} Γ(p/2)` for real `p > 0`;
* `hasSubgaussianMGF_sum_mul_rademacher`, `integral_abs_rpow_sum_mul_rademacher_le`: Khintchine's
  inequality with an explicit constant (atlas `rademacher-khintchine`, upper half);
* `integrable_iSup_of_hasSubgaussianMGF`, `integral_iSup_le_of_hasSubgaussianMGF` and the `|·|`
  and `√(2c log N)` forms: the maximal inequality (atlas `subgaussian-max`), no independence
  needed;
* the generic moment and exponential-square API (`hasSubgaussianMGF_mono`,
  `integral_eq_zero_of_hasSubgaussianMGF`, `integral_pow_two_mul_le_of_hasSubgaussianMGF`,
  `integral_exp_mul_sq_le_of_hasSubgaussianMGF`, `hasSubgaussianMGF_finset_sum_mul_of_iIndepFun`)
  lives in `NLAlib.Probability.SubGaussian.EvenMoments` and `…ExpSquare`.

Sources: Vershynin 2018, Prop 2.5.2, Thm 2.6.3, Ex 2.5.10; Boucheron–Lugosi–Massart 2013,
Thm 2.5.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal

namespace NLAlib

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Two-sided sub-Gaussian tail: `P(t < |X|) ≤ 2 e^{-t²/(2c)}` for `t ≥ 0`.
Vershynin 2018, Prop 2.5.2 (i).
atlas: subgaussian-max-/
theorem measureReal_lt_abs_le_of_hasSubgaussianMGF [IsProbabilityMeasure μ] {X : Ω → ℝ}
    {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t < |X ω|} ≤ 2 * exp (-t ^ 2 / (2 * c)) := by
  have hsub : {ω | t < |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ (-X) ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_union, Pi.neg_apply] at hω ⊢
    rcases le_or_gt 0 (X ω) with h0 | h0
    · left; rw [abs_of_nonneg h0] at hω; exact hω.le
    · right; rw [abs_of_neg h0] at hω; exact hω.le
  calc μ.real {ω | t < |X ω|} ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | t ≤ (-X) ω} :=
        (measureReal_mono hsub).trans (measureReal_union_le _ _)
    _ ≤ exp (-t ^ 2 / (2 * c)) + exp (-t ^ 2 / (2 * c)) :=
        add_le_add (h.measure_ge_le ht) (h.neg.measure_ge_le ht)
    _ = 2 * exp (-t ^ 2 / (2 * c)) := by ring

/-! ### Khintchine's inequality with an explicit constant -/

/-- A Rademacher series `∑ᵢ aᵢ εᵢ` (`ε` a Rademacher vector) is sub-Gaussian with proxy
`‖a‖₂² = ∑ᵢ aᵢ²`. Vershynin 2018, Prop 2.6.1 with Example 2.5.8(ii). For independent signs given
as a family, build the vector law with `hasLaw_rademacherVector_of_iIndepFun`.
atlas: rademacher-khintchine-/
theorem hasSubgaussianMGF_sum_mul_rademacher {ι : Type*} [Fintype ι] (a : ι → ℝ)
    {ε : Ω → ι → ℝ} (hε : HasLaw ε (rademacherVector ι) μ) :
    HasSubgaussianMGF (fun ω => ∑ i, a i * ε ω i) (‖WithLp.toLp 2 a‖₊ ^ 2) μ := by
  have := hε.isProbabilityMeasure
  have h := hasSubgaussianMGF_finset_sum_mul_of_iIndepFun hε.iIndepFun_eval_of_rademacherVector
    (c := fun _ => 1) (s := Finset.univ)
    (fun i _ => hasSubgaussianMGF_of_hasLaw_rademacherMeasure (hε.hasLaw_eval_rademacherMeasure i))
    a
  refine (congrArg (fun c : ℝ≥0 => HasSubgaussianMGF (fun ω => ∑ i, a i * ε ω i) c μ) ?_).mp h
  ext
  simp [EuclideanSpace.norm_sq_eq, Real.coe_toNNReal _ (sq_nonneg _)]

/-! ### Maximal inequality -/

private lemma integral_le_log_div_of_integral_exp_le [IsProbabilityMeasure μ] {M : Ω → ℝ}
    (hM : Integrable M μ) {s B : ℝ} (hs : 0 < s)
    (hexp : Integrable (fun ω => exp (s * M ω)) μ) (hB : ∫ ω, exp (s * M ω) ∂μ ≤ B) :
    ∫ ω, M ω ∂μ ≤ log B / s := by
  have hJ : exp (∫ ω, s * M ω ∂μ) ≤ ∫ ω, exp (s * M ω) ∂μ :=
    convexOn_exp.map_integral_le continuousOn_exp isClosed_univ (ae_of_all _ fun _ => trivial)
      (hM.const_mul s) hexp
  rw [integral_const_mul] at hJ
  have hBpos : 0 < B := (exp_pos _).trans_le (hJ.trans hB)
  rw [le_div_iff₀ hs, mul_comm]
  exact (le_log_iff_exp_le hBpos).2 (hJ.trans hB)

private lemma exists_eq_iSup_fintype {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    ∃ j, f j = ⨆ i, f i := exists_eq_ciSup_of_finite

private lemma abs_iSup_le_sum_abs {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    |⨆ i, f i| ≤ ∑ i, |f i| := by
  obtain ⟨j, hj⟩ := exists_eq_iSup_fintype f
  rw [← hj]
  exact Finset.single_le_sum (f := fun i => |f i|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)

/-- The pointwise supremum of finitely many integrable functions is integrable.-/
private lemma integrable_iSup_of_integrable {ι : Type*} [Fintype ι] [Nonempty ι]
    (Y : ι → Ω → ℝ) (hY : ∀ i, Integrable (Y i) μ) : Integrable (fun ω => ⨆ i, Y i ω) μ :=
  (integrable_finsetSum Finset.univ fun i _ => (hY i).abs).mono'
    (AEMeasurable.iSup fun i => (hY i).aemeasurable).aestronglyMeasurable
    (ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs, Finset.sum_apply] using abs_iSup_le_sum_abs (Y · ω))

/-- Shared skeleton of the maximal inequalities for `M ω = ⨆ᵢ Yᵢ ω`: if `e^{sM} ≤ ∑ₖ Fₖ` pointwise
with `∫ Fₖ ≤ b`, then `𝔼 M ≤ log(K b)/s`.-/
private lemma integral_iSup_le_aux [IsProbabilityMeasure μ] {ι κ : Type*} [Fintype ι]
    [Nonempty ι] [Fintype κ] (Y : ι → Ω → ℝ) (hY : ∀ i, Integrable (Y i) μ)
    (F : κ → Ω → ℝ) (hF : ∀ k, Integrable (F k) μ) {s b : ℝ} (hs : 0 < s)
    (hexp : ∀ ω, exp (s * ⨆ i, Y i ω) ≤ ∑ k, F k ω) (hb : ∀ k, ∫ ω, F k ω ∂μ ≤ b) :
    ∫ ω, ⨆ i, Y i ω ∂μ ≤ log (Fintype.card κ * b) / s := by
  have hm : AEMeasurable (fun ω => ⨆ i, Y i ω) μ :=
    AEMeasurable.iSup fun i => (hY i).aemeasurable
  have hint : Integrable (fun ω => ⨆ i, Y i ω) μ := integrable_iSup_of_integrable Y hY
  have hsum : Integrable (fun ω => ∑ k, F k ω) μ := integrable_finsetSum Finset.univ fun k _ => hF k
  have hexpint : Integrable (fun ω => exp (s * ⨆ i, Y i ω)) μ :=
    hsum.mono' (measurable_exp.comp_aemeasurable (hm.const_mul s)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
        exact hexp ω)
  refine integral_le_log_div_of_integral_exp_le hint hs hexpint ?_
  calc ∫ ω, exp (s * ⨆ i, Y i ω) ∂μ ≤ ∫ ω, ∑ k, F k ω ∂μ :=
        integral_mono hexpint hsum hexp
    _ = ∑ k, ∫ ω, F k ω ∂μ := integral_finsetSum _ fun k _ => hF k
    _ ≤ ∑ _k : κ, b := Finset.sum_le_sum fun k _ => hb k
    _ = Fintype.card κ * b := by simp

/-- The maximum of finitely many sub-Gaussian variables is integrable (no independence needed).
Boucheron–Lugosi–Massart 2013, Thm 2.5.-/
theorem integrable_iSup_of_hasSubgaussianMGF {ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → Ω → ℝ) (c : ℝ≥0) (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    Integrable (fun ω => ⨆ i, X i ω) μ :=
  integrable_iSup_of_integrable X fun i => (h i).integrable

/-- The maximum of the absolute values of finitely many sub-Gaussian variables is integrable.
Boucheron–Lugosi–Massart 2013, Thm 2.5.-/
theorem integrable_iSup_abs_of_hasSubgaussianMGF {ι : Type*} [Fintype ι] [Nonempty ι]
    (X : ι → Ω → ℝ) (c : ℝ≥0) (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    Integrable (fun ω => ⨆ i, |X i ω|) μ :=
  integrable_iSup_of_integrable (fun i ω => |X i ω|) fun i => (h i).integrable.abs

/-- **Sub-Gaussian maximal inequality.** If each `Xᵢ` (finitely many, no independence needed)
is sub-Gaussian with proxy `c`, then for every `s > 0`,
`𝔼 maxᵢ Xᵢ ≤ log N / s + c s / 2` with `N = card ι` (integrability:
`integrable_iSup_of_hasSubgaussianMGF`).
Boucheron–Lugosi–Massart 2013, Thm 2.5 (proof); Vershynin 2018, Ex 2.5.10.
Atlas `subgaussian-max`.-/
theorem integral_iSup_le_of_hasSubgaussianMGF [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] [Nonempty ι] (X : ι → Ω → ℝ) (c : ℝ≥0)
    (h : ∀ i, HasSubgaussianMGF (X i) c μ) {s : ℝ} (hs : 0 < s) :
    ∫ ω, ⨆ i, X i ω ∂μ ≤ log (Fintype.card ι) / s + c * s / 2 := by
  have hexp : ∀ ω, exp (s * ⨆ i, X i ω) ≤ ∑ i, exp (s * X i ω) := by
    intro ω
    obtain ⟨j, hj⟩ := exists_eq_iSup_fintype (X · ω)
    rw [← hj]
    exact Finset.single_le_sum (f := fun i => exp (s * X i ω)) (fun i _ => (exp_pos _).le)
      (Finset.mem_univ j)
  have hle := integral_iSup_le_aux X (fun i => (h i).integrable)
    (fun i ω => exp (s * X i ω)) (fun i => (h i).integrable_exp_mul s) hs hexp
    (fun i => (h i).mgf_le s)
  refine hle.trans_eq ?_
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [log_mul hN.ne' (exp_pos _).ne', log_exp, add_div]
  congr 1
  field_simp

/-- **Sub-Gaussian maximal inequality, absolute values.** Under the hypotheses of
`integral_iSup_le_of_hasSubgaussianMGF`, for every `s > 0`,
`𝔼 maxᵢ |Xᵢ| ≤ log (2N) / s + c s / 2` (integrability:
`integrable_iSup_abs_of_hasSubgaussianMGF`). Boucheron–Lugosi–Massart 2013, Thm 2.5 (applied to
`±Xᵢ`); Vershynin 2018, Ex 2.5.10. Atlas `subgaussian-max`.-/
theorem integral_iSup_abs_le_of_hasSubgaussianMGF [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] [Nonempty ι] (X : ι → Ω → ℝ) (c : ℝ≥0)
    (h : ∀ i, HasSubgaussianMGF (X i) c μ) {s : ℝ} (hs : 0 < s) :
    ∫ ω, ⨆ i, |X i ω| ∂μ ≤ log (2 * Fintype.card ι) / s + c * s / 2 := by
  have hexp : ∀ ω, exp (s * ⨆ i, |X i ω|) ≤
      ∑ k : ι × Bool, exp ((if k.2 then s else -s) * X k.1 ω) := by
    intro ω
    obtain ⟨j, hj⟩ := exists_eq_iSup_fintype (fun i => |X i ω|)
    rw [← hj]
    have hj2 : exp (s * |X j ω|) ≤ ∑ b : Bool, exp ((if b then s else -s) * X j ω) := by
      simp only [Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
      rcases le_or_gt 0 (X j ω) with h0 | h0
      · rw [abs_of_nonneg h0]; linarith [exp_pos (-s * X j ω)]
      · rw [abs_of_neg h0, mul_neg, ← neg_mul]; linarith [exp_pos (s * X j ω)]
    refine hj2.trans ?_
    rw [Fintype.sum_prod_type]
    exact Finset.single_le_sum (f := fun i => ∑ b : Bool, exp ((if b then s else -s) * X i ω))
      (fun i _ => Finset.sum_nonneg fun _ _ => (exp_pos _).le) (Finset.mem_univ j)
  have hb : ∀ k : ι × Bool, ∫ ω, exp ((if k.2 then s else -s) * X k.1 ω) ∂μ ≤
      exp (c * s ^ 2 / 2) := by
    intro k
    have := (h k.1).mgf_le (if k.2 then s else -s)
    split_ifs at this ⊢ <;> simpa [mgf] using this
  have hle := integral_iSup_le_aux (fun i ω => |X i ω|) (fun i => (h i).integrable.abs)
    (fun (k : ι × Bool) ω => exp ((if k.2 then s else -s) * X k.1 ω))
    (fun k => (h k.1).integrable_exp_mul _) hs hexp hb
  refine hle.trans_eq ?_
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat, mul_comm _ (2 : ℝ),
    log_mul (by positivity) (exp_pos _).ne', log_exp, add_div]
  congr 1
  field_simp

private lemma le_sqrt_of_forall_le_div_add {x L c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c)
    (h : ∀ s : ℝ, 0 < s → x ≤ L / s + c * s / 2) : x ≤ √(2 * c * L) := by
  rcases hL.eq_or_lt with rfl | hL'
  · rw [mul_zero, sqrt_zero]
    by_contra hx
    push Not at hx
    have := h (x / (c + 1)) (by positivity)
    rw [zero_div, zero_add] at this
    have h1 : c * (x / (c + 1)) / 2 < x := by
      rw [mul_div_assoc', div_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  rcases hc.eq_or_lt with rfl | hc'
  · rw [mul_zero, zero_mul, sqrt_zero]
    by_contra hx
    push Not at hx
    have := h (2 * L / x) (by positivity)
    rw [zero_mul, zero_div, add_zero, div_div_eq_mul_div] at this
    have h1 : L * x / (2 * L) = x / 2 := by field_simp
    linarith
  set r := √(2 * c * L) with hr
  have hr0 : 0 < r := sqrt_pos.2 (by positivity)
  have hr2 : r * r = 2 * c * L := mul_self_sqrt (by positivity)
  have := h (r / c) (by positivity)
  have h1 : L / (r / c) + c * (r / c) / 2 = r := by
    field_simp
    nlinarith
  linarith

/-- **Sub-Gaussian maximal inequality, optimised form**: `𝔼 maxᵢ Xᵢ ≤ √(2 c log N)` for
`N = card ι ≥ 1` sub-Gaussian variables with proxy `c` (no independence needed).
Boucheron–Lugosi–Massart 2013, Thm 2.5; Vershynin 2018, Ex 2.5.10.
Atlas `subgaussian-max`.
atlas: subgaussian-max-/
theorem integral_iSup_le_sqrt_of_hasSubgaussianMGF [IsProbabilityMeasure μ] {ι : Type*}
    [Fintype ι] [Nonempty ι] (X : ι → Ω → ℝ) (c : ℝ≥0) (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    ∫ ω, ⨆ i, X i ω ∂μ ≤ √(2 * c * log (Fintype.card ι)) :=
  le_sqrt_of_forall_le_div_add (log_nonneg (by exact_mod_cast Fintype.card_pos)) c.2
    fun _ hs => integral_iSup_le_of_hasSubgaussianMGF X c h hs

/-- **Sub-Gaussian maximal inequality, absolute values, optimised form**:
`𝔼 maxᵢ |Xᵢ| ≤ √(2 c log (2N))`. Boucheron–Lugosi–Massart 2013, Thm 2.5; Vershynin 2018,
Ex 2.5.10. Atlas `subgaussian-max`.
atlas: subgaussian-max-/
theorem integral_iSup_abs_le_sqrt_of_hasSubgaussianMGF [IsProbabilityMeasure μ] {ι : Type*}
    [Fintype ι] [Nonempty ι] (X : ι → Ω → ℝ) (c : ℝ≥0) (h : ∀ i, HasSubgaussianMGF (X i) c μ) :
    ∫ ω, ⨆ i, |X i ω| ∂μ ≤ √(2 * c * log (2 * Fintype.card ι)) :=
  le_sqrt_of_forall_le_div_add
    (log_nonneg (by have : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
                    linarith)) c.2
    fun _ hs => integral_iSup_abs_le_of_hasSubgaussianMGF X c h hs

end NLAlib
