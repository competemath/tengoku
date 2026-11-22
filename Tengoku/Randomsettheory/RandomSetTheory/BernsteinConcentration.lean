/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.SubgaussianConcentration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bernstein concentration for empirical Minkowski averages

This file develops the sub-exponential counterpart of the sub-Gaussian
concentration API.  The hypothesis `HasBernsteinMGF X v b μ` is the classical
Bernstein moment-generating-function bound

`mgf X μ t ≤ exp (v t² / (2 (1 - b |t|)))`,  for `b |t| < 1`.

It is stable under independent finite sums (the variance proxies add while
the scale `b` stays fixed), contains Mathlib's sub-Gaussian MGF condition as
the special case `b = 0`, and yields the bilateral tail

`P(|X| ≥ ε) ≤ 2 exp (-ε² / (2 (v + b ε)))`.

The final results apply this scalar inequality to directional support
deviations and then use a finite net to obtain Hausdorff concentration for
empirical Minkowski averages.
-/

open Real Set Metric Finset MeasureTheory
open scoped Pointwise BigOperators InnerProductSpace ProbabilityTheory NNReal ENNReal

noncomputable section

namespace ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A real random variable satisfies a Bernstein MGF bound with variance
proxy `v` and scale proxy `b`.  The explicit a.e.-measurability field makes
the property stable under finite independent sums without requiring the
random variables to be everywhere measurable.-/
structure HasBernsteinMGF (X : Ω → ℝ) (v b : ℝ≥0)
    (μ : Measure Ω := by volume_tac) : Prop where
  aemeasurable : AEMeasurable X μ
  integrable_exp_mul : ∀ t : ℝ, (b : ℝ) * |t| < 1 →
    Integrable (fun ω => exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, (b : ℝ) * |t| < 1 →
    mgf X μ t ≤ exp ((v : ℝ) * t ^ 2 /
      (2 * (1 - (b : ℝ) * |t|)))

namespace HasBernsteinMGF

/-- A sub-Gaussian MGF is a Bernstein MGF with zero scale proxy.
@isnad1 id=hasberns.1h4v.s5.476c0435432e from=translated src=- shape=cd90fa82 vocab=a0b9e432
-/
theorem of_hasSubgaussianMGF [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasSubgaussianMGF X v μ) :
    HasBernsteinMGF X v 0 μ where
  aemeasurable := hX.aemeasurable
  integrable_exp_mul t _ := hX.integrable_exp_mul t
  mgf_le t _ := by
    simpa using hX.mgf_le t

/-- The zero random variable satisfies every zero-variance Bernstein bound.
@isnad1 id=hasberns.0h3v.s5.73fb643059c1 from=translated src=- shape=d7fcd9e3 vocab=45a77db9
-/
@[simp] theorem zero [IsProbabilityMeasure μ] (b : ℝ≥0) :
    HasBernsteinMGF (fun _ : Ω => 0) 0 b μ where
  aemeasurable := aemeasurable_const
  integrable_exp_mul t _ := by simp
  mgf_le t _ := by simp

/-- Bernstein MGF bounds are invariant under sign change.
@isnad1 id=hasberns.1h5v.s5.59dbf2368491 from=translated src=- shape=a68e8c8a vocab=524efe4e
-/
theorem neg {X : Ω → ℝ} {v b : ℝ≥0}
    (hX : HasBernsteinMGF X v b μ) :
    HasBernsteinMGF (fun ω => -X ω) v b μ where
  aemeasurable := hX.aemeasurable.neg
  integrable_exp_mul t ht := by
    have ht' : (b : ℝ) * |-t| < 1 := by simpa using ht
    simpa [mul_neg] using hX.integrable_exp_mul (-t) ht'
  mgf_le t ht := by
    have ht' : (b : ℝ) * |-t| < 1 := by simpa using ht
    rw [show (fun ω => -X ω) = -X from rfl, mgf_neg]
    simpa using hX.mgf_le (-t) ht'

/-- Congruence under almost-everywhere equality.
@isnad1 id=hasberns.2h6v.s5.fb71cc65028a from=translated src=- shape=c3b685bb vocab=d5c11269
-/
theorem congr {X Y : Ω → ℝ} {v b : ℝ≥0}
    (hX : HasBernsteinMGF X v b μ) (hXY : X =ᵐ[μ] Y) :
    HasBernsteinMGF Y v b μ where
  aemeasurable := hX.aemeasurable.congr hXY
  integrable_exp_mul t ht :=
    (hX.integrable_exp_mul t ht).congr
      (hXY.fun_comp fun x => exp (t * x))
  mgf_le t ht := by
    rw [← mgf_congr hXY]
    exact hX.mgf_le t ht

/-- Internal congruence form with the equality argument first, convenient
for finite-sum normalization.
@isnad1 id=hasberns.2h6v.s5.fb71cc65028a from=translated src=- shape=c3b685bb vocab=d5c11269
-/
theorem congr' {X Y : Ω → ℝ} {v b : ℝ≥0}
    (hX : HasBernsteinMGF X v b μ) (hXY : X =ᵐ[μ] Y) :
    HasBernsteinMGF Y v b μ := hX.congr hXY

/-- Bernstein MGF bounds are invariant under equality in distribution.
@isnad1 id=hasberns.2h8v.s5.1e3ef9c7474e from=translated src=- shape=9d81a382 vocab=f3983643
-/
theorem congr_identDistrib
    {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'}
    {X : Ω → ℝ} {Y : Ω' → ℝ} {v b : ℝ≥0}
    (hX : HasBernsteinMGF X v b μ)
    (hXY : IdentDistrib X Y μ μ') :
    HasBernsteinMGF Y v b μ' where
  aemeasurable := hXY.aemeasurable_snd
  integrable_exp_mul t ht := by
    have hident : IdentDistrib
        (fun ω => exp (t * X ω)) (fun ω => exp (t * Y ω)) μ μ' :=
      hXY.comp (measurable_const_mul t).exp
    exact hident.integrable_iff.mp (hX.integrable_exp_mul t ht)
  mgf_le t ht := by
    rw [← mgf_congr_of_identDistrib X Y hXY t]
    exact hX.mgf_le t ht

/-- Independent Bernstein variables with a common scale proxy add their
variance proxies.
@isnad1 id=hasberns.3h7v.s6.d116329c266a from=translated src=- shape=1ff533a6 vocab=f7a1996b
-/
theorem add_of_indepFun {X Y : Ω → ℝ} {vX vY b : ℝ≥0}
    (hX : HasBernsteinMGF X vX b μ)
    (hY : HasBernsteinMGF Y vY b μ)
    (hindep : IndepFun X Y μ) :
    HasBernsteinMGF (fun ω => X ω + Y ω) (vX + vY) b μ where
  aemeasurable := hX.aemeasurable.add hY.aemeasurable
  integrable_exp_mul t ht :=
    hindep.integrable_exp_mul_add
      (hX.integrable_exp_mul t ht) (hY.integrable_exp_mul t ht)
  mgf_le t ht := by
    have hXi := hX.integrable_exp_mul t ht
    have hYi := hY.integrable_exp_mul t ht
    calc
      mgf (fun ω => X ω + Y ω) μ t = mgf X μ t * mgf Y μ t :=
        hindep.mgf_add hXi.1 hYi.1
      _ ≤ exp ((vX : ℝ) * t ^ 2 / (2 * (1 - (b : ℝ) * |t|))) *
          exp ((vY : ℝ) * t ^ 2 / (2 * (1 - (b : ℝ) * |t|))) := by
        gcongr
        · exact mgf_nonneg
        · exact hX.mgf_le t ht
        · exact hY.mgf_le t ht
      _ = exp (((vX + vY : ℝ≥0) : ℝ) * t ^ 2 /
          (2 * (1 - (b : ℝ) * |t|))) := by
        rw [← exp_add]
        congr 1
        push_cast
        ring

private theorem sum_of_iIndepFun_of_forall_aemeasurable
    [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    {v : ι → ℝ≥0} (b : ℝ≥0) {s : Finset ι}
    (hB : ∀ i ∈ s, HasBernsteinMGF (X i) (v i) b μ) :
    HasBernsteinMGF (fun ω => ∑ i ∈ s, X i ω) (∑ i ∈ s, v i) b μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      have hindep' :=
        (h_indep.indepFun_finsetSum_of_notMem₀ h_meas his).symm
      have hi := hB i (Finset.mem_insert_self i s)
      have hs : ∀ j ∈ s, HasBernsteinMGF (X j) (v j) b μ :=
        fun j hj => hB j (Finset.mem_insert_of_mem hj)
      have hsum := ih hs
      have hindep'' : IndepFun (X i) (fun ω => ∑ j ∈ s, X j ω) μ := by
        convert! hindep'
        rw [Finset.sum_apply]
      simpa [Finset.sum_insert his] using hi.add_of_indepFun hsum hindep''

/-- A finite sum of independent Bernstein variables has variance proxy equal
to the sum of the individual proxies.
@isnad1 id=hasberns.2h7v.s6.91aa8ee2c620 from=translated src=- shape=99c9731e vocab=50aa5a08
-/
theorem sum_of_iIndepFun [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {v : ι → ℝ≥0} (b : ℝ≥0) {s : Finset ι}
    (hB : ∀ i ∈ s, HasBernsteinMGF (X i) (v i) b μ) :
    HasBernsteinMGF (fun ω => ∑ i ∈ s, X i ω) (∑ i ∈ s, v i) b μ := by
  have hsub : HasBernsteinMGF
      (fun ω => ∑ i : s, X i ω) (∑ i : s, v i) b μ := by
    apply sum_of_iIndepFun_of_forall_aemeasurable
    · exact h_indep.precomp Subtype.val_injective
    · exact fun i => (hB i i.2).aemeasurable
    · exact fun i _ => hB i i.2
  rw [Finset.sum_coe_sort] at hsub
  exact hsub.congr' (Filter.Eventually.of_forall fun ω =>
    Finset.sum_attach s (fun i => X i ω))

/-- One-sided Bernstein inequality obtained by optimizing the Chernoff
parameter at `t = ε / (v + b ε)`.
@isnad1 id=le.3h6v.s7.9b0cc1468c85 from=translated src=- shape=6f207c86 vocab=a6fe41f1
-/
theorem measure_ge_le [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {v b : ℝ≥0}
    (hX : HasBernsteinMGF X v b μ)
    {ε : ℝ} (hε : 0 ≤ ε) (hv : 0 < (v : ℝ)) :
    μ.real {ω | ε ≤ X ω} ≤
      exp (-ε ^ 2 / (2 * ((v : ℝ) + (b : ℝ) * ε))) := by
  let D : ℝ := (v : ℝ) + (b : ℝ) * ε
  let t : ℝ := ε / D
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have ht : 0 ≤ t := div_nonneg hε hD.le
  have hbdomain : (b : ℝ) * |t| < 1 := by
    rw [abs_of_nonneg ht]
    dsimp [t]
    rw [← mul_div_assoc]
    exact (div_lt_one hD).2 (by
      dsimp [D]
      linarith [mul_nonneg (NNReal.coe_nonneg b) hε])
  have hremain : 1 - (b : ℝ) * |t| = (v : ℝ) / D := by
    rw [abs_of_nonneg ht]
    dsimp [t, D]
    field_simp [hD.ne']
    ring
  have hexponent :
      -t * ε + (v : ℝ) * t ^ 2 /
          (2 * (1 - (b : ℝ) * |t|)) =
        -ε ^ 2 / (2 * D) := by
    rw [hremain]
    dsimp [t]
    field_simp [hD.ne', hv.ne']
    ring
  calc
    μ.real {ω | ε ≤ X ω} ≤ exp (-t * ε) * mgf X μ t :=
      measure_ge_le_exp_mul_mgf ε ht (hX.integrable_exp_mul t hbdomain)
    _ ≤ exp (-t * ε) *
        exp ((v : ℝ) * t ^ 2 / (2 * (1 - (b : ℝ) * |t|))) := by
      gcongr
      exact hX.mgf_le t hbdomain
    _ = exp (-ε ^ 2 / (2 * D)) := by
      rw [← exp_add, hexponent]
    _ = exp (-ε ^ 2 / (2 * ((v : ℝ) + (b : ℝ) * ε))) := rfl

/-- Bilateral Bernstein inequality.
@isnad1 id=le.3h6v.s7.585974b44f1a from=translated src=- shape=d8d75d2c vocab=2c4339ba
-/
theorem measure_abs_ge_le [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {v b : ℝ≥0}
    (hX : HasBernsteinMGF X v b μ)
    {ε : ℝ} (hε : 0 ≤ ε) (hv : 0 < (v : ℝ)) :
    μ.real {ω | ε ≤ |X ω|} ≤
      2 * exp (-ε ^ 2 / (2 * ((v : ℝ) + (b : ℝ) * ε))) := by
  let Xneg : Ω → ℝ := fun ω => -X ω
  have hpos := hX.measure_ge_le hε hv
  have hneg := hX.neg.measure_ge_le hε hv
  have hset : {ω | ε ≤ |X ω|} =
      {ω | ε ≤ X ω} ∪ {ω | ε ≤ Xneg ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, Xneg]
    rw [le_abs]
  rw [hset]
  calc
    _ ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ Xneg ω} :=
      measureReal_union_le _ _
    _ ≤ exp (-ε ^ 2 / (2 * ((v : ℝ) + (b : ℝ) * ε))) +
        exp (-ε ^ 2 / (2 * ((v : ℝ) + (b : ℝ) * ε))) :=
      add_le_add hpos hneg
    _ = 2 * exp (-ε ^ 2 / (2 * ((v : ℝ) + (b : ℝ) * ε))) := by ring

/-- Confidence-parameter form of the bilateral Bernstein inequality.  The
square-root plus linear threshold is the form most often used in statistical
applications.
@isnad1 id=le.3h6v.s7.db1760cfdbfa from=translated src=- shape=dfaf7016 vocab=44fbfdf4
-/
theorem measure_abs_ge_sqrt_add_le [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {v b : ℝ≥0}
    (hX : HasBernsteinMGF X v b μ)
    {x : ℝ} (hx : 0 ≤ x) (hv : 0 < (v : ℝ)) :
    μ.real {ω |
        Real.sqrt (2 * (v : ℝ) * x) + 2 * (b : ℝ) * x ≤ |X ω|} ≤
      2 * exp (-x) := by
  let ε : ℝ := Real.sqrt (2 * (v : ℝ) * x) + 2 * (b : ℝ) * x
  have hε : 0 ≤ ε := by
    dsimp [ε]
    positivity
  have hsqrt_sq : (Real.sqrt (2 * (v : ℝ) * x)) ^ 2 =
      2 * (v : ℝ) * x := by
    rw [sq_sqrt]
    positivity
  have hquad :
      2 * x * ((v : ℝ) + (b : ℝ) * ε) ≤ ε ^ 2 := by
    apply sub_nonneg.mp
    have heq :
        ε ^ 2 - 2 * x * ((v : ℝ) + (b : ℝ) * ε) =
          2 * (b : ℝ) * x * Real.sqrt (2 * (v : ℝ) * x) := by
      calc
        ε ^ 2 - 2 * x * ((v : ℝ) + (b : ℝ) * ε) =
            Real.sqrt (2 * (v : ℝ) * x) ^ 2 - 2 * (v : ℝ) * x +
              2 * (b : ℝ) * x * Real.sqrt (2 * (v : ℝ) * x) := by
                dsimp [ε]
                ring
        _ = 2 * (b : ℝ) * x * Real.sqrt (2 * (v : ℝ) * x) := by
          rw [hsqrt_sq]
          ring
    rw [heq]
    positivity
  have hden : 0 < 2 * ((v : ℝ) + (b : ℝ) * ε) := by
    positivity
  have hratio :
      x ≤ ε ^ 2 / (2 * ((v : ℝ) + (b : ℝ) * ε)) := by
    rw [le_div_iff₀ hden]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hquad
  have htail := hX.measure_abs_ge_le hε hv
  change μ.real {ω | ε ≤ |X ω|} ≤ 2 * exp (-x)
  exact htail.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by simpa [neg_div] using neg_le_neg hratio))
    (by positivity))

end HasBernsteinMGF

/-- Bilateral Bernstein tail for a finite sum of independent real random
variables with a common scale proxy.
@isnad1 id=le.4h8v.s7.2bc547a71159 from=translated src=- shape=d058d998 vocab=7280cb18
-/
theorem bernstein_finset_sum_abs_real [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (v : ι → ℝ≥0) (b : ℝ≥0)
    (h_indep : iIndepFun X μ)
    (s : Finset ι)
    (hB : ∀ i ∈ s, HasBernsteinMGF (X i) (v i) b μ)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hV : 0 < ((∑ i ∈ s, v i : ℝ≥0) : ℝ)) :
    μ.real {ω | ε ≤ |∑ i ∈ s, X i ω|} ≤
      2 * exp (-ε ^ 2 /
        (2 * (((∑ i ∈ s, v i : ℝ≥0) : ℝ) + (b : ℝ) * ε))) := by
  exact (HasBernsteinMGF.sum_of_iIndepFun h_indep b hB).measure_abs_ge_le hε hV

/-- Bilateral Bernstein tail for an arithmetic average over a nonempty
finite index set.
@isnad1 id=le.5h8v.s8.732fd1326e68 from=translated src=- shape=e85b323c vocab=9761e907
-/
theorem bernstein_finset_average_abs_real [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (v : ι → ℝ≥0) (b : ℝ≥0)
    (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty)
    (hB : ∀ i ∈ s, HasBernsteinMGF (X i) (v i) b μ)
    {t : ℝ} (ht : 0 ≤ t)
    (hV : 0 < ((∑ i ∈ s, v i : ℝ≥0) : ℝ)) :
    μ.real {ω | t ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} ≤
      2 * exp (-((s.card : ℝ) * t) ^ 2 /
        (2 * (((∑ i ∈ s, v i : ℝ≥0) : ℝ) +
          (b : ℝ) * ((s.card : ℝ) * t)))) := by
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hs)
  have htail := bernstein_finset_sum_abs_real X v b h_indep s hB
    (mul_nonneg hcard.le ht) hV
  have hset : {ω | t ≤ |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} =
      {ω | (s.card : ℝ) * t ≤ |∑ i ∈ s, X i ω|} := by
    ext ω
    simp only [mem_ofPred_eq, abs_div, abs_of_pos hcard]
    rw [le_div_iff₀ hcard]
    ring_nf
  rw [hset]
  exact htail

/-- Confidence-parameter form for a finite average.  The deviation threshold
is `(sqrt (2 V x) + 2 b x) / n`, where `V` is the sum of the variance
proxies.
@isnad1 id=le.5h8v.s8.f37ade60dbd1 from=translated src=- shape=c7bc1c02 vocab=4d24a0f4
-/
theorem bernstein_finset_average_abs_sqrt_add_real [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (v : ι → ℝ≥0) (b : ℝ≥0)
    (h_indep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty)
    (hB : ∀ i ∈ s, HasBernsteinMGF (X i) (v i) b μ)
    {x : ℝ} (hx : 0 ≤ x)
    (hV : 0 < ((∑ i ∈ s, v i : ℝ≥0) : ℝ)) :
    μ.real {ω |
        (Real.sqrt (2 * ((∑ i ∈ s, v i : ℝ≥0) : ℝ) * x) +
            2 * (b : ℝ) * x) / (s.card : ℝ) ≤
          |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} ≤
      2 * exp (-x) := by
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hs)
  have hsum : HasBernsteinMGF
      (fun ω => ∑ i ∈ s, X i ω) (∑ i ∈ s, v i) b μ :=
    HasBernsteinMGF.sum_of_iIndepFun h_indep b hB
  have htail := hsum.measure_abs_ge_sqrt_add_le hx hV
  have hset :
      {ω |
        (Real.sqrt (2 * ((∑ i ∈ s, v i : ℝ≥0) : ℝ) * x) +
            2 * (b : ℝ) * x) / (s.card : ℝ) ≤
          |(∑ i ∈ s, X i ω) / (s.card : ℝ)|} =
      {ω | Real.sqrt (2 * ((∑ i ∈ s, v i : ℝ≥0) : ℝ) * x) +
          2 * (b : ℝ) * x ≤ |∑ i ∈ s, X i ω|} := by
    ext ω
    simp only [mem_ofPred_eq, abs_div, abs_of_pos hcard]
    exact div_le_div_iff_of_pos_right hcard
  rw [hset]
  exact htail

end ProbabilityTheory

namespace RandomSetTheory

variable {Ω ι E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Directional Bernstein concentration for an empirical Minkowski average.
The variance proxies may depend on the observation index, while the scale
proxy is common.
@isnad1 id=le.7h11v.s8.1c65f1eece42 from=translated src=- shape=b5662cb4 vocab=8243b4c4
-/
theorem minkowskiAverage_support_bernstein
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E) (u : E)
    (v : ι → ℝ≥0) (b : ℝ≥0)
    (h_indep : ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L u) μ)
    (s : Finset ι) (hs : s.Nonempty)
    (hB : ∀ i ∈ s, ProbabilityTheory.HasBernsteinMGF
      (directionalSupportDeviation S L u i) (v i) b μ)
    (hV : 0 < ((∑ i ∈ s, v i : ℝ≥0) : ℝ))
    (hScompact : ∀ i ∈ s, ∀ ω, IsCompact (S i ω))
    (hSne : ∀ i ∈ s, ∀ ω, (S i ω).Nonempty)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u|} ≤
      2 * exp (-((s.card : ℝ) * t) ^ 2 /
        (2 * (((∑ i ∈ s, v i : ℝ≥0) : ℝ) +
          (b : ℝ) * ((s.card : ℝ) * t)))) := by
  have htail := ProbabilityTheory.bernstein_finset_average_abs_real
    (directionalSupportDeviation S L u) v b h_indep s hs hB ht hV
  have hset :
      {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
        supportFunction L u|} =
      {ω | t ≤ |(∑ i ∈ s, directionalSupportDeviation S L u i ω) /
        (s.card : ℝ)|} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [supportFunction_minkowskiAverage_sub_eq_average_deviation
      S L s hs hScompact hSne]
  rw [hset]
  exact htail

/-- Directional confidence-parameter Bernstein bound.
@isnad1 id=le.7h11v.s8.8b82218653ef from=translated src=- shape=035fbf22 vocab=f82f8edb
-/
theorem minkowskiAverage_support_bernstein_sqrt_add
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E) (u : E)
    (v : ι → ℝ≥0) (b : ℝ≥0)
    (h_indep : ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L u) μ)
    (s : Finset ι) (hs : s.Nonempty)
    (hB : ∀ i ∈ s, ProbabilityTheory.HasBernsteinMGF
      (directionalSupportDeviation S L u i) (v i) b μ)
    (hV : 0 < ((∑ i ∈ s, v i : ℝ≥0) : ℝ))
    (hScompact : ∀ i ∈ s, ∀ ω, IsCompact (S i ω))
    (hSne : ∀ i ∈ s, ∀ ω, (S i ω).Nonempty)
    {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω |
        (Real.sqrt (2 * ((∑ i ∈ s, v i : ℝ≥0) : ℝ) * x) +
            2 * (b : ℝ) * x) / (s.card : ℝ) ≤
          |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
            supportFunction L u|} ≤
      2 * exp (-x) := by
  have htail := ProbabilityTheory.bernstein_finset_average_abs_sqrt_add_real
    (directionalSupportDeviation S L u) v b h_indep s hs hB hx hV
  have hset :
      {ω |
        (Real.sqrt (2 * ((∑ i ∈ s, v i : ℝ≥0) : ℝ) * x) +
            2 * (b : ℝ) * x) / (s.card : ℝ) ≤
          |supportFunction (minkowskiAverage s (fun i => S i ω)) u -
            supportFunction L u|} =
      {ω |
        (Real.sqrt (2 * ((∑ i ∈ s, v i : ℝ≥0) : ℝ) * x) +
            2 * (b : ℝ) * x) / (s.card : ℝ) ≤
          |(∑ i ∈ s, directionalSupportDeviation S L u i ω) /
            (s.card : ℝ)|} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [supportFunction_minkowskiAverage_sub_eq_average_deviation
      S L s hs hScompact hSne]
  rw [hset]
  exact htail

/-- Finite-net Hausdorff Bernstein concentration for empirical Minkowski
averages.  This is the sub-exponential analogue of
`hausdorffDist_minkowskiAverage_risk_bound_of_subgaussian`.
@isnad1 id=le.15h14v.s9.7d4cf92ee992 from=translated src=- shape=b4431ad6 vocab=f536a368
-/
theorem hausdorffDist_minkowskiAverage_risk_bound_of_bernstein
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E)
    (s : Finset ι) (hs : s.Nonempty)
    (v : ι → ℝ≥0) (b : ℝ≥0)
    {RS RL eps t : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ x ∈ S i ω, ‖x‖ ≤ RS)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 ≤ eps) (ht : 0 ≤ t)
    (N : Finset E)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ w ∈ N, dist u w ≤ eps)
    (h_indep : ∀ w ∈ N, ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L w) μ)
    (hB : ∀ w ∈ N, ∀ i ∈ s, ProbabilityTheory.HasBernsteinMGF
      (directionalSupportDeviation S L w i) (v i) b μ)
    (hV : 0 < ((∑ i ∈ s, v i : ℝ≥0) : ℝ)) :
    μ.real {ω | t + (RS + RL) * eps <
        hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      N.card * (2 * exp (-((s.card : ℝ) * t) ^ 2 /
        (2 * (((∑ i ∈ s, v i : ℝ≥0) : ℝ) +
          (b : ℝ) * ((s.card : ℝ) * t))))) := by
  apply measureReal_hausdorffDist_gt_le_finset_support
    (μ := μ) (fun ω => minkowskiAverage s (fun i => S i ω)) (fun _ => L)
    (fun ω => isCompact_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hScompact i ω))
    (fun _ => hLcompact)
    (fun ω => nonempty_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hSne i ω))
    (fun _ => hLne)
    (fun ω => convex_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hSconv i ω))
    (fun _ => hLconv)
    (fun ω x hx => norm_le_radius_of_mem_nonempty_minkowskiAverage s hs
      (fun i => S i ω) (fun i hi => hRS i ω) hx)
    (fun _ => hRL) heps ht
    (by positivity)
    N hnet
  intro w hw
  calc
    μ.real {ω | t < |supportFunction (minkowskiAverage s (fun i => S i ω)) w -
        supportFunction L w|} ≤
        μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) w -
          supportFunction L w|} := by
      apply measureReal_mono
      · intro ω hω
        change t < |supportFunction (minkowskiAverage s (fun i => S i ω)) w -
          supportFunction L w| at hω
        change t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) w -
          supportFunction L w|
        exact hω.le
      · finiteness
    _ ≤ 2 * exp (-((s.card : ℝ) * t) ^ 2 /
        (2 * (((∑ i ∈ s, v i : ℝ≥0) : ℝ) +
          (b : ℝ) * ((s.card : ℝ) * t)))) :=
      minkowskiAverage_support_bernstein S L w v b
        (h_indep w hw) s hs (hB w hw) hV
        (fun i _hi ω => hScompact i ω)
        (fun i _hi ω => hSne i ω) ht

/-- Finite-net Hausdorff Bernstein inequality in confidence-parameter form.
It exhibits directly the classical square-root plus linear deviation rate.
@isnad1 id=le.15h14v.s9.4cd65f94498c from=translated src=- shape=2908da18 vocab=9c3235ea
-/
theorem hausdorffDist_minkowskiAverage_risk_bound_bernstein_sqrt_add
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (S : ι → Ω → Set E) (L : Set E)
    (s : Finset ι) (hs : s.Nonempty)
    (v : ι → ℝ≥0) (b : ℝ≥0)
    {RS RL eps x : ℝ}
    (hScompact : ∀ i ω, IsCompact (S i ω))
    (hSne : ∀ i ω, (S i ω).Nonempty)
    (hSconv : ∀ i ω, Convex ℝ (S i ω))
    (hLcompact : IsCompact L) (hLne : L.Nonempty) (hLconv : Convex ℝ L)
    (hRS : ∀ i ω, ∀ y ∈ S i ω, ‖y‖ ≤ RS)
    (hRL : ∀ y ∈ L, ‖y‖ ≤ RL)
    (heps : 0 ≤ eps) (hx : 0 ≤ x)
    (N : Finset E)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ w ∈ N, dist u w ≤ eps)
    (h_indep : ∀ w ∈ N, ProbabilityTheory.iIndepFun
      (directionalSupportDeviation S L w) μ)
    (hB : ∀ w ∈ N, ∀ i ∈ s, ProbabilityTheory.HasBernsteinMGF
      (directionalSupportDeviation S L w i) (v i) b μ)
    (hV : 0 < ((∑ i ∈ s, v i : ℝ≥0) : ℝ)) :
    μ.real {ω |
        (Real.sqrt (2 * ((∑ i ∈ s, v i : ℝ≥0) : ℝ) * x) +
            2 * (b : ℝ) * x) / (s.card : ℝ) + (RS + RL) * eps <
          hausdorffDist (minkowskiAverage s (fun i => S i ω)) L} ≤
      N.card * (2 * exp (-x)) := by
  let t : ℝ :=
    (Real.sqrt (2 * ((∑ i ∈ s, v i : ℝ≥0) : ℝ) * x) +
      2 * (b : ℝ) * x) / (s.card : ℝ)
  have hcard : 0 < (s.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hs)
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  apply measureReal_hausdorffDist_gt_le_finset_support
    (μ := μ) (fun ω => minkowskiAverage s (fun i => S i ω)) (fun _ => L)
    (fun ω => isCompact_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hScompact i ω))
    (fun _ => hLcompact)
    (fun ω => nonempty_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hSne i ω))
    (fun _ => hLne)
    (fun ω => convex_minkowskiAverage s (fun i => S i ω)
      (fun i hi => hSconv i ω))
    (fun _ => hLconv)
    (fun ω y hy => norm_le_radius_of_mem_nonempty_minkowskiAverage s hs
      (fun i => S i ω) (fun i hi => hRS i ω) hy)
    (fun _ => hRL) heps ht
    (by positivity)
    N hnet
  intro w hw
  calc
    μ.real {ω | t < |supportFunction (minkowskiAverage s (fun i => S i ω)) w -
        supportFunction L w|} ≤
        μ.real {ω | t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) w -
          supportFunction L w|} := by
      apply measureReal_mono
      · intro ω hω
        change t < |supportFunction (minkowskiAverage s (fun i => S i ω)) w -
          supportFunction L w| at hω
        change t ≤ |supportFunction (minkowskiAverage s (fun i => S i ω)) w -
          supportFunction L w|
        exact hω.le
      · finiteness
    _ ≤ 2 * exp (-x) := by
      dsimp [t]
      exact minkowskiAverage_support_bernstein_sqrt_add
        S L w v b (h_indep w hw) s hs (hB w hw) hV
        (fun i _hi ω => hScompact i ω)
        (fun i _hi ω => hSne i ω) hx

end RandomSetTheory
