module

public import Tengoku.AtPalomar.Paper.RSFunctional
public import Tengoku.Seed.MeasureTheory.Function.LocallyIntegrable
public import Tengoku.Seed.Analysis.Convex.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# The probability-measure and convex-analysis parts of the JT criterion

The support/minimum statement below is proved for the genuine probability
measures on the compact overlap interval. The later convex-analysis theorem
isolates the first variation and segment convexity as ordinary hypotheses;
identification with the general weak Parisi PDE is a separate obligation.
-/

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace Paper

/-- The set of global minimizers on the actual overlap interval.-/
def overlapArgmin (G : Overlap → ℝ) : Set Overlap :=
  {x | ∀ y : Overlap, G x ≤ G y}

/-- A continuous observable on the overlap interval is integrable against
every actual Parisi probability measure.
@isnad1 id=integrab.1h2v.s6.3b00278785dc from=translated src=- shape=75d40cb6 vocab=caacf301
-/
theorem integrable_overlap_continuous {G : Overlap → ℝ} (hG : Continuous G)
    (μ : ParisiMeasure) : Integrable G (μ : Measure Overlap) := by
  simpa only [IntegrableOn, Measure.restrict_univ] using
    hG.continuousOn.integrableOn_compact (μ := (μ : Measure Overlap)) isCompact_univ

/--
@isnad1 id=isclosed.1h1v.s5.26d8761ae9b9 from=translated src=- shape=3a58a77f vocab=57bc9cbd
-/
theorem isClosed_overlapArgmin {G : Overlap → ℝ} (hG : Continuous G) :
    IsClosed (overlapArgmin G) := by
  have heq : overlapArgmin G = ⋂ y : Overlap, {x | G x ≤ G y} := by
    ext x
    simp only [overlapArgmin, mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact isClosed_iInter (fun _ => isClosed_le hG continuous_const)

/--
@isnad1 id=isprobab.1h3v.s8.67330684d2b1 from=translated src=- shape=e4a5a660 vocab=ad0b2c98
-/
theorem parisiMix_probability (μ ν : ParisiMeasure) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) : IsProbabilityMeasure
      (ENNReal.ofReal (1 - t) • (μ : Measure Overlap) +
        ENNReal.ofReal t • (ν : Measure Overlap)) := by
  apply isProbabilityMeasure_iff.mpr
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr ht.2) ht.1]
  simp

/-- The actual convex mixing variation of probability measures on `[0,1]`.
Outside the parameter interval it is extended by its initial measure;
only its restriction to `[0,1]` and right derivative at zero are used.-/
noncomputable def parisiMix (μ ν : ParisiMeasure) (t : ℝ) : ParisiMeasure :=
  if ht : t ∈ Icc (0 : ℝ) 1 then
    ⟨ENNReal.ofReal (1 - t) • (μ : Measure Overlap) +
      ENNReal.ofReal t • (ν : Measure Overlap), parisiMix_probability μ ν t ht⟩
  else μ

/--
@isnad1 id=eq.1h3v.s8.6ddcf59e6d70 from=translated src=- shape=aeba8027 vocab=ff6ae399
-/
theorem parisiMix_measure (μ ν : ParisiMeasure) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (parisiMix μ ν t : Measure Overlap) =
      ENNReal.ofReal (1 - t) • (μ : Measure Overlap) +
        ENNReal.ofReal t • (ν : Measure Overlap) := by
  simp [parisiMix, ht]

/--
@isnad1 id=eq.0h2v.s4.99ef0b7f18c1 from=translated src=- shape=f56bb0f5 vocab=9aa948bc
-/
@[simp] theorem parisiMix_zero (μ ν : ParisiMeasure) : parisiMix μ ν 0 = μ := by
  apply Subtype.ext
  change (parisiMix μ ν 0 : Measure Overlap) = (μ : Measure Overlap)
  rw [parisiMix_measure μ ν 0 (by constructor <;> norm_num)]
  simp

/--
@isnad1 id=eq.0h2v.s4.05dc14c538de from=translated src=- shape=cc48e823 vocab=9aa948bc
-/
@[simp] theorem parisiMix_one (μ ν : ParisiMeasure) : parisiMix μ ν 1 = ν := by
  apply Subtype.ext
  change (parisiMix μ ν 1 : Measure Overlap) = (ν : Measure Overlap)
  rw [parisiMix_measure μ ν 1 (by constructor <;> norm_num)]
  simp

/-- Integrating along a genuine probability mixing variation gives the
usual affine formula, including both endpoints.
@isnad1 id=eq.2h4v.s8.252554502b6b from=translated src=- shape=437d87c0 vocab=a9f55fa1
-/
theorem integral_parisiMix {G : Overlap → ℝ} (hG : Continuous G)
    (μ ν : ParisiMeasure) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ x, G x ∂(parisiMix μ ν t : Measure Overlap)) =
      (1 - t) * (∫ x, G x ∂(μ : Measure Overlap)) +
        t * (∫ x, G x ∂(ν : Measure Overlap)) := by
  rw [parisiMix_measure μ ν t ht]
  rw [integral_add_measure
    ((integrable_overlap_continuous hG μ).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_overlap_continuous hG ν).smul_measure ENNReal.ofReal_ne_top)]
  rw [integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2), ENNReal.toReal_ofReal ht.1]
  rfl

/-- The genuine CDF of a mixing variation is affine in its mixing parameter.
This holds even when either measure has atoms or a discontinuous CDF.
@isnad1 id=eq.1h4v.s6.3aa51c94a531 from=translated src=- shape=baada04a vocab=021e829e
-/
theorem parisiCDF_mix (μ ν : ParisiMeasure) (t s : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    parisiCDF (parisiMix μ ν t) s = (1 - t) * parisiCDF μ s + t * parisiCDF ν s := by
  unfold parisiCDF
  rw [parisiMix_measure μ ν t ht]
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (μ : Measure Overlap) _))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (ν : Measure Overlap) _))]
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2), ENNReal.toReal_ofReal ht.1]

/-- The complete CDF correction integral is affine under actual probability
mixing. Its integrability is proved for each measure rather than assumed.
@isnad1 id=eq.1h3v.s7.20e947d1d67b from=translated src=- shape=6ab977aa vocab=ebd496a6
-/
theorem parisiCorrection_integral_mix (μ ν : ParisiMeasure) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..1, s * parisiCDF (parisiMix μ ν t) s) =
      (1 - t) * (∫ s in (0 : ℝ)..1, s * parisiCDF μ s) +
        t * (∫ s in (0 : ℝ)..1, s * parisiCDF ν s) := by
  have hfun : (fun s : ℝ => s * parisiCDF (parisiMix μ ν t) s) =
      (fun s => (1 - t) * (s * parisiCDF μ s) + t * (s * parisiCDF ν s)) := by
    funext s
    rw [parisiCDF_mix μ ν t s ht]
    ring
  rw [hfun, intervalIntegral.integral_add
    ((parisiCorrection_intervalIntegrable μ 0 1).const_mul (1 - t))
    ((parisiCorrection_intervalIntegrable ν 0 1).const_mul t),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

/-- A local affine identity supplies the right endpoint derivative of a
mixing variation, without making any assertion outside `[0,1]`.
@isnad1 id=hasderiv.1h3v.s7.3ca032cdb8e5 from=translated src=- shape=c3df41f0 vocab=b64359f7
-/
theorem hasDerivWithinAt_of_affine_mixing {f : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, f t = (1 - t) * a + t * b) :
    HasDerivWithinAt f (b - a) (Ioi (0 : ℝ)) 0 := by
  have hd : HasDerivAt (fun t : ℝ => (1 - t) * a + t * b) (b - a) 0 := by
    convert (((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0)).mul_const a).add
      ((hasDerivAt_id 0).mul_const b) using 1 <;> first | rfl | ring
  apply hd.hasDerivWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)) (a := (0 : ℝ)))] with t ht ht1
    exact hf t ⟨ht.le, ht1.le⟩
  · exact hf 0 (by constructor <;> norm_num)

/-- Actual first variation of a continuous linear observable along the
probability mixing path.
@isnad1 id=hasderiv.1h3v.s8.e045d7c604ca from=translated src=- shape=b8cbe3e1 vocab=8074087c
-/
theorem hasDerivWithinAt_integral_parisiMix {G : Overlap → ℝ} (hG : Continuous G)
    (μ ν : ParisiMeasure) :
    HasDerivWithinAt (fun t => ∫ x, G x ∂(parisiMix μ ν t : Measure Overlap))
      ((∫ x, G x ∂(ν : Measure Overlap)) - ∫ x, G x ∂(μ : Measure Overlap))
      (Ioi (0 : ℝ)) 0 :=
  hasDerivWithinAt_of_affine_mixing (integral_parisiMix hG μ ν)

/-- Actual first variation of the Parisi CDF correction. Only the potential
part remains to be identified with the PDE first variation.
@isnad1 id=hasderiv.0h3v.s8.be3a3a80bd61 from=translated src=- shape=14c49956 vocab=55db1fc9
-/
theorem hasDerivWithinAt_parisiCorrection_mix (β : ℝ) (μ ν : ParisiMeasure) :
    HasDerivWithinAt
      (fun t => β ^ 2 / 2 * ∫ s in (0 : ℝ)..1, s * parisiCDF (parisiMix μ ν t) s)
      (β ^ 2 / 2 * ((∫ s in (0 : ℝ)..1, s * parisiCDF ν s) -
        ∫ s in (0 : ℝ)..1, s * parisiCDF μ s)) (Ioi (0 : ℝ)) 0 :=
  (hasDerivWithinAt_of_affine_mixing (parisiCorrection_integral_mix μ ν)).const_mul _

/-- The elementary convex one-sided derivative criterion used by JT.
The derivative is genuinely at the endpoint from the right.
@isnad1 id=iff.2h2v.s7.ec5420aabf99 from=translated src=- shape=9aa32041 vocab=b8525621
-/
theorem convex_minimum_iff_right_deriv_nonneg {f : ℝ → ℝ} {d : ℝ}
    (hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) f)
    (hderiv : HasDerivWithinAt f d (Ioi (0 : ℝ)) 0) :
    (∀ t ∈ Icc (0 : ℝ) 1, f 0 ≤ f t) ↔ 0 ≤ d := by
  constructor
  · intro hmin
    have hslope := (hasDerivWithinAt_iff_tendsto_slope' (self_notMem_Ioi :
      (0 : ℝ) ∉ Ioi (0 : ℝ))).mp hderiv
    apply ge_of_tendsto hslope
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)) (a := (0 : ℝ)))] with t ht ht1
    rw [slope_def_field, sub_zero]
    exact div_nonneg (sub_nonneg.mpr (hmin t ⟨ht.le, ht1.le⟩)) ht.le
  · intro hd t ht
    rcases ht.1.eq_or_lt with hzero | hpos
    · simp only [← hzero, le_refl]
    · have hs := hconv.le_slope_of_hasDerivWithinAt_Ioi
        (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) ht hpos hderiv
      rw [slope_def_field, sub_zero] at hs
      have hproduct := (le_div_iff₀ hpos).mp hs
      have hn := mul_nonneg hd hpos.le
      linarith

/-- For a functional convex along all genuine probability mixing variations,
nonnegative first variations are equivalent to global minimality.
@isnad1 id=iff.2h3v.s7.dcd507f3a7bb from=translated src=- shape=4b44e291 vocab=f102e835
-/
theorem functional_minimum_iff_variations_nonneg (P : ParisiMeasure → ℝ)
    (μ : ParisiMeasure) (D : ParisiMeasure → ℝ)
    (hconv : ∀ ν : ParisiMeasure,
      ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => P (parisiMix μ ν t)))
    (hderiv : ∀ ν : ParisiMeasure,
      HasDerivWithinAt (fun t => P (parisiMix μ ν t)) (D ν) (Ioi (0 : ℝ)) 0) :
    (∀ ν : ParisiMeasure, P μ ≤ P ν) ↔ ∀ ν : ParisiMeasure, 0 ≤ D ν := by
  constructor
  · intro hmin ν
    apply (convex_minimum_iff_right_deriv_nonneg (hconv ν) (hderiv ν)).mp
    intro t ht
    simpa only [parisiMix_zero] using hmin (parisiMix μ ν t)
  · intro hD ν
    have hminimum := (convex_minimum_iff_right_deriv_nonneg
      (hconv ν) (hderiv ν)).mpr (hD ν)
    simpa only [parisiMix_zero, parisiMix_one] using
      hminimum 1 (by constructor <;> norm_num)

end Paper
