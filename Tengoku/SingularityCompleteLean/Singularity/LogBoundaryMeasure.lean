import Tengoku.SingularityCompleteLean.Singularity.CurrentComparison
import Tengoku.SingularityCompleteLean.Singularity.LiouvilleFourier
import Tengoku.Seed.MeasureTheory.Function.JacobianOneDim
import Tengoku.Seed.Analysis.SpecialFunctions.ExpDeriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Logarithmic coordinates for boundary measures

The maps t ↦ exp(t) and t ↦ -exp(t) parametrize the positive and negative
boundary half-lines. The Jacobian identities below are identities of measures,
so they apply even to currents with infinite mass.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Singularity

/-- A density pulled back along a measurable map commutes with pushforward.
@isnad1 id=eq.2h5v.s6.a0144b18da1a from=translated src=- shape=e298f8d9 vocab=0eccf0dc
-/
theorem map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (hf : Measurable f) (m : Measure X) (w : Y → ℝ≥0∞)
    (hw : Measurable w) :
    Measure.map f (m.withDensity (w ∘ f)) = (Measure.map f m).withDensity w := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map hh hf, lintegral_withDensity_eq_lintegral_mul _ (hw.comp hf)
      (show Measurable (fun x => h (f x)) from hh.comp hf),
    lintegral_withDensity_eq_lintegral_mul _ hw hh, lintegral_map (hw.mul hh) hf]
  rfl

/-- Exponential coordinates transport exp(t) dt to Lebesgue measure on (0,∞).
@isnad1 id=eq.0h0v.s5.e48df7ddc48d from=translated src=- shape=997f01cc vocab=2e71926b
-/
theorem exp_jacobian_map :
    Measure.map Real.exp (volume.withDensity (fun t : ℝ => ENNReal.ofReal (Real.exp t))) =
      volume.restrict (Ioi (0 : ℝ)) := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map hh Real.measurable_exp,
    lintegral_withDensity_eq_lintegral_mul _ Real.measurable_exp.ennreal_ofReal
      (show Measurable (fun x => h (Real.exp x)) from hh.comp Real.measurable_exp)]
  simpa only [image_univ, Real.range_exp, Measure.restrict_univ,
    abs_of_pos (Real.exp_pos _), Pi.mul_apply] using
    (lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn h).symm

/-- The negative exponential parametrizes precisely the negative half-line.
@isnad1 id=eq.0h0v.s4.6530993d5388 from=translated src=- shape=bc10f8d9 vocab=f790144f
-/
theorem range_neg_exp : range (fun t : ℝ => -Real.exp t) = Iio 0 := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact neg_neg_of_pos (Real.exp_pos t)
  · intro hx
    exact ⟨Real.log (-x), by simp only [Real.exp_log (neg_pos.mpr hx), neg_neg]⟩

/-- Negative exponential coordinates have absolute Jacobian exp(t).
@isnad1 id=eq.0h0v.s5.60b78556e08a from=translated src=- shape=bc9d8185 vocab=636e80a4
-/
theorem neg_exp_jacobian_map :
    Measure.map (fun t : ℝ => -Real.exp t)
      (volume.withDensity (fun t : ℝ => ENNReal.ofReal (Real.exp t))) =
      volume.restrict (Iio (0 : ℝ)) := by
  apply Measure.ext_of_lintegral
  intro h hh
  have hm : Measurable (fun t : ℝ => -Real.exp t) := Real.measurable_exp.neg
  rw [lintegral_map hh hm,
    lintegral_withDensity_eq_lintegral_mul _ Real.measurable_exp.ennreal_ofReal
      (show Measurable (fun x => h (-Real.exp x)) from hh.comp hm)]
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => -Real.exp t) (-Real.exp x) x :=
    (Real.hasDerivAt_exp x).neg
  simpa only [image_univ, range_neg_exp, Measure.restrict_univ, abs_neg,
    abs_of_pos (Real.exp_pos _), Pi.mul_apply] using
    (lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
      (fun x _ => (hd x).hasDerivWithinAt)
      (neg_injective.comp Real.exp_injective).injOn h).symm

/-- Coordinates for an ordered boundary pair on opposite sides of zero.-/
def logBoundaryPair (z : ℝ × ℝ) : ℝ × ℝ := (-Real.exp z.1, Real.exp z.2)

/--
@isnad1 id=measurab.0h0v.s4.0482deb44cf9 from=translated src=- shape=31244855 vocab=9e98a7b6
-/
theorem measurable_logBoundaryPair : Measurable logBoundaryPair := by
  exact (Real.measurable_exp.neg.comp measurable_fst).prodMk
    (Real.measurable_exp.comp measurable_snd)

/-- The two-dimensional Jacobian is exp(s) exp(t).
@isnad1 id=eq.0h0v.s6.9aac6f4b2f86 from=translated src=- shape=8617562e vocab=80a89c5f
-/
theorem logBoundaryPair_jacobian_map :
    Measure.map logBoundaryPair ((volume.prod volume).withDensity
      (fun z : ℝ × ℝ => ENNReal.ofReal (Real.exp z.1 * Real.exp z.2))) =
    (volume.restrict (Iio (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))) := by
  have hm : Measurable (fun t : ℝ => -Real.exp t) := Real.measurable_exp.neg
  have h := Measure.map_prod_map
    (volume.withDensity (fun t : ℝ => ENNReal.ofReal (Real.exp t)))
    (volume.withDensity (fun t : ℝ => ENNReal.ofReal (Real.exp t)))
    hm Real.measurable_exp
  rw [neg_exp_jacobian_map, exp_jacobian_map,
    prod_withDensity Real.measurable_exp.ennreal_ofReal Real.measurable_exp.ennreal_ofReal] at h
  have hf : Prod.map (fun t : ℝ => -Real.exp t) Real.exp = logBoundaryPair := by
    funext z
    rfl
  rw [hf] at h
  simpa only [ENNReal.ofReal_mul (Real.exp_pos _).le] using h.symm

/-- Weighted change of variables for the two boundary half-lines.
@isnad1 id=eq.1h1v.s7.273a621a3a85 from=translated src=- shape=58627c47 vocab=b4b4371f
-/
theorem logBoundaryPair_weighted_map (w : ℝ × ℝ → ℝ≥0∞) (hw : Measurable w) :
    Measure.map logBoundaryPair ((volume.prod volume).withDensity
      (fun z : ℝ × ℝ => ENNReal.ofReal (Real.exp z.1 * Real.exp z.2) *
        w (logBoundaryPair z))) =
    ((volume.restrict (Iio (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))).withDensity w := by
  have h := map_withDensity_comp logBoundaryPair measurable_logBoundaryPair
    ((volume.prod volume).withDensity
      (fun z : ℝ × ℝ => ENNReal.ofReal (Real.exp z.1 * Real.exp z.2))) w hw
  rw [logBoundaryPair_jacobian_map, ← withDensity_mul _ (by fun_prop)
    (hw.comp measurable_logBoundaryPair)] at h
  exact h

/-- The Jacobian times the classical Liouville density is the kernel already
used in the Fourier calculation.
@isnad1 id=eq.0h2v.s6.ce7e41ecd849 from=translated src=- shape=8acdd977 vocab=3c2634a9
-/
theorem logBoundaryPair_liouville_density (s t : ℝ) :
    Real.exp s * Real.exp t * (1 / ((-Real.exp s) - Real.exp t) ^ 2) =
      liouvilleKernel (s - t) := by
  unfold liouvilleKernel
  rw [neg_sub, Real.exp_sub]
  have hs := Real.exp_pos s
  have ht := Real.exp_pos t
  rw [show (-Real.exp s - Real.exp t) ^ 2 = (Real.exp s + Real.exp t) ^ 2 by ring]
  have hr : 1 + Real.exp t / Real.exp s = (Real.exp s + Real.exp t) / Real.exp s := by
    field_simp
  rw [hr, div_pow, div_div]
  field_simp [ne_of_gt hs, ne_of_gt (add_pos hs ht)]

/-- The classical Liouville density in the finite real boundary chart.-/
def realLiouvilleDensity (z : ℝ × ℝ) : ℝ := 1 / (z.1 - z.2) ^ 2

/--
@isnad1 id=measurab.0h0v.s3.44193b4a12eb from=translated src=- shape=8e22ceaf vocab=f7a318d9
-/
theorem measurable_realLiouvilleDensity : Measurable realLiouvilleDensity := by
  unfold realLiouvilleDensity
  fun_prop

/-- Pushing forward the cosh-kernel measure in logarithmic coordinates gives
the classical Liouville current restricted to opposite half-lines.
@isnad1 id=eq.0h0v.s7.e3aebe80ff2f from=translated src=- shape=fe31cf75 vocab=c3b17baa
-/
theorem logBoundaryPair_liouville_map :
    Measure.map logBoundaryPair ((volume.prod volume).withDensity
      (fun z : ℝ × ℝ => ENNReal.ofReal (liouvilleKernel (z.1 - z.2)))) =
    ((volume.restrict (Iio (0 : ℝ))).prod
      (volume.restrict (Ioi (0 : ℝ)))).withDensity
      (fun z => ENNReal.ofReal (realLiouvilleDensity z)) := by
  have h := logBoundaryPair_weighted_map
    (fun z => ENNReal.ofReal (realLiouvilleDensity z))
    measurable_realLiouvilleDensity.ennreal_ofReal
  have hd : (fun z : ℝ × ℝ => ENNReal.ofReal (Real.exp z.1 * Real.exp z.2) *
      ENNReal.ofReal (realLiouvilleDensity (logBoundaryPair z))) =
      (fun z => ENNReal.ofReal (liouvilleKernel (z.1 - z.2))) := by
    funext z
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact congrArg ENNReal.ofReal (logBoundaryPair_liouville_density z.1 z.2)
  rw [hd] at h
  exact h

/-- The logarithmic chart is a measurable embedding, so equality of its
pushforward measures implies equality of the original measures.
@isnad1 id=measurab.0h0v.s4.3b54ac2d3a2a from=translated src=- shape=31244855 vocab=4d4f4b8b
-/
theorem measurableEmbedding_logBoundaryPair : MeasurableEmbedding logBoundaryPair := by
  have he := Real.isOpenEmbedding_exp.measurableEmbedding
  have hn : MeasurableEmbedding (fun t : ℝ => -Real.exp t) :=
    (Homeomorph.neg ℝ).measurableEmbedding.comp he
  have h := hn.prodMap he
  have hf : Prod.map (fun t : ℝ => -Real.exp t) Real.exp = logBoundaryPair := by
    funext z
    rfl
  rwa [hf] at h

/-- Null sets for product Lebesgue measure remain null on logarithmic pullback.
@isnad1 id=quasimea.0h0v.s5.0d1463d620a9 from=translated src=- shape=483074d5 vocab=49047b20
-/
theorem quasiMeasurePreserving_logBoundaryPair :
    Measure.QuasiMeasurePreserving logBoundaryPair (volume.prod volume) (volume.prod volume) := by
  have hp : ∀ᵐ z : ℝ × ℝ ∂volume.prod volume, 0 < Real.exp z.1 * Real.exp z.2 :=
    Filter.Eventually.of_forall (fun z => mul_pos (Real.exp_pos z.1) (Real.exp_pos z.2))
  have hac := ((positive_real_weight_measureClass (volume.prod volume)
    (fun z : ℝ × ℝ => Real.exp z.1 * Real.exp z.2) (by fun_prop) hp).2).map
      measurable_logBoundaryPair
  rw [logBoundaryPair_jacobian_map, Measure.prod_restrict] at hac
  exact ⟨measurable_logBoundaryPair, hac.trans Measure.absolutelyContinuous_restrict⟩

end Singularity
