import Tengoku.Seed.Dynamics.Ergodic.Action.Basic
import Tengoku.Seed.Dynamics.Ergodic.Function
import Tengoku.Seed.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniqueness of absolutely continuous invariant currents

Group ergodicity, together with absolute continuity, forces an invariant
sigma-finite measure to be a scalar multiple of the reference measure. Neither
measure needs finite total mass. This does not prove Hopf ergodicity or absolute
continuity for the geometric currents in the singularity argument.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Singularity

variable {G X : Type*} [MeasurableSpace X]

/-- A measurable function invariant almost everywhere under an ergodic group
of transformations is almost everywhere constant.
@isnad1 id=ex.2h5v.s6.355960a6ed4b from=translated src=- shape=38b5f31e vocab=00a21ed3
-/
theorem ergodicSMul_ae_eq_const [SMul G X] (μ : Measure X) [ErgodicSMul G X μ]
    {Y : Type*} [MeasurableSpace Y] [MeasurableSpace.CountablySeparated Y] [Nonempty Y]
    (F : X → Y) (hF : Measurable F)
    (hi : ∀ g : G, (fun x => F (g • x)) =ᵐ[μ] F) :
    ∃ c, F =ᵐ[μ] Function.const X c := by
  apply exists_eventuallyEq_const_of_forall_separating MeasurableSet
  intro U hU
  apply eventuallyConst_set.mp
  apply aeconst_of_forall_preimage_smul_ae_eq G (hF hU).nullMeasurableSet
  intro g
  filter_upwards [hi g] with x hx
  change (F (g • x) ∈ U) = (F x ∈ U)
  rw [hx]

/-- Invariance of both measures makes their Radon–Nikodym derivative invariant.
Invertibility permits sigma-finite measures, without a finite-mass assumption.
@isnad1 id=eventual.0h5v.s7.c4a158f28959 from=translated src=- shape=69bfb9db vocab=06db18a4
-/
theorem invariant_rnDeriv_smul [Group G] [MulAction G X] [MeasurableConstSMul G X]
    (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    [SMulInvariantMeasure G X μ] [SMulInvariantMeasure G X ν] (g : G) :
    (fun x => ν.rnDeriv μ (g • x)) =ᵐ[μ] ν.rnDeriv μ := by
  have h := (MeasurableEquiv.smul g).measurableEmbedding.rnDeriv_map ν μ
  change (fun x => (Measure.map (fun x => g • x) ν).rnDeriv
    (Measure.map (fun x => g • x) μ) (g • x)) =ᵐ[μ] ν.rnDeriv μ at h
  simpa only [(measurePreserving_smul g ν).map_eq,
    (measurePreserving_smul g μ).map_eq] using h

/-- Ergodicity and absolute continuity give uniqueness up to a scalar for
invariant sigma-finite measures, including currents of infinite total mass.
@isnad1 id=ex.1h4v.s7.3480f1eaba4b from=translated src=- shape=3788f974 vocab=d84def05
-/
theorem invariantMeasure_eq_smul_of_ergodic [Group G] [MulAction G X]
    [MeasurableConstSMul G X] (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    [ErgodicSMul G X μ] [SMulInvariantMeasure G X ν] (hac : ν ≪ μ) :
    ∃ c : ℝ≥0∞, ν = c • μ := by
  obtain ⟨c, hc⟩ := ergodicSMul_ae_eq_const (G := G) μ (ν.rnDeriv μ)
    (Measure.measurable_rnDeriv ν μ) (invariant_rnDeriv_smul μ ν)
  refine ⟨c, ?_⟩
  rw [← Measure.withDensity_rnDeriv_eq ν μ hac, withDensity_congr_ae hc]
  exact withDensity_const c

/-- If both invariant measures are nonzero, the scalar is strictly positive and
finite. Sigma-finiteness excludes an infinite constant density.
@isnad1 id=ex.1h4v.s7.a74ca5c85256 from=translated src=- shape=8bbe9a9d vocab=c7abec14
-/
theorem invariantMeasure_eq_pos_finite_smul_of_ergodic [Group G] [MulAction G X]
    [MeasurableConstSMul G X] (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    [NeZero μ] [NeZero ν] [ErgodicSMul G X μ] [SMulInvariantMeasure G X ν]
    (hac : ν ≪ μ) : ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ ν = c • μ := by
  obtain ⟨c, hc⟩ := ergodicSMul_ae_eq_const (G := G) μ (ν.rnDeriv μ)
    (Measure.measurable_rnDeriv ν μ) (invariant_rnDeriv_smul μ ν)
  have heq : ν = c • μ := by
    rw [← Measure.withDensity_rnDeriv_eq ν μ hac, withDensity_congr_ae hc]
    exact withDensity_const c
  have hpos : 0 < c := by
    apply pos_iff_ne_zero.mpr
    intro hzero
    exact NeZero.ne ν (by simpa [hzero] using heq)
  obtain ⟨x, hx, hxt⟩ := (hc.and (Measure.rnDeriv_lt_top ν μ)).exists
  exact ⟨c, hpos, by simpa only [hx, Function.const_apply] using hxt, heq⟩

/-- A pushforward-invariance proof can be used directly in the uniqueness
criterion, without supplying an invariant-measure instance separately.
@isnad1 id=ex.2h4v.s7.89927a292fb4 from=translated src=- shape=b2355808 vocab=002488cd
-/
theorem invariantMeasure_eq_pos_finite_smul_of_maps [Group G] [MulAction G X]
    [MeasurableConstSMul G X] (μ ν : Measure X) [SigmaFinite μ] [SigmaFinite ν]
    [NeZero μ] [NeZero ν] [ErgodicSMul G X μ]
    (hi : ∀ g : G, Measure.map (fun x => g • x) ν = ν) (hac : ν ≪ μ) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧ ν = c • μ := by
  let : SMulInvariantMeasure G X ν := ⟨fun g A hA => by
    rw [← Measure.map_apply (measurable_const_smul g) hA, hi g]⟩
  exact invariantMeasure_eq_pos_finite_smul_of_ergodic (G := G) μ ν hac

end Singularity
