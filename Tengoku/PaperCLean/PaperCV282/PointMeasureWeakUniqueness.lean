import Tengoku.PaperCLean.PaperCV282.PointMeasureSpace
import Tengoku.Seed.MeasureTheory.Measure.LevyProkhorovMetric

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Uniqueness of the weak law of genuine finite point measures

Finite measures are embedded topologically into a probability measure and a
positive mass after adding one fixed Dirac mass. This proves the missing
metrizability instance from existing weak-topology and normalization facts.
-/
namespace PaperC.V282.PointMeasureWeakUniqueness

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace PointMeasureSpace
open scoped Topology NNReal BoundedContinuousFunction

noncomputable section

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]

/--
@isnad1 id=eq.0h4v.s7.db29fe554f41 from=translated src=- shape=b89f342f vocab=5fdd6a48
-/
theorem finite_integral_add (mu nu : FiniteMeasure X) (f : X →ᵇ ℝ) :
    (∫ x,f x ∂(mu+nu : FiniteMeasure X))=(∫ x,f x ∂mu)+(∫ x,f x ∂nu) := by
  rw [FiniteMeasure.toMeasure_add,integral_add_measure (f.integrable _) (f.integrable _)]

/-- Removing a fixed finite summand preserves weak convergence.
@isnad1 id=tendsto.1h6v.s6.b9a222cb910f from=translated src=- shape=a4041341 vocab=898575d8
-/
theorem tendsto_of_add_constant {α : Type*} {l : Filter α} (mu : α→FiniteMeasure X)
    (target extra : FiniteMeasure X)
    (h : Tendsto (fun i => mu i+extra) l (𝓝 (target+extra))) :
    Tendsto mu l (𝓝 target) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hi := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp h f
  simp_rw [finite_integral_add] at hi
  simpa only [add_sub_cancel_right] using hi.sub_const (∫ x,f x ∂extra)

omit [TopologicalSpace X] [BorelSpace X] in
/--
@isnad1 id=ne.0h3v.s5.e93e48e6c431 from=translated src=- shape=a851ef48 vocab=f522b81d
-/
theorem shifted_nonzero (x : X) (mu : FiniteMeasure X) :
    mu+(diracProba x).toFiniteMeasure≠0 := by
  intro he
  have hm := congrArg (fun v : FiniteMeasure X => v.mass) he
  change (mu+(diracProba x).toFiniteMeasure) Set.univ=0 at hm
  simp only [FiniteMeasure.coeFn_add,Pi.add_apply] at hm
  change mu.mass+(diracProba x).toFiniteMeasure.mass=0 at hm
  rw [ProbabilityMeasure.mass_toFiniteMeasure] at hm
  exact (by positivity : mu.mass+(1 : ℝ≥0)≠0) hm

def probabilityMassEncoding [Nonempty X] (x : X) (mu : FiniteMeasure X) :
    ProbabilityMeasure X × ℝ≥0 :=
  ((mu+(diracProba x).toFiniteMeasure).normalize,(mu+(diracProba x).toFiniteMeasure).mass)

/--
@isnad1 id=iff.0h6v.s6.0407f441401e from=translated src=- shape=1ae7edd0 vocab=f54f6cb2
-/
theorem encoding_tendsto_iff [Nonempty X] (x : X) {α : Type*} {l : Filter α}
    (mu : α→FiniteMeasure X) (target : FiniteMeasure X) :
    Tendsto (fun i => probabilityMassEncoding x (mu i)) l (𝓝 (probabilityMassEncoding x target)) ↔
      Tendsto mu l (𝓝 target) := by
  rw [probabilityMassEncoding,Prod.tendsto_iff]
  change (Tendsto (fun i => (mu i+(diracProba x).toFiniteMeasure).normalize) l
    (𝓝 (target+(diracProba x).toFiniteMeasure).normalize) ∧
    Tendsto (fun i => (mu i+(diracProba x).toFiniteMeasure).mass) l
    (𝓝 (target+(diracProba x).toFiniteMeasure).mass)) ↔ _
  rw [FiniteMeasure.tendsto_normalize_iff_tendsto (shifted_nonzero x target)]
  exact ⟨tendsto_of_add_constant mu target _,fun h => h.add_const _⟩

/--
@isnad1 id=isinduci.0h2v.s5.854975bc0fad from=translated src=- shape=dc63f6e8 vocab=f99e66af
-/
theorem isInducing_encoding [Nonempty X] (x : X) :
    IsInducing (probabilityMassEncoding x) := by
  apply isInducing_iff_nhds.mpr
  intro mu
  apply le_antisymm
  · exact ((encoding_tendsto_iff x id mu).mpr tendsto_id).le_comap
  · have h : Tendsto id (Filter.comap (probabilityMassEncoding x)
        (𝓝 (probabilityMassEncoding x mu))) (𝓝 mu) :=
      (encoding_tendsto_iff x id mu).mp tendsto_comap
    simpa only [Filter.tendsto_id'] using h

/-- The actual weak topology of finite measures is pseudo-metrizable on a separable metrizable base.
@isnad1 id=pseudome.0h1v.s5.e208ed8ac092 from=translated src=- shape=2b22752e vocab=5d2b9e8a
-/
instance instPseudoMetrizableFinite [Nonempty X] [PseudoMetrizableSpace X] [SeparableSpace X] :
    PseudoMetrizableSpace (FiniteMeasure X) :=
  (isInducing_encoding (Classical.choice (inferInstance : Nonempty X))).pseudoMetrizableSpace

/--
@isnad1 id=pseudome.0h1v.s5.2c8458a51a14 from=translated src=- shape=2b22752e vocab=2b38833a
-/
instance instPseudoMetrizablePoint [Nonempty X] [PseudoMetrizableSpace X] [SeparableSpace X] :
    PseudoMetrizableSpace (PointMeasure X) :=
  inferInstanceAs (PseudoMetrizableSpace (FiniteMeasure X))

/--
@isnad1 id=t2space.0h1v.s5.da4b687b2e95 from=translated src=- shape=dea3ad65 vocab=95718845
-/
instance instT2PointLaws [Nonempty X] [PseudoMetrizableSpace X] [SeparableSpace X] :
    T2Space (ProbabilityMeasure (PointMeasure X)) := by infer_instance

/-- Weak convergence of point-configuration laws has a unique genuine probability limit.
@isnad1 id=eq.2h6v.s7.cc5430ca649f from=translated src=- shape=75866f93 vocab=c914512f
-/
theorem point_law_limit_unique [Nonempty X] [PseudoMetrizableSpace X] [SeparableSpace X]
    {α : Type*} {l : Filter α} [l.NeBot] (laws : α→ProbabilityMeasure (PointMeasure X))
    (mu nu : ProbabilityMeasure (PointMeasure X))
    (hmu : Tendsto laws l (𝓝 mu)) (hnu : Tendsto laws l (𝓝 nu)) : mu=nu :=
  tendsto_nhds_unique hmu hnu

end
end PaperC.V282.PointMeasureWeakUniqueness
