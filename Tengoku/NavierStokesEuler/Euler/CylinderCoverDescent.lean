import Tengoku.NavierStokesEuler.Euler.CylinderMeasureDescent

/-! Canonical descent of periodic cover fields and deck-equivariant maps
to the cylinder, with genuine continuity, inverse and volume properties. -/

noncomputable section

namespace EulerCylinderCoverDescent

open Set Function MeasureTheory EulerLiftedGradientSpace

variable (P : ℝ) [Fact (0 < P)]

def sectionPoint (q : LiftDomain P) : LiftTangent :=
  (q.1,(AddCircle.equivIoc P 0 q.2 : ℝ))

/--
@isnad1 id=eq.0h2v.s4.a89b73f62089 from=translated src=- shape=d039a2f7 vocab=e80c7ea8
-/
theorem coveringMap_sectionPoint (q : LiftDomain P) : coveringMap P (sectionPoint P q)=q := by
  simp only [sectionPoint,coveringMap,AddCircle.coe_equivIoc,Prod.mk.eta]

/--
@isnad1 id=measurab.0h1v.s7.20e5ad31507b from=translated src=- shape=f1c80f4f vocab=c55ddeb4
-/
theorem sectionPoint_measurable : Measurable (sectionPoint P) :=
  measurable_fst.prodMk ((measurable_subtype_coe.comp
    (AddCircle.measurableEquivIoc P 0).measurable).comp measurable_snd)

def descend {V : Type*} (f : LiftTangent → V) (q : LiftDomain P) : V := f (sectionPoint P q)

/--
@isnad1 id=eq.1h4v.s5.e3a656272534 from=translated src=- shape=40a60c77 vocab=4c6f880a
-/
theorem descend_cover {V : Type*} (f : LiftTangent → V)
    (hf : ∀ a b, coveringMap P a=coveringMap P b → f a=f b) (z : LiftTangent) :
    descend P f (coveringMap P z)=f z :=
  hf _ _ (coveringMap_sectionPoint P (coveringMap P z))

/--
@isnad1 id=measurab.1h3v.s7.333c7adcf81c from=translated src=- shape=f2a4033b vocab=a221ec2e
-/
theorem descend_measurable {V : Type*} [MeasurableSpace V] (f : LiftTangent → V)
    (hf : Measurable f) : Measurable (descend P f) := hf.comp (sectionPoint_measurable P)

/--
@isnad1 id=continuo.2h3v.s7.c797d2b697f5 from=translated src=- shape=b2c83f3b vocab=b6a5b4dd
-/
theorem descend_continuous {V : Type*} [TopologicalSpace V] (f : LiftTangent → V)
    (hf : Continuous f) (he : ∀ a b, coveringMap P a=coveringMap P b → f a=f b) :
    Continuous (descend P f) := by
  apply (coveringMap_isOpenQuotient P).isQuotientMap.continuous_iff.mpr
  have h : descend P f ∘ coveringMap P = f := funext (descend_cover P f he)
  rw [h]
  exact hf

/--
@isnad1 id=continuo.2h4v.s7.af4a129b1f38 from=translated src=- shape=cf34c695 vocab=d0f5da66
-/
theorem descend_joint_continuous {K V : Type*} [TopologicalSpace K] [TopologicalSpace V]
    (f : K → LiftTangent → V) (hf : Continuous (Function.uncurry f))
    (he : ∀ t a b, coveringMap P a=coveringMap P b → f t a=f t b) :
    Continuous (fun z : K × LiftDomain P => descend P (f z.1) z.2) := by
  apply (IsOpenQuotientMap.id.prodMap (coveringMap_isOpenQuotient P)).isQuotientMap.continuous_iff.mpr
  have h : (fun z : K × LiftDomain P => descend P (f z.1) z.2) ∘
      Prod.map id (coveringMap P) = Function.uncurry f := by
    funext z
    exact descend_cover P (f z.1) (he z.1) z.2
  rw [h]
  exact hf

omit [Fact (0 < P)] in
/--
@isnad1 id=eq.2h5v.s6.e8277b5067a8 from=translated src=- shape=a6381142 vocab=1d34f5d7
-/
theorem fiber_constant_of_deck {V : Type*} (f : LiftTangent → V)
    (hf : ∀ (c : AddSubgroup.zmultiples P) z, f (z.1,(c : ℝ)+z.2)=f z)
    (a b : LiftTangent) (h : coveringMap P a=coveringMap P b) : f a=f b := by
  have h₁ : a.1=b.1 := congrArg (fun q : LiftDomain P => q.1) h
  have h₂ : (a.2 : AddCircle P)=(b.2 : AddCircle P) :=
    congrArg (fun q : LiftDomain P => q.2) h
  have hm : a.2-b.2 ∈ AddSubgroup.zmultiples P := QuotientAddGroup.eq_iff_sub_mem.mp h₂
  let c : AddSubgroup.zmultiples P := ⟨a.2-b.2,hm⟩
  have hz : (b.1,(c : ℝ)+b.2)=a := by
    apply Prod.ext
    · exact h₁.symm
    · exact sub_add_cancel a.2 b.2
  rw [← hz]
  exact hf c b

def descendMap (f : LiftTangent → LiftTangent) : LiftDomain P → LiftDomain P :=
  descend P (coveringMap P ∘ f)

variable (f : LiftTangent → LiftTangent)
  (hdeck : ∀ (c : AddSubgroup.zmultiples P) z,
    f (z.1,(c : ℝ)+z.2)=((f z).1,(c : ℝ)+(f z).2))

include hdeck in
omit [Fact (0 < P)] in
/--
@isnad1 id=eq.2h4v.s7.65d3df1c9ebb from=translated src=- shape=0c8d30df vocab=1d34f5d7
-/
theorem map_fiber_constant (a b : LiftTangent) (h : coveringMap P a=coveringMap P b) :
    coveringMap P (f a)=coveringMap P (f b) := by
  apply fiber_constant_of_deck P (coveringMap P ∘ f) _ a b h
  intro c z
  change coveringMap P (f (z.1,(c : ℝ)+z.2))=coveringMap P (f z)
  rw [hdeck]
  exact EulerCylinderMeasureDescent.coveringMap_deck P c (f z)

include hdeck in
/--
@isnad1 id=eq.1h3v.s7.dfae5686e263 from=translated src=- shape=7ef69cec vocab=0845a495
-/
theorem descendMap_cover (z : LiftTangent) :
    descendMap P f (coveringMap P z)=coveringMap P (f z) :=
  descend_cover P (coveringMap P ∘ f) (map_fiber_constant P f hdeck) z

include hdeck in
/--
@isnad1 id=continuo.2h2v.s8.b45f3376b49f from=translated src=- shape=ec858477 vocab=c0318357
-/
theorem descendMap_continuous (hf : Continuous f) : Continuous (descendMap P f) :=
  descend_continuous P _ ((coveringMap_isOpenQuotient P).continuous.comp hf)
    (map_fiber_constant P f hdeck)

include hdeck in
/--
@isnad1 id=measurep.2h2v.s9.548b52d43925 from=translated src=- shape=52588158 vocab=02c56f32
-/
theorem descendMap_measurePreserving (hf : MeasurePreserving f volume volume) :
    MeasurePreserving (descendMap P f) (liftMeasure P) (liftMeasure P) :=
  EulerCylinderMeasureDescent.measurePreserving_of_cover P f (descendMap P f) hf
    (descend_measurable P _ ((coveringMap_isOpenQuotient P).continuous.measurable.comp hf.measurable))
    hdeck (fun z => (descendMap_cover P f hdeck z).symm)

include hdeck in
/--
@isnad1 id=leftinve.3h3v.s8.e41d5f64413c from=translated src=- shape=f56b4c92 vocab=5b930de1
-/
theorem descendMap_leftInverse (g : LiftTangent → LiftTangent)
    (hg : ∀ (c : AddSubgroup.zmultiples P) z,
      g (z.1,(c : ℝ)+z.2)=((g z).1,(c : ℝ)+(g z).2))
    (hgf : Function.LeftInverse g f) :
    Function.LeftInverse (descendMap P g) (descendMap P f) := by
  intro q
  obtain ⟨z,rfl⟩ := (coveringMap_isOpenQuotient P).surjective q
  rw [descendMap_cover P f hdeck,descendMap_cover P g hg,hgf]

end EulerCylinderCoverDescent
