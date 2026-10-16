import Tengoku.NavierStokesEuler.Euler.CylinderSpatialMean
import Tengoku.NavierStokesEuler.Euler.CylinderAngleAverageRepresentative

/-! The bounded cylinder-to-space operator is the literal angular integral on smooth fields. -/

noncomputable section

namespace EulerCylinderSpatialMean

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderSpatialEmbedding EulerCylinderAngleAverage
  EulerCylinderSobolevSpace EulerSobolevPointEvaluation

variable (P : ℝ) [Fact (0 < P)]

/-- A continuous constant-angle field is spatially L² whenever its cylinder lift is L². -/
theorem continuous_memLp_of_lift {V : Type*} [NormedAddCommGroup V]
    (g : Space → V) (hg : Continuous g)
    (hgl : MemLp (fun z : LiftDomain P => g z.1) 2 (liftMeasure P)) :
    MemLp g 2 (volume : Measure Space) := by
  have hm : MemLp g 2 (Measure.map (Prod.fst : LiftDomain P → Space) (liftMeasure P)) :=
    (memLp_map_measure_iff hg.aestronglyMeasurable measurable_fst.aemeasurable).mpr hgl
  change MemLp g 2 (Measure.map Prod.fst
    ((volume : Measure Space).prod (volume : Measure (AddCircle P)))) at hm
  rw [Measure.map_fst_prod, AddCircle.measure_univ] at hm
  have hP : ENNReal.ofReal P ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (Fact.out : 0 < P))
  have hu := hm.smul_measure (c := (ENNReal.ofReal P)⁻¹) (ENNReal.inv_ne_top.mpr hP)
  simpa only [smul_smul, ENNReal.inv_mul_cancel hP ENNReal.ofReal_ne_top, one_smul] using hu

def rawMean (f : LiftDomain P → Space) (y : Space) : Space :=
  P⁻¹ • (∫ s in (0 : ℝ)..P, f (y,(s : AddCircle P)))

variable (u : SobolevSpace P 3) (f : LiftDomain P → Space) (hf : Continuous f)
  (hrep : (value P u : LiftDomain P → Space) =ᵐ[liftMeasure P] f)

include hf hrep

end EulerCylinderSpatialMean
