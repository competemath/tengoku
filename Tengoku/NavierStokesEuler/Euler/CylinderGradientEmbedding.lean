import Tengoku.NavierStokesEuler.Euler.CylinderSpatialEmbedding
import Tengoku.NavierStokesEuler.Euler.MeanSolenoidalSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual constant-angle embedding preserves the closed gradient
spaces.  Compact ordinary scalar tests give compact cylinder scalar tests,
and the bounded embedding carries their closures into one another. -/

noncomputable section

namespace EulerCylinderSpatialEmbedding

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]

def scalarLift (φ : Space → ℝ) : LiftDomain P → ℝ := fun z => φ z.1

/--
@isnad1 id=hascompa.1h2v.s7.3e180c2d8737 from=translated src=- shape=b0cbc96b vocab=19850062
-/
theorem scalarLift_compact (φ : Space → ℝ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (scalarLift P φ) := by
  apply HasCompactSupport.intro (hφ.prod (isCompact_univ : IsCompact (univ : Set (AddCircle P))))
  intro z hz
  change φ z.1 = 0
  exact image_eq_zero_of_notMem_tsupport (by simpa only [mem_prod,mem_univ,and_true] using hz)

omit [Fact (0 < P)] in
/--
@isnad1 id=contdiff.1h3v.s8.fc9ddcf00cbe from=translated src=- shape=81a8cdcf vocab=b64e0151
-/
theorem scalarLift_smooth (φ : Space → ℝ) (hφ : ContDiff ℝ ∞ φ) (z : LiftDomain P) :
    ContDiff ℝ ∞ (localLift P (scalarLift P φ) z) :=
  hφ.comp (contDiff_const.add contDiff_fst)

/--
@isnad1 id=eq.0h3v.s9.35265c558966 from=translated src=- shape=d770a4a4 vocab=4879d55a
-/
theorem gradient_component (φ : Space → ℝ) (x : Space) (i : Fin 3) :
    gradient φ x i = fderiv ℝ φ x (EuclideanSpace.single i 1) := by
  have h := toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single i 1) (y := fderiv ℝ φ x)
  simpa only [gradient,EuclideanSpace.inner_single_right,conj_trivial,one_mul] using h

omit [Fact (0 < P)] in
/--
@isnad1 id=eq.1h5v.s8.a1604f02be0d from=translated src=- shape=7e81eccb vocab=4b076742
-/
theorem scalarLift_gradient (κ : ℝ) (m : Space) (φ : Space → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (z : LiftDomain P) :
    liftedGradient P κ m (scalarLift P φ) z = κ • gradient φ z.1 := by
  have hh : HasFDerivAt (fun y : LiftTangent => z.1+y.1) (fst ℝ Space ℝ) 0 :=
    hasFDerivAt_fst.const_add z.1
  have hf : HasFDerivAt φ (fderiv ℝ φ z.1) (z.1+(0 : LiftTangent).1) := by
    simpa only [Prod.fst_zero,add_zero] using ((hφ.differentiable (by simp)) z.1).hasFDerivAt
  have h := hf.comp (0 : LiftTangent) hh
  have hd : fderiv ℝ (localLift P (scalarLift P φ) z) 0 =
      (fderiv ℝ φ z.1).comp (fst ℝ Space ℝ) := by
    convert! h.fderiv using 1
  ext i
  change κ * (fderiv ℝ (localLift P (scalarLift P φ) z) 0) (EuclideanSpace.single i 1,0) +
    m i * (fderiv ℝ (localLift P (scalarLift P φ) z) 0) (0,1) = κ * gradient φ z.1 i
  rw [hd,gradient_component]
  change κ * fderiv ℝ φ z.1 (EuclideanSpace.single i 1) + m i * fderiv ℝ φ z.1 0 = _
  rw [map_zero,mul_zero,add_zero]

/--
@isnad1 id=mem.1h4v.s17.c86dbd7eba4e from=translated src=- shape=71071a5a vocab=151223c8
-/
theorem smul_embedding_gradient_mem (κ : ℝ) (m : Space)
    (g : EulerMeanSolenoidal.L2) (hg : g ∈ EulerMeanSolenoidal.gradientSpace) :
    κ • embedding P g ∈ gradientSpace P κ m := by
  let L : EulerMeanSolenoidal.L2 →L[ℝ] LiftL2 P := κ • embedding P
  let K := (gradientSpace P κ m).comap L.toLinearMap
  have hgen : Submodule.span ℝ EulerMeanSolenoidal.gradientGenerators ≤ K := by
    apply Submodule.span_le.mpr
    rintro u ⟨φ,hφc,hφs,hu⟩
    change κ • embedding P u ∈ gradientSpace P κ m
    apply testGradient_mem P κ m
    refine ⟨scalarLift P φ,⟨scalarLift_compact P φ hφc,scalarLift_smooth P φ hφs⟩,?_⟩
    filter_upwards [Lp.coeFn_smul κ (embedding P u),lift_ae P u,
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space))
        (ν := (volume : Measure (AddCircle P)))).ae hu] with z hs hl hz
    change (κ • embedding P u) z = _
    rw [hs]
    change κ • embedding P u z = _
    rw [show embedding P u z = u z.1 from hl,hz,scalarLift_gradient P κ m φ hφs]
  have hclosed : IsClosed (K : Set EulerMeanSolenoidal.L2) :=
    (gradientSpace_closed P κ m).preimage L.continuous
  exact ((Submodule.span ℝ EulerMeanSolenoidal.gradientGenerators).topologicalClosure_minimal
    hgen hclosed) hg

/--
@isnad1 id=mem.2h4v.s16.88ff28d9c94d from=translated src=- shape=603b8ffe vocab=c6f25e7e
-/
theorem embedding_gradient_mem (κ : ℝ) (hκ : κ ≠ 0) (m : Space)
    (g : EulerMeanSolenoidal.L2) (hg : g ∈ EulerMeanSolenoidal.gradientSpace) :
    embedding P g ∈ gradientSpace P κ m := by
  have h := (gradientSpace P κ m).smul_mem κ⁻¹ (smul_embedding_gradient_mem P κ m g hg)
  simpa only [smul_smul,inv_mul_cancel₀ hκ,one_smul] using h

end EulerCylinderSpatialEmbedding
