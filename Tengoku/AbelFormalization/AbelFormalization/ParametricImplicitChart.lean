import Tengoku.AbelFormalization.AbelFormalization.ParametricKernelCoordinates
import Tengoku.Seed.Analysis.Calculus.ImplicitContDiff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open Set Function Filter
open scoped Topology ContDiff

namespace AbelFormalization

set_option autoImplicit false

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

def parametricImplicitData
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hSurj : (fderiv ℝ Phi p).range = ⊤) :
    ImplicitFunctionData ℝ (X × Y) Z (fderiv ℝ Phi p).ker :=
  (hPhi.hasStrictFDerivAt one_ne_zero).implicitFunctionDataOfComplemented
    Phi (fderiv ℝ Phi p) hSurj
      (fderiv ℝ Phi p).ker_closedComplemented_of_finiteDimensional_range

def parametricImplicitChart
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hSurj : (fderiv ℝ Phi p).range = ⊤) :
    OpenPartialHomeomorph (X × Y)
      (Z × (fderiv ℝ Phi p).ker) :=
  (parametricImplicitData Phi p hPhi hSurj).toOpenPartialHomeomorph

/--
@isnad1 id=eq.2h6v.s11.004b38650311 from=translated src=- shape=37eaaaa1 vocab=e9c92fe9
-/
@[simp]
theorem parametricImplicitChart_fst
    (Phi : X × Y → Z) (p q : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hSurj : (fderiv ℝ Phi p).range = ⊤) :
    (parametricImplicitChart Phi p hPhi hSurj q).1 = Phi q := by
  rfl

/--
@isnad1 id=mem.2h5v.s12.d748f47a78ea from=translated src=- shape=04a0d5f5 vocab=ffedd593
-/
theorem parametricImplicitChart_base_mem_source
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hSurj : (fderiv ℝ Phi p).range = ⊤) :
    p ∈ (parametricImplicitChart Phi p hPhi hSurj).source := by
  exact (parametricImplicitData Phi p hPhi hSurj).pt_mem_toOpenPartialHomeomorph_source

/--
@isnad1 id=eq.2h5v.s12.63ffbac9882a from=translated src=- shape=313d9436 vocab=1ce7eac2
-/
theorem parametricImplicitChart_base_image
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hSurj : (fderiv ℝ Phi p).range = ⊤) :
    parametricImplicitChart Phi p hPhi hSurj p = (Phi p, 0) := by
  simp [parametricImplicitChart, parametricImplicitData,
    ImplicitFunctionData.toOpenPartialHomeomorph_apply,
    HasStrictFDerivAt.implicitFunctionDataOfComplemented]

def parametricLevelCoordinates
    (Phi : X × Y → Z) (p : X × Y)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hSurj : (fderiv ℝ Phi p).range = ⊤) :
    Y → Z × (fderiv ℝ Phi p).ker := fun y =>
  (Phi p, parameterKernelEquiv (fderiv ℝ Phi p) hdim hSurj y)

def parametricLevelChart
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hSurj : (fderiv ℝ Phi p).range = ⊤) :
    Y → X × Y := fun y =>
  (parametricImplicitChart Phi p hPhi hSurj).symm
    (parametricLevelCoordinates Phi p hdim hSurj y)

/--
@isnad1 id=eq.3h5v.s9.511d39d6de2a from=translated src=- shape=d6a7d0fd vocab=be3b2f91
-/
@[simp]
theorem parametricLevelChart_baseParameter
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hSurj : (fderiv ℝ Phi p).range = ⊤) :
    parametricLevelChart Phi p hPhi hdim hSurj 0 = p := by
  rw [parametricLevelChart, parametricLevelCoordinates]
  simp only [map_zero]
  rw [← parametricImplicitChart_base_image Phi p hPhi hSurj]
  exact (parametricImplicitChart Phi p hPhi hSurj).left_inv
    (parametricImplicitChart_base_mem_source Phi p hPhi hSurj)

/--
@isnad1 id=contdiff.3h6v.s12.8fcae2de17a5 from=translated src=- shape=79d4ad4f vocab=b2267904
-/
theorem contDiffAt_parametricImplicitChart
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hSurj : (fderiv ℝ Phi p).range = ⊤)
    (q : X × Y) (hPhiQ : ContDiffAt ℝ 1 Phi q) :
    ContDiffAt ℝ 1 (parametricImplicitChart Phi p hPhi hSurj) q := by
  change ContDiffAt ℝ 1 (parametricImplicitData Phi p hPhi hSurj).prodFun q
  unfold ImplicitFunctionData.prodFun
  dsimp [parametricImplicitData,
    HasStrictFDerivAt.implicitFunctionDataOfComplemented]
  fun_prop

def parametricImplicitRegularSource
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hSurj : (fderiv ℝ Phi p).range = ⊤) : Set (X × Y) :=
  (parametricImplicitChart Phi p hPhi hSurj).source ∩
    {q | ContDiffAt ℝ 1 Phi q ∧
      (fderiv ℝ (parametricImplicitChart Phi p hPhi hSurj) q).IsInvertible}

/--
@isnad1 id=contdiff.2h5v.s12.c84155bfd559 from=translated src=- shape=b1b449ef vocab=aff60e47
-/
theorem contDiff_parametricLevelCoordinates
    (Phi : X × Y → Z) (p : X × Y)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hSurj : (fderiv ℝ Phi p).range = ⊤) :
    ContDiff ℝ 1 (parametricLevelCoordinates Phi p hdim hSurj) := by
  unfold parametricLevelCoordinates
  fun_prop

/--
@isnad1 id=contdiff.6h6v.s14.dfcfc801b16b from=translated src=- shape=52c90af0 vocab=150d5c94
-/
theorem contDiffAt_parametricLevelChart_of_mem
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hSurj : (fderiv ℝ Phi p).range = ⊤)
    (y : Y)
    (htarget : parametricLevelCoordinates Phi p hdim hSurj y ∈
      (parametricImplicitChart Phi p hPhi hSurj).target)
    (hPhiPoint : ContDiffAt ℝ 1 Phi
      (parametricLevelChart Phi p hPhi hdim hSurj y))
    (hinv : (fderiv ℝ (parametricImplicitChart Phi p hPhi hSurj)
      (parametricLevelChart Phi p hPhi hdim hSurj y)).IsInvertible) :
    ContDiffAt ℝ 1 (parametricLevelChart Phi p hPhi hdim hSurj) y := by
  rcases hinv with ⟨A, hA⟩
  have heCD : ContDiffAt ℝ 1
      (parametricImplicitChart Phi p hPhi hSurj)
      (parametricLevelChart Phi p hPhi hdim hSurj y) :=
    contDiffAt_parametricImplicitChart Phi p hPhi hSurj _ hPhiPoint
  have hsymm : ContDiffAt ℝ 1
      (parametricImplicitChart Phi p hPhi hSurj).symm
      (parametricLevelCoordinates Phi p hdim hSurj y) := by
    apply (parametricImplicitChart Phi p hPhi hSurj).contDiffAt_symm
      htarget (f₀' := A)
    · simpa [parametricLevelChart, hA] using
        (heCD.differentiableAt one_ne_zero).hasFDerivAt
    · simpa [parametricLevelChart] using
        heCD
  exact hsymm.comp y
    (contDiff_parametricLevelCoordinates Phi p hdim hSurj).contDiffAt

/--
@isnad1 id=eq.7h6v.s14.d1a1d787b962 from=translated src=- shape=b7ebdda9 vocab=150d5c94
-/
theorem fderiv_parametricLevelChart_range_eq_ker
    (Phi : X × Y → Z) (p : X × Y)
    (hPhi : ContDiffAt ℝ 1 Phi p)
    (hdim : Module.finrank ℝ X = Module.finrank ℝ Z)
    (hSurj : (fderiv ℝ Phi p).range = ⊤)
    (y : Y)
    (htarget : parametricLevelCoordinates Phi p hdim hSurj y ∈
      (parametricImplicitChart Phi p hPhi hSurj).target)
    (hPhiPoint : ContDiffAt ℝ 1 Phi
      (parametricLevelChart Phi p hPhi hdim hSurj y))
    (hinv : (fderiv ℝ (parametricImplicitChart Phi p hPhi hSurj)
      (parametricLevelChart Phi p hPhi hdim hSurj y)).IsInvertible)
    (hPointSurj : (fderiv ℝ Phi
      (parametricLevelChart Phi p hPhi hdim hSurj y)).range = ⊤) :
    (fderiv ℝ (parametricLevelChart Phi p hPhi hdim hSurj) y).range =
      (fderiv ℝ Phi
        (parametricLevelChart Phi p hPhi hdim hSurj y)).ker := by
  let e := parametricImplicitChart Phi p hPhi hSurj
  let c := parametricLevelCoordinates Phi p hdim hSurj
  let gamma := parametricLevelChart Phi p hPhi hdim hSurj
  let q := parameterKernelEquiv (fderiv ℝ Phi p) hdim hSurj
  let A := fderiv ℝ e (gamma y)
  let d := fderiv ℝ gamma y
  let L := fderiv ℝ Phi (gamma y)
  have hgammaCD : ContDiffAt ℝ 1 gamma y := by
    exact contDiffAt_parametricLevelChart_of_mem
      Phi p hPhi hdim hSurj y htarget hPhiPoint hinv
  have hgamma : DifferentiableAt ℝ gamma y :=
    hgammaCD.differentiableAt one_ne_zero
  have heDiff : DifferentiableAt ℝ e (gamma y) :=
    (contDiffAt_parametricImplicitChart Phi p hPhi hSurj _ hPhiPoint).differentiableAt
      one_ne_zero
  have hcDeriv : HasFDerivAt c
      ((0 : Y →L[ℝ] Z).prod (q : Y →L[ℝ] (fderiv ℝ Phi p).ker)) y := by
    exact (hasFDerivAt_const (𝕜 := ℝ) (Phi p) y).prodMk q.hasFDerivAt
  have hevent : (fun t => e (gamma t)) =ᶠ[𝓝 y] c := by
    have hright := (e.eventually_right_inverse htarget)
    have hpre :=
      (contDiff_parametricLevelCoordinates Phi p hdim hSurj).continuous.continuousAt
        hright
    filter_upwards [hpre] with t ht
    exact ht
  have hcompDeriv : HasFDerivAt (fun t => e (gamma t)) (A.comp d) y := by
    exact heDiff.hasFDerivAt.comp y hgamma.hasFDerivAt
  have hcomp : A.comp d =
      (0 : Y →L[ℝ] Z).prod (q : Y →L[ℝ] (fderiv ℝ Phi p).ker) := by
    exact (hcompDeriv.congr_of_eventuallyEq hevent.symm).unique hcDeriv
  have hfirstFun : (fun w => (e w).1) = Phi := by
    funext w
    exact parametricImplicitChart_fst Phi p w hPhi hSurj
  have hfirstDeriv :
      fderiv ℝ (fun w => (e w).1) (gamma y) = L := by
    exact congrArg (fun f : (X × Y) → Z => fderiv ℝ f (gamma y)) hfirstFun
  have hfst : (ContinuousLinearMap.fst ℝ Z (fderiv ℝ Phi p).ker).comp A = L := by
    exact (fderiv.fst heDiff).symm.trans hfirstDeriv
  exact range_eq_ker_of_chart_derivative L A d q hdim hPointSurj hfst hcomp

end AbelFormalization
