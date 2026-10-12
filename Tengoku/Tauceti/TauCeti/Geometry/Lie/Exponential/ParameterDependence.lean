/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Geometry.Lie.Exponential.Basic

/-!
# Parameter dependence of invariant integral curves

This file begins the analytic parameter-dependence theory for the invariant integral curves that
define the Lie-group exponential. In the identity chart, the tangent vector and group coordinate
form an autonomous ODE on the product model space. Picard--Lindelöf then supplies a single local
solution family, continuous jointly in its initial condition and time, for all sufficiently small
tangent vectors.

## Main results

* `mulInvariantCoordinateVectorField`: the invariant vector field in the identity chart, with its
  generating tangent vector included as a parameter.
* `contDiffAt_mulInvariantCoordinateVectorField`: this coordinate vector field is `C^n` at every
  generating vector over the identity coordinate when multiplication is `C^(n + 1)`.
* `mulInvariantCoordinateLinearMap`: the coordinate field as an operator on its generating vector.
* `contDiffAt_mulInvariantCoordinateLinearMap_one`: this operator is `C^n` at the identity
  coordinate.
* `hasStrictFDerivAt_mulInvariantCoordinateVectorField_zero_one`: the linearization of the
  parameterized coordinate field at zero and the identity is projection onto the parameter.
* `exists_lipschitzOn_local_mulInvariantCoordinateFlow`: a local solution family on a uniform
  closed neighborhood of the zero vector and the identity coordinate, jointly continuous and
  uniformly Lipschitz in its initial state.
* `exists_eventually_hasDerivAt_mulInvariantCoordinateFlow`: a neighborhood form of the local
  solution family whose values remain inside the identity chart.
* `exists_local_coordinate_representation_mulInvariantIntegralCurve`: the local solution family
  solves the coordinate ODE and represents the canonical integral curves uniformly for all small
  generators.
* `continuousAt_mulInvariantExp_modelSpace_zero`: the tangent-space exponential is continuous at
  zero in model-space coordinates.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
* Winston Yin's Mathlib proof of `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`, whose
  chart calculation is exposed by `IsMIntegralCurveAt.of_extChartAt_symm` and invoked below.
-/

public section

open Bundle Function Manifold VectorField
open scoped ContDiff Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- A tangent vector is represented by the model vector type `E`. This private helper isolates the
definitional identification used when a tangent-bundle value enters coordinate calculus. -/
private abbrev tangentVectorModelSpace {g : G} (v : TangentSpace I g) : E := v

/-- The left-invariant vector field, expressed in the identity chart and parameterized by its
generating tangent vector in the model space. -/
noncomputable def mulInvariantCoordinateVectorField [IsManifold I 1 G] (p : E × E) : E :=
  let g := (extChartAt I (1 : G)).symm p.2
  tangentCoordChange I g (1 : G) g
    (mulInvariantVectorField (I := I) (G := G) p.1 g)

/-- The parameterized coordinate field is the invariant vector field transported through the
identity chart. -/
theorem mulInvariantCoordinateVectorField_apply [IsManifold I 1 G] (v y : E) :
    mulInvariantCoordinateVectorField (I := I) (G := G) (v, y) =
      tangentCoordChange I ((extChartAt I (1 : G)).symm y) (1 : G)
        ((extChartAt I (1 : G)).symm y)
        (mulInvariantVectorField (I := I) (G := G)
          (v : GroupLieAlgebra I G) ((extChartAt I (1 : G)).symm y)) := by
  rfl

/-- The invariant coordinate field is additive in its generating vector. -/
@[simp]
theorem mulInvariantCoordinateVectorField_add [IsManifold I 1 G] (v w y : E) :
    mulInvariantCoordinateVectorField (I := I) (G := G) (v + w, y) =
      mulInvariantCoordinateVectorField (I := I) (G := G) (v, y) +
        mulInvariantCoordinateVectorField (I := I) (G := G) (w, y) := by
  let g := (extChartAt I (1 : G)).symm y
  let A := tangentCoordChange I g (1 : G) g
  calc
    A (tangentVectorModelSpace (I := I) <|
        mulInvariantVectorField (I := I) (G := G)
          ((v + w : E) : GroupLieAlgebra I G) g) =
        A (tangentVectorModelSpace (I := I) <|
            mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G) g) +
          A (tangentVectorModelSpace (I := I) <|
            mulInvariantVectorField (I := I) (G := G) (w : GroupLieAlgebra I G) g) := by
      rw [← map_add]
      apply congrArg A
      -- Compare the underlying tangent vectors before their definitional model-space conversion.
      change mulInvariantVectorField (I := I) (G := G)
          ((v + w : E) : GroupLieAlgebra I G) g =
        mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G) g +
          mulInvariantVectorField (I := I) (G := G) (w : GroupLieAlgebra I G) g
      have hparameter : ((v + w : E) : GroupLieAlgebra I G) =
          (v : GroupLieAlgebra I G) + (w : GroupLieAlgebra I G) := rfl
      rw [hparameter]
      exact congrFun (mulInvariantVectorField_add (I := I) (G := G)
        (v : GroupLieAlgebra I G) (w : GroupLieAlgebra I G)) g

/-- The invariant coordinate field respects scalar multiplication in its generating vector. -/
@[simp]
theorem mulInvariantCoordinateVectorField_smul [IsManifold I 1 G] (c : ℝ) (v y : E) :
    mulInvariantCoordinateVectorField (I := I) (G := G) (c • v, y) =
      c • mulInvariantCoordinateVectorField (I := I) (G := G) (v, y) := by
  let g := (extChartAt I (1 : G)).symm y
  let A := tangentCoordChange I g (1 : G) g
  calc
    A (tangentVectorModelSpace (I := I) <|
        mulInvariantVectorField (I := I) (G := G)
          ((c • v : E) : GroupLieAlgebra I G) g) =
        c • A (tangentVectorModelSpace (I := I) <|
          mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G) g) := by
      rw [← map_smul]
      apply congrArg A
      -- Compare the underlying tangent vectors before their definitional model-space conversion.
      change mulInvariantVectorField (I := I) (G := G)
          ((c • v : E) : GroupLieAlgebra I G) g =
        c • mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G) g
      have hparameter : ((c • v : E) : GroupLieAlgebra I G) =
          c • (v : GroupLieAlgebra I G) := rfl
      rw [hparameter]
      exact congrFun (mulInvariantVectorField_smul (I := I) (G := G)
        c (v : GroupLieAlgebra I G)) g

/-- At the identity coordinate, the parameterized invariant field equals its generator. -/
@[simp]
theorem mulInvariantCoordinateVectorField_one [IsManifold I 1 G] (v : E) :
    mulInvariantCoordinateVectorField (I := I) (G := G)
      (v, I (chartAt H (1 : G) (1 : G))) = v := by
  have hidentityCoordinate : I (chartAt H (1 : G) (1 : G)) =
      extChartAt I (1 : G) (1 : G) := by
    rfl
  rw [hidentityCoordinate]
  rw [mulInvariantCoordinateVectorField_apply]
  have hsymm : (extChartAt I (1 : G)).symm (extChartAt I (1 : G) (1 : G)) = 1 :=
    (extChartAt I (1 : G)).left_inv (mem_extChartAt_source (I := I) (1 : G))
  rw [hsymm]
  have hfieldOne : tangentVectorModelSpace (I := I)
      (mulInvariantVectorField (I := I) (G := G)
        (v : GroupLieAlgebra I G) 1) = v := by
    exact mulInvariantVectorField_one (I := I) (G := G) (v : GroupLieAlgebra I G)
  change tangentCoordChange I 1 1 1
      (tangentVectorModelSpace (I := I) <|
        mulInvariantVectorField (I := I) (G := G) (v : GroupLieAlgebra I G) 1) = v
  rw [hfieldOne]
  exact tangentCoordChange_self (mem_extChartAt_source (I := I) (1 : G))

/-- The invariant coordinate field vanishes when its generating vector vanishes. -/
@[simp]
theorem mulInvariantCoordinateVectorField_zero [IsManifold I 1 G] (y : E) :
    mulInvariantCoordinateVectorField (I := I) (G := G) (0, y) = 0 := by
  simpa using mulInvariantCoordinateVectorField_smul
    (I := I) (G := G) (0 : ℝ) (0 : E) y

/-- The coordinate expression of the parameterized left-invariant vector field is `C^n` at every
generating vector over the identity coordinate when multiplication is `C^(n + 1)`. -/
theorem contDiffAt_mulInvariantCoordinateVectorField (v : E) {n : ℕ∞ω}
    [ContMDiffMul I (n + 1) G] (h1 : I.IsInteriorPoint (1 : G)) :
    let _ : IsManifold I 1 G := IsManifold.of_le (n := n + 1) le_add_self
    ContDiffAt ℝ n (mulInvariantCoordinateVectorField (I := I) (G := G))
      (v, extChartAt I (1 : G) (1 : G)) := by
  let _ : IsManifold I 1 G := IsManifold.of_le (n := n + 1) le_add_self
  dsimp only
  let V : E × G → TangentBundle I G := fun p =>
    ⟨p.2, mulInvariantVectorField (I := I) (G := G) p.1 p.2⟩
  have hV : ContMDiff (𝓘(ℝ, E).prod I) I.tangent n V :=
    contMDiff_mulInvariantVectorField_modelSpace (m := n) (n := n + 1) le_rfl
  have hV₀ := hV.contMDiffAt (x := (v, (1 : G)))
  rw [contMDiffAt_iff] at hV₀
  have hv1 : (𝓘(ℝ, E).prod I).IsInteriorPoint (v, (1 : G)) := by
    -- `ModelWithCorners.interior_prod` is stated for membership in `interior`; unfold
    -- `IsInteriorPoint` to expose precisely that representation.
    change (v, (1 : G)) ∈ (𝓘(ℝ, E).prod I).interior (E × G)
    rw [ModelWithCorners.interior_prod]
    exact ⟨BoundarylessManifold.isInteriorPoint, h1⟩
  have h := hV₀.2.contDiffAt
    (range_mem_nhds_isInteriorPoint hv1)
  let w : E × E → E := fun x =>
    ((extChartAt I.tangent (V (v, 1)) ∘ V ∘
      (extChartAt (𝓘(ℝ, E).prod I) (v, 1)).symm) x).2
  have hw_apply (p : E × E) :
      w p = tangentCoordChange I ((extChartAt I (1 : G)).symm p.2) (1 : G)
        ((extChartAt I (1 : G)).symm p.2)
        (tangentVectorModelSpace (I := I) <|
          mulInvariantVectorField (I := I) (G := G)
            (p.1 : GroupLieAlgebra I G) ((extChartAt I (1 : G)).symm p.2)) := by
    -- This is the defining second coordinate of the tangent-bundle extended chart. Keeping the
    -- implementation-level conversion here prevents its definitional equality from leaking into
    -- the regularity argument below.
    change tangentCoordChange I ((extChartAt I (1 : G)).symm p.2) (1 : G)
      ((extChartAt I (1 : G)).symm p.2)
        (tangentVectorModelSpace (I := I) <|
          mulInvariantVectorField (I := I) (G := G)
            (p.1 : GroupLieAlgebra I G) ((extChartAt I (1 : G)).symm p.2)) = _
    rfl
  have hw : w = mulInvariantCoordinateVectorField (I := I) (G := G) := by
    funext p
    rw [mulInvariantCoordinateVectorField_apply]
    exact hw_apply p
  rw [← hw]
  simpa only [w, extChartAt_prod, extChartAt_self_apply, modelWithCornersSelf_coe,
    PartialEquiv.prod_coe, PartialEquiv.refl_coe, id_eq] using h.snd

/-- At a fixed identity-chart coordinate, the invariant coordinate field as a continuous linear
map of its generating model vector. -/
noncomputable def mulInvariantCoordinateLinearMap [IsManifold I 1 G] (y : E) : E →L[ℝ] E :=
  let g := (extChartAt I (1 : G)).symm y
  (tangentCoordChange I g (1 : G) g).comp
    (mfderiv I I (fun x : G => g * x) (1 : G))

/-- Applying the coordinate-field linear map recovers the parameterized coordinate vector field. -/
@[simp]
theorem mulInvariantCoordinateLinearMap_apply [IsManifold I 1 G] (y v : E) :
    mulInvariantCoordinateLinearMap (I := I) (G := G) y v =
      mulInvariantCoordinateVectorField (I := I) (G := G) (v, y) := by
  rfl

/-- At the identity coordinate, the coordinate-field linear map is the identity operator. -/
@[simp]
theorem mulInvariantCoordinateLinearMap_one [IsManifold I 1 G] :
    mulInvariantCoordinateLinearMap (I := I) (G := G)
      (I (chartAt H (1 : G) (1 : G))) = ContinuousLinearMap.id ℝ E := by
  apply ContinuousLinearMap.ext
  intro v
  rw [mulInvariantCoordinateLinearMap_apply, ContinuousLinearMap.id_apply]
  exact mulInvariantCoordinateVectorField_one (I := I) (G := G) v

/-- In finite dimensions, the coordinate-field linear map is `C^n` at the identity coordinate. -/
theorem contDiffAt_mulInvariantCoordinateLinearMap_one {n : ℕ∞ω}
    [FiniteDimensional ℝ E] [ContMDiffMul I (n + 1) G] (h1 : I.IsInteriorPoint (1 : G)) :
    let _ : IsManifold I 1 G := IsManifold.of_le (n := n + 1) le_add_self
    ContDiffAt ℝ n (mulInvariantCoordinateLinearMap (I := I) (G := G))
      (extChartAt I (1 : G) (1 : G)) := by
  let _ : IsManifold I 1 G := IsManifold.of_le (n := n + 1) le_add_self
  dsimp only
  let d := Module.finrank ℝ E
  let e₁ : E ≃L[ℝ] Fin d → ℝ :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
  let e₂ : (E →L[ℝ] E) ≃L[ℝ] Fin d → E :=
    (e₁.arrowCongr (ContinuousLinearEquiv.refl ℝ E)).trans
      (ContinuousLinearEquiv.piRing (Fin d))
  rw [← e₂.comp_contDiffAt_iff]
  apply contDiffAt_pi'
  intro i
  let b : E := e₁.symm (Pi.single i 1)
  have h := (contDiffAt_mulInvariantCoordinateVectorField (I := I) (G := G) (v := b)
    (n := n) h1).comp
    (extChartAt I (1 : G) (1 : G)) (contDiffAt_const.prodMk contDiffAt_id)
  convert h using 1
  funext y
  simp [e₂, b, ContinuousLinearEquiv.piRing, mulInvariantCoordinateLinearMap_apply,
    ContinuousLinearEquiv.refl_apply]

/-- At the zero generating vector over the identity coordinate, the parameterized coordinate
vector field has strict derivative equal to projection onto the generating-vector coordinate. -/
theorem hasStrictFDerivAt_mulInvariantCoordinateVectorField_zero_one
    [FiniteDimensional ℝ E] [ContMDiffMul I (1 + 1) G]
    (h1 : I.IsInteriorPoint (1 : G)) :
    let _ : IsManifold I 1 G := IsManifold.of_le (n := 1 + 1) (by norm_num)
    HasStrictFDerivAt (mulInvariantCoordinateVectorField (I := I) (G := G))
      (ContinuousLinearMap.fst ℝ E E)
      ((0 : E), extChartAt I (1 : G) (1 : G)) := by
  let _ : IsManifold I 1 G := IsManifold.of_le (n := 1 + 1) (by norm_num)
  dsimp only
  let A : E → E →L[ℝ] E := mulInvariantCoordinateLinearMap (I := I) (G := G)
  let p : E × E := ((0 : E), extChartAt I (1 : G) (1 : G))
  have hAcd : ContDiffAt ℝ 1 (fun q : E × E => A q.2) p :=
    ContDiffAt.fun_comp p
      (contDiffAt_mulInvariantCoordinateLinearMap_one (I := I) (G := G) (n := 1)
        h1) contDiffAt_snd
  have hA : DifferentiableAt ℝ (fun q : E × E => A q.2) p :=
    hAcd.differentiableAt one_ne_zero
  have h := hA.hasFDerivAt.clm_apply (hasFDerivAt_fst (p := p))
  have hfield : mulInvariantCoordinateVectorField (I := I) (G := G) =
      fun q : E × E => (A q.2) q.1 := by
    funext q
    exact (mulInvariantCoordinateLinearMap_apply (I := I) (G := G) q.2 q.1).symm
  have hderiv : HasFDerivAt (mulInvariantCoordinateVectorField (I := I) (G := G))
      (ContinuousLinearMap.fst ℝ E E) p := by
    rw [hfield]
    apply h.congr_fderiv
    apply ContinuousLinearMap.ext
    rintro ⟨q₁, q₂⟩
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
      p, map_zero, A, add_zero]
    have hidentityCoordinate : extChartAt I (1 : G) (1 : G) =
        I (chartAt H (1 : G) (1 : G)) := by
      rw [extChartAt_coe]
      rfl
    rw [hidentityCoordinate]
    rw [mulInvariantCoordinateLinearMap_one]
    rfl
  exact (contDiffAt_mulInvariantCoordinateVectorField (I := I) (G := G) (v := 0) (n := 1)
    h1).hasStrictFDerivAt' hderiv one_ne_zero
