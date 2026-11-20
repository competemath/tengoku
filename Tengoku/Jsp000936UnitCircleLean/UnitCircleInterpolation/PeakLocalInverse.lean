/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.PeakHeightDerivative
import Tengoku.Seed.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Tengoku.Seed.LinearAlgebra.Matrix.Nondegenerate
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin
import Tengoku.Seed.Topology.IsLocalHomeomorph
import Tengoku.Seed.Topology.OpenPartialHomeomorph.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local inverses of the actual height-difference map

The already proved actual Jacobian determinant gives a continuous linear
equivalence. The smooth inverse function theorem then supplies a local inverse
whose source lies in the admissible angular domain. Global injectivity and
properness are separate results.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ContDiff

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

/--
@isnad1 id=contdiff.2h2v.s7.d816323ef707 from=translated src=- shape=adde1c77 vocab=64bad1b5
-/
theorem contDiffAt_parameterAdjacentHeightDifferences_of_mem_domain (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    ContDiffAt ℝ ∞ (parameterAdjacentHeightDifferences hsize) u := by
  exact contDiffAt_pi.mpr (fun i =>
    (contDiffAt_parameterOrderedHeight_of_mem_domain u hu hsize i.succ).sub
      (contDiffAt_parameterOrderedHeight_of_mem_domain u hu hsize i.castSucc))

/--
@isnad1 id=eq.1h3v.s9.63871b8335c6 from=translated src=- shape=1cbbdf69 vocab=5b8bbf90
-/
lemma parameterAdjacentHeightJacobian_mulVec (hsize : 2 ≤ d + 1)
    (u v : Fin d → ℝ) :
    (parameterAdjacentHeightJacobian hsize u).mulVec v =
      fderiv ℝ (parameterAdjacentHeightDifferences hsize) u v := by
  have hm : LinearMap.toMatrix'
      (fderiv ℝ (parameterAdjacentHeightDifferences hsize) u).toLinearMap =
        parameterAdjacentHeightJacobian hsize u := by
    ext i j
    rfl
  rw [← hm]
  exact LinearMap.toMatrix'_mulVec
    (fderiv ℝ (parameterAdjacentHeightDifferences hsize) u).toLinearMap v

/--
@isnad1 id=bijectiv.2h2v.s9.6eecd9d53f87 from=translated src=- shape=240d2248 vocab=1080a8ea
-/
theorem fderiv_parameterAdjacentHeightDifferences_bijective (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    Function.Bijective (fderiv ℝ (parameterAdjacentHeightDifferences hsize) u) := by
  have hinj : Function.Injective
      (fderiv ℝ (parameterAdjacentHeightDifferences hsize) u) := by
    intro v w hvw
    apply Matrix.mulVec_injective_of_det_ne_zero
      (parameterAdjacentHeightJacobian_det_ne_zero u hu hsize)
    simpa only [parameterAdjacentHeightJacobian_mulVec] using hvw
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The literal actual differential, packaged as a continuous linear equivalence.-/
def heightDifferenceDerivativeEquiv (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearEquiv.ofBijective
    (fderiv ℝ (parameterAdjacentHeightDifferences hsize) u)
    (LinearMap.ker_eq_bot.mpr
      (fderiv_parameterAdjacentHeightDifferences_bijective u hu hsize).1)
    (LinearMap.range_eq_top.mpr
      (fderiv_parameterAdjacentHeightDifferences_bijective u hu hsize).2)

/--
@isnad1 id=eq.2h2v.s8.d0c3dd6ef9f1 from=translated src=- shape=d78827ba vocab=a9cae282
-/
lemma heightDifferenceDerivativeEquiv_coe (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    (heightDifferenceDerivativeEquiv u hu hsize :
      (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) =
      fderiv ℝ (parameterAdjacentHeightDifferences hsize) u :=
  ContinuousLinearEquiv.coe_ofBijective _ _ _

/--
@isnad1 id=hasfderi.2h2v.s7.2cfab8216d9d from=translated src=- shape=bd771020 vocab=91bd71ad
-/
lemma hasFDerivAt_heightDifferenceDerivativeEquiv (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    HasFDerivAt (parameterAdjacentHeightDifferences hsize)
      (heightDifferenceDerivativeEquiv u hu hsize :
        (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) u := by
  rw [heightDifferenceDerivativeEquiv_coe,
    fderiv_parameterAdjacentHeightDifferences_of_mem_domain u hu]
  exact hasFDerivAt_parameterAdjacentHeightDifferences_of_mem_domain u hu hsize

/-- An actual local inverse chart restricted to the admissible angular domain.-/
def heightDifferenceLocalChart (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ) :=
  ((contDiffAt_parameterAdjacentHeightDifferences_of_mem_domain u hu hsize).toOpenPartialHomeomorph
    (parameterAdjacentHeightDifferences hsize)
    (hasFDerivAt_heightDifferenceDerivativeEquiv u hu hsize) (by norm_num)).restrOpen
      (angularParameterDomain d) (isOpen_angularParameterDomain d)

/--
@isnad1 id=eq.2h2v.s6.7c851f8786ca from=translated src=- shape=9d72d3f8 vocab=bf7b2f2d
-/
@[simp] lemma heightDifferenceLocalChart_coe (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    (heightDifferenceLocalChart u hu hsize : (Fin d → ℝ) → (Fin d → ℝ)) =
      parameterAdjacentHeightDifferences hsize := rfl

/--
@isnad1 id=mem.2h2v.s7.55469e5040b9 from=translated src=- shape=d4c33be1 vocab=666ec189
-/
lemma mem_heightDifferenceLocalChart_source (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    u ∈ (heightDifferenceLocalChart u hu hsize).source := by
  exact ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, hu⟩

/--
@isnad1 id=le.2h2v.s7.84afa4e6ce4f from=translated src=- shape=b5d39a8e vocab=666ec189
-/
lemma heightDifferenceLocalChart_source_subset (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1) :
    (heightDifferenceLocalChart u hu hsize).source ⊆ angularParameterDomain d :=
  fun _ hx => hx.2

/--
@isnad1 id=eq.3h3v.s7.9331e280dd1f from=translated src=- shape=1182835f vocab=e8437902
-/
lemma heightDifferenceLocalChart_left_inv (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1)
    (v : Fin d → ℝ) (hv : v ∈ (heightDifferenceLocalChart u hu hsize).source) :
    (heightDifferenceLocalChart u hu hsize).symm
      (parameterAdjacentHeightDifferences hsize v) = v :=
  (heightDifferenceLocalChart u hu hsize).left_inv hv

/--
@isnad1 id=eq.3h3v.s7.80e7023f8586 from=translated src=- shape=dc08978a vocab=9a1888ab
-/
lemma heightDifferenceLocalChart_right_inv (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (hsize : 2 ≤ d + 1)
    (y : Fin d → ℝ) (hy : y ∈ (heightDifferenceLocalChart u hu hsize).target) :
    parameterAdjacentHeightDifferences hsize
      ((heightDifferenceLocalChart u hu hsize).symm y) = y :=
  (heightDifferenceLocalChart u hu hsize).right_inv hy

/-- The actual adjacent-height difference map on its admissible domain.-/
def heightDifferenceMap (hsize : 2 ≤ d + 1) (u : angularParameterDomain d) : Fin d → ℝ :=
  parameterAdjacentHeightDifferences hsize u.val

/--
@isnad1 id=islocalh.1h1v.s6.d1c33f61bdf7 from=translated src=- shape=2176ad16 vocab=f9080776
-/
theorem isLocalHomeomorph_heightDifferenceMap (hsize : 2 ≤ d + 1) :
    IsLocalHomeomorph (heightDifferenceMap hsize) := by
  intro u
  let S : TopologicalSpace.Opens (Fin d → ℝ) :=
    ⟨angularParameterDomain d, isOpen_angularParameterDomain d⟩
  have hS : Nonempty S := ⟨u⟩
  let e := heightDifferenceLocalChart u.val u.property hsize
  refine ⟨e.subtypeRestr hS, ?_, ?_⟩
  · simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using
      mem_heightDifferenceLocalChart_source u.val u.property hsize
  · rfl

/--
@isnad1 id=continuo.1h1v.s6.044b41ed7480 from=translated src=- shape=2176ad16 vocab=137a08c3
-/
theorem continuous_heightDifferenceMap (hsize : 2 ≤ d + 1) :
    Continuous (heightDifferenceMap hsize) :=
  (isLocalHomeomorph_heightDifferenceMap hsize).continuous

end

end UnitCircleInterpolation
