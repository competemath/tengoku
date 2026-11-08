module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.Rigidity.Classify.Discriminant
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.Rigidity.Classify.DualLatticeFinite
public import Tengoku.Seed.Algebra.Module.ZLattice.Covolume
public import Tengoku.Seed.Data.Matrix.Mul
public import Tengoku.Seed.LinearAlgebra.Basis.Basic
public import Tengoku.Seed.LinearAlgebra.Matrix.BilinearForm
public import Tengoku.Seed.LinearAlgebra.Span.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dual covolume and discriminant size

This file collects standard covolume identities for `ℤ`-lattices in a real inner product space.
In particular, for an integral lattice (`L ≤ L*`) the discriminant group `L*/L` has cardinality
`(covolume L)^2`.

The main computations are reduced to a coordinate space `ι → ℝ` via `ZLattice.covolume_comap`.
There we use the dot-product bilinear form and a determinant computation with a basis and its
bilinear dual basis.

## Main statements
* `relIndex_eq_card_discriminantGroup`
* `card_discriminantGroup_eq_covolume_sq`
-/

namespace SpherePacking.Dim24.Uniqueness.RigidityClassify

noncomputable section

open scoped RealInnerProductSpace BigOperators
open MeasureTheory Matrix Module

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

section Pi

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "E" => (ι → ℝ)

noncomputable def dotBilin : LinearMap.BilinForm ℝ E :=
  Matrix.toBilin' (1 : Matrix ι ι ℝ)

@[simp] lemma dotBilin_apply (x y : E) : dotBilin (ι := ι) x y = dotProduct x y := by
  simp [dotBilin, Matrix.toBilin'_apply']

lemma dotBilin_nondegenerate :
    (dotBilin (ι := ι) : LinearMap.BilinForm ℝ E).Nondegenerate := by
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft
    (B := (dotBilin (ι := ι) : LinearMap.BilinForm ℝ E)) ?_
  intro x hx
  ext i
  have h0 : dotProduct x (Pi.single i (1 : ℝ)) = 0 := by
    simpa [dotBilin_apply] using hx (Pi.single i (1 : ℝ))
  simpa [dotProduct_single] using h0

lemma covolume_dualSubmodule_eq_inv (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume
        ((dotBilin (ι := ι) : LinearMap.BilinForm ℝ E).dualSubmodule L)
        volume
      =
      (ZLattice.covolume L volume)⁻¹ := by
  let B : LinearMap.BilinForm ℝ E := dotBilin (ι := ι)
  let b : Basis ι ℤ L := IsZLattice.basis (L := L)
  let bR : Basis ι ℝ E := b.ofZLatticeBasis ℝ L
  have hB : B.Nondegenerate := dotBilin_nondegenerate (ι := ι)
  let wR : Basis ι ℝ E := B.dualBasis hB bR
  have hLspan : Submodule.span ℤ (Set.range bR) = L := by
    simpa using (b.ofZLatticeBasis_span (K := ℝ) (L := L))
  have hLstar :
      B.dualSubmodule L = Submodule.span ℤ (Set.range wR) := by
    simpa [hLspan] using
      (LinearMap.BilinForm.dualSubmodule_span_of_basis (R := ℤ) (B := B) hB bR)
  -- Work with the `ℤ`-span description of the dual submodule.
  let LstarSpan : Submodule ℤ E := Submodule.span ℤ (Set.range wR)
  have hLstar' : B.dualSubmodule L = LstarSpan := hLstar
  haveI : DiscreteTopology LstarSpan := inferInstance
  haveI : IsZLattice ℝ LstarSpan := inferInstance
  have hw_lin : LinearIndependent ℤ (fun i : ι => (wR i : E)) := by
    -- restrict scalars along `ℤ → ℝ`
    simpa using
      (LinearIndependent.restrict_scalars' (R := ℤ) (K := ℝ) (M := E)
        (v := fun i : ι => (wR i : E)) wR.linearIndependent)
  let wZ : ι → LstarSpan := fun i =>
    ⟨(wR i : E), Submodule.subset_span (Set.mem_range_self i)⟩
  have hwZ_lin : LinearIndependent ℤ wZ := by
    simpa [LstarSpan, wZ] using (linearIndependent_span (R := ℤ) hw_lin)
  have hwZ_span : Submodule.span ℤ (Set.range wZ) = ⊤ := by
    have hw_mem : ∀ i : ι, (wR i : E) ∈ LstarSpan := fun i =>
      Submodule.subset_span (Set.mem_range_self i)
    have hiff :=
      (Submodule.span_range_subtype_eq_top_iff (p := LstarSpan)
        (s := fun i : ι => (wR i : E)) hw_mem)
    simpa [LstarSpan, wZ] using (hiff.2 rfl)
  have hwZ_span' : (⊤ : Submodule ℤ LstarSpan) ≤ Submodule.span ℤ (Set.range wZ) := by
    simp [hwZ_span]
  let bStarSpan : Basis ι ℤ LstarSpan := Basis.mk hwZ_lin hwZ_span'
  -- Covolume formulas as determinants.
  have hcovL : ZLattice.covolume L volume = |(Matrix.of ((↑) ∘ b)).det| := by
    simpa using (ZLattice.covolume_eq_det (L := L) (b := b))
  have hcovLstar :
      ZLattice.covolume LstarSpan volume = |(Matrix.of ((↑) ∘ bStarSpan)).det| := by
    simpa using (ZLattice.covolume_eq_det (L := LstarSpan) (b := bStarSpan))
  -- Matrices of the real bases.
  let W : Matrix ι ι ℝ := Matrix.of fun i => (bR i : E)
  let Wstar : Matrix ι ι ℝ := Matrix.of fun i => (wR i : E)
  have hmul : Wstar * W.transpose = (1 : Matrix ι ι ℝ) := by
    ext i j
    have hij : B (wR i) (bR j) = (if j = i then (1 : ℝ) else 0) := by
      simpa using (LinearMap.BilinForm.apply_dualBasis_left (B := B) hB bR i j)
    have hij' : dotProduct (wR i : E) (bR j : E) = (if i = j then (1 : ℝ) else 0) := by
      simpa [B, dotBilin_apply, eq_comm] using hij
    have hentry : (Wstar * W.transpose) i j = dotProduct (wR i : E) (bR j : E) := by
      simp [W, Wstar, Matrix.mul_apply, Matrix.of_apply, dotProduct]
    -- finish with `hij'`
    simpa [hentry, Matrix.one_apply] using hij'
  have hdet_mul : Wstar.det * W.det = (1 : ℝ) := by
    have : (Wstar * W.transpose).det = (1 : Matrix ι ι ℝ).det := congrArg Matrix.det hmul
    simpa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, mul_assoc] using this
  have hWdet : W.det ≠ (0 : ℝ) := by
    exact right_ne_zero_of_mul_eq_one hdet_mul
  have hdet : Wstar.det = (W.det)⁻¹ := by
    have := congrArg (fun t => t * (W.det)⁻¹) hdet_mul
    simpa [mul_assoc, hWdet] using this
  have hW : (Matrix.of ((↑) ∘ b) : Matrix ι ι ℝ) = W := by
    ext i j
    simp [W, bR, Basis.ofZLatticeBasis_apply]
  have hWstar : (Matrix.of ((↑) ∘ bStarSpan) : Matrix ι ι ℝ) = Wstar := by
    ext i j
    simp [Wstar, bStarSpan, wZ]
  calc
    ZLattice.covolume (B.dualSubmodule L) volume
        = ZLattice.covolume LstarSpan volume := by simp [hLstar']
    _ = |(Matrix.of ((↑) ∘ bStarSpan) : Matrix ι ι ℝ).det| := hcovLstar
    _ = |Wstar.det| := by simp [hWstar]
    _ = |(W.det)⁻¹| := by simp [hdet]
    _ = |W.det|⁻¹ := by simp [abs_inv]
    _ = (ZLattice.covolume L volume)⁻¹ := by simp [hcovL, hW]

end Pi

/-! ### Discriminant group size -/

end

end SpherePacking.Dim24.Uniqueness.RigidityClassify
