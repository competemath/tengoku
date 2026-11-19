import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.HilbertSchmidtBound
import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.BoundedKernelL2
import Tengoku.OddcyclegoodmanLean.OddCycleBound.Spectral.EigenBasis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.Spectral
open OddCycleBound.Spectral.CompactSpectral
open OddCycleBound.Spectral.InfiniteSpectral
open OddCycleBound.Spectral.L2Kernel

universe u

section AbstractSpectrum

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [CompleteSpace E]

abbrev zeroEigenOrthogonal (T : E →L[Real] E) : Submodule Real E :=
  (Module.End.eigenspace (T : Module.End Real E) 0)ᗮ

abbrev NonzeroEigenIndex (T : E →L[Real] E) : Type :=
  Sigma fun lambda : {lambda : Real // lambda ≠ 0} =>
    Fin (Module.finrank Real
      (Module.End.eigenspace (T : Module.End Real E) lambda.1))

/--
@isnad1 id=finitedi.1h3v.s9.fbfa1fb1b1d4 from=translated src=- shape=c3bda919 vocab=03b1c6e9
-/
theorem nonzeroEigenspace_finiteDimensional
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (lambda : {lambda : Real // lambda ≠ 0}) :
    FiniteDimensional Real
      (Module.End.eigenspace (T : Module.End Real E) lambda.1) :=
  ContinuousLinearMap.finite_dimensional_eigenspace
    (T := T) hcompact lambda.1 lambda.2

noncomputable def nonzeroEigenspaceBasis
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (lambda : {lambda : Real // lambda ≠ 0}) :
    HilbertBasis
      (Fin (Module.finrank Real
        (Module.End.eigenspace (T : Module.End Real E) lambda.1)))
      Real (Module.End.eigenspace (T : Module.End Real E) lambda.1) := by
  letI := nonzeroEigenspace_finiteDimensional T hcompact lambda
  exact (stdOrthonormalBasis Real
    (Module.End.eigenspace (T : Module.End Real E) lambda.1)).toHilbertBasis

def nonzeroEigenvalue (T : E →L[Real] E)
    (i : NonzeroEigenIndex T) : Real := i.1.1

noncomputable def nonzeroEigenmode
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (i : NonzeroEigenIndex T) : E :=
  ((nonzeroEigenspaceBasis T hcompact i.1 i.2 :
      Module.End.eigenspace (T : Module.End Real E) i.1.1) : E)

omit [CompleteSpace E] in
/--
@isnad1 id=ne.0h3v.s6.6be9d37d7e48 from=translated src=- shape=81a0eab8 vocab=c292b6f9
-/
theorem nonzeroEigenvalue_ne
    (T : E →L[Real] E) (i : NonzeroEigenIndex T) :
    nonzeroEigenvalue T i ≠ 0 :=
  i.1.2

/--
@isnad1 id=countabl.2h2v.s8.4f911f7551b1 from=translated src=- shape=59420652 vocab=1be86c42
-/
theorem nonzeroEigenIndex_countable
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    Countable (NonzeroEigenIndex T) := by
  exact compactSelfAdjoint_countable_nonzero_eigenspace_finIndex
    T hcompact hsymm

/--
@isnad1 id=orthonor.2h2v.s8.f8b113635ac0 from=translated src=- shape=97f268ed vocab=397085f6
-/
theorem nonzeroEigenmode_orthonormal
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    Orthonormal Real (nonzeroEigenmode T hcompact) := by
  letI hfin : ∀ lambda : {lambda : Real // lambda ≠ 0},
      FiniteDimensional Real
        (Module.End.eigenspace (T : Module.End Real E) lambda.1) := by
    intro lambda
    exact nonzeroEigenspace_finiteDimensional T hcompact lambda
  exact compactSelfAdjoint_nonzero_eigenspace_hilbertBasis_orthonormal
    T hsymm (nonzeroEigenspaceBasis T hcompact)

/--
@isnad1 id=eq.1h3v.s9.6eb9f6dc3948 from=translated src=- shape=40f56db2 vocab=4fb0421b
-/
theorem nonzeroEigenmode_diagonal
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (i : NonzeroEigenIndex T) :
    T (nonzeroEigenmode T hcompact i) =
      nonzeroEigenvalue T i • nonzeroEigenmode T hcompact i := by
  exact Module.End.mem_eigenspace_iff.mp
    (nonzeroEigenspaceBasis T hcompact i.1 i.2).property

/--
@isnad1 id=mem.2h3v.s8.182e76e194f8 from=translated src=- shape=2b275c83 vocab=162e546d
-/
theorem nonzeroEigenmode_mem_zeroEigenOrthogonal
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) (i : NonzeroEigenIndex T) :
    nonzeroEigenmode T hcompact i ∈ zeroEigenOrthogonal T := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have horth :
      Module.End.eigenspace (T : Module.End Real E) i.1.1 ⟂
        Module.End.eigenspace (T : Module.End Real E) 0 :=
    (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
      (T := (T : Module.End Real E)) hsymm).isOrtho i.1.2
  exact horth.symm.inner_eq hy
    (nonzeroEigenspaceBasis T hcompact i.1 i.2).property

noncomputable def nonzeroEigenmodeSubspace
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) (i : NonzeroEigenIndex T) :
    zeroEigenOrthogonal T :=
  ⟨nonzeroEigenmode T hcompact i,
    nonzeroEigenmode_mem_zeroEigenOrthogonal T hcompact hsymm i⟩

/--
@isnad1 id=eq.2h2v.s11.db9e80f275a0 from=translated src=- shape=1224ce14 vocab=ff41e036
-/
theorem nonzeroEigenmodeSubspace_dense
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    (Submodule.span Real
      (Set.range (nonzeroEigenmodeSubspace T hcompact hsymm)))ᗮ = ⊥ := by
  letI hfin : ∀ lambda : {lambda : Real // lambda ≠ 0},
      FiniteDimensional Real
        (Module.End.eigenspace (T : Module.End Real E) lambda.1) := by
    intro lambda
    exact nonzeroEigenspace_finiteDimensional T hcompact lambda
  have h :=
    compactSelfAdjoint_nonzero_eigenspace_hilbertBasis_dense_in_zero_orthogonal
      T hcompact hsymm (nonzeroEigenspaceBasis T hcompact)
  convert h using 1
  apply congrArg (fun S : Submodule Real (zeroEigenOrthogonal T) => Sᗮ)
  apply congrArg (Submodule.span Real)
  ext x
  simp only [Set.mem_range]
  constructor <;> rintro ⟨i, rfl⟩
  · exact ⟨i, Subtype.ext rfl⟩
  · exact ⟨i, Subtype.ext rfl⟩

/--
@isnad1 id=orthonor.2h2v.s8.69c55998761c from=translated src=- shape=7e7e4487 vocab=7004142c
-/
theorem nonzeroEigenmodeSubspace_orthonormal
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    Orthonormal Real (nonzeroEigenmodeSubspace T hcompact hsymm) := by
  rw [orthonormal_iff_ite]
  intro i j
  simpa [nonzeroEigenmodeSubspace] using
    (orthonormal_iff_ite.mp
      (nonzeroEigenmode_orthonormal T hcompact hsymm) i j)

noncomputable def nonzeroSpectralHilbertBasis
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) :
    HilbertBasis (NonzeroEigenIndex T) Real (zeroEigenOrthogonal T) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (nonzeroEigenmodeSubspace_orthonormal T hcompact hsymm)
    (nonzeroEigenmodeSubspace_dense T hcompact hsymm)

/--
@isnad1 id=eq.2h3v.s9.f624013a1954 from=translated src=- shape=b8f622b8 vocab=816f896d
-/
@[simp]
theorem coe_nonzeroSpectralHilbertBasis
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) (i : NonzeroEigenIndex T) :
    (((nonzeroSpectralHilbertBasis T hcompact hsymm i :
        zeroEigenOrthogonal T) : E)) =
      nonzeroEigenmode T hcompact i := by
  have hfun := HilbertBasis.coe_mkOfOrthogonalEqBot
    (nonzeroEigenmodeSubspace_orthonormal T hcompact hsymm)
    (nonzeroEigenmodeSubspace_dense T hcompact hsymm)
  exact congrArg (fun x : zeroEigenOrthogonal T => (x : E))
    (congrFun hfun i)

omit [CompleteSpace E] in
/--
@isnad1 id=mem.1h3v.s8.6c37bd42c922 from=translated src=- shape=0db4029d vocab=8ce06158
-/
theorem apply_mem_zeroEigenOrthogonal
    (T : E →L[Real] E) (hsymm : T.IsSymmetric) (f : E) :
    T f ∈ zeroEigenOrthogonal T := by
  exact symmetric_range_le_orthogonal_zero_eigenspace hsymm
    (LinearMap.mem_range.mpr ⟨f, rfl⟩)

/--
@isnad1 id=hassum.2h3v.s9.8c4af80dad0e from=translated src=- shape=7dd59d45 vocab=42504d19
-/
theorem compactSelfAdjoint_action_expansion
    (T : E →L[Real] E) (hcompact : IsCompactOperator T)
    (hsymm : T.IsSymmetric) (f : E) :
    HasSum
      (fun i : NonzeroEigenIndex T =>
        (nonzeroEigenvalue T i *
          inner Real f (nonzeroEigenmode T hcompact i)) •
            nonzeroEigenmode T hcompact i)
      (T f) := by
  let U := zeroEigenOrthogonal T
  let b := nonzeroSpectralHilbertBasis T hcompact hsymm
  have hproj := (b.hasSum_orthogonalProjectionOnto (T f)).mapL U.subtypeL
  have hself : ((U.orthogonalProjectionOnto (T f) : U) : E) = T f := by
    let v : U := ⟨T f, apply_mem_zeroEigenOrthogonal T hsymm f⟩
    have hv := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (K := U) v
    simpa [v] using congrArg (fun x : U => (x : E)) hv
  have hproj' :
      HasSum
        (fun i : NonzeroEigenIndex T =>
          inner Real (T f) (nonzeroEigenmode T hcompact i) •
            nonzeroEigenmode T hcompact i)
        ((U.orthogonalProjectionOnto (T f) : U) : E) := by
    refine hproj.congr_fun ?_
    intro i
    simp [b, U, coe_nonzeroSpectralHilbertBasis, real_inner_comm]
  rw [hself] at hproj'
  refine hproj'.congr_fun ?_
  intro i
  have hinner :
      inner Real (T f) (nonzeroEigenmode T hcompact i) =
        nonzeroEigenvalue T i *
          inner Real f (nonzeroEigenmode T hcompact i) := by
    calc
      inner Real (T f) (nonzeroEigenmode T hcompact i) =
          inner Real f (T (nonzeroEigenmode T hcompact i)) :=
        hsymm f (nonzeroEigenmode T hcompact i)
      _ = _ := by
        rw [nonzeroEigenmode_diagonal T hcompact i]
        simp [inner_smul_right]
  rw [hinner]

end AbstractSpectrum

section CenteredSpectrum

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega → Omega → Real}

abbrev CenteredEigenIndex (hW : IsGraphon W mu) : Type :=
  NonzeroEigenIndex (OddCycleBound.DenseRegion.centeredGraphonOp hW)

def centeredEigenvalue (hW : IsGraphon W mu)
    (i : CenteredEigenIndex hW) : Real :=
  nonzeroEigenvalue (OddCycleBound.DenseRegion.centeredGraphonOp hW) i

noncomputable def centeredEigenmode (hW : IsGraphon W mu)
    (i : CenteredEigenIndex hW) : Lp Real 2 mu :=
  nonzeroEigenmode (OddCycleBound.DenseRegion.centeredGraphonOp hW)
    (centeredGraphonOp_isCompact hW) i

/--
@isnad1 id=orthonor.1h3v.s8.04f99c380dbe from=translated src=- shape=0ceead6f vocab=79abf21f
-/
theorem centeredEigenmode_orthonormal (hW : IsGraphon W mu) :
    Orthonormal Real (centeredEigenmode hW) := by
  exact nonzeroEigenmode_orthonormal
    (OddCycleBound.DenseRegion.centeredGraphonOp hW)
    (centeredGraphonOp_isCompact hW)
    (OddCycleBound.DenseRegion.centeredGraphonOp_isSymmetric hW)

/--
@isnad1 id=eq.1h4v.s13.e26ebbed879e from=translated src=- shape=a16d9fa3 vocab=89d73c57
-/
theorem centeredEigenmode_diagonal (hW : IsGraphon W mu)
    (i : CenteredEigenIndex hW) :
    OddCycleBound.DenseRegion.centeredGraphonOp hW (centeredEigenmode hW i) =
      centeredEigenvalue hW i • centeredEigenmode hW i := by
  exact nonzeroEigenmode_diagonal
    (OddCycleBound.DenseRegion.centeredGraphonOp hW)
    (centeredGraphonOp_isCompact hW) i

/--
@isnad1 id=hassum.1h4v.s13.8d78d0e82b32 from=translated src=- shape=9a2f2509 vocab=e0449056
-/
theorem centeredGraphonOp_action_expansion (hW : IsGraphon W mu)
    (f : Lp Real 2 mu) :
    HasSum
      (fun i : CenteredEigenIndex hW =>
        (centeredEigenvalue hW i * inner Real f (centeredEigenmode hW i)) •
          centeredEigenmode hW i)
      (OddCycleBound.DenseRegion.centeredGraphonOp hW f) := by
  exact compactSelfAdjoint_action_expansion
    (OddCycleBound.DenseRegion.centeredGraphonOp hW)
    (centeredGraphonOp_isCompact hW)
    (OddCycleBound.DenseRegion.centeredGraphonOp_isSymmetric hW) f

/--
@isnad1 id=le.1h4v.s6.9d605af80e18 from=translated src=- shape=bf12f8ef vocab=3be0673e
-/
theorem centeredEigenvalue_finite_square_bound (hW : IsGraphon W mu)
    (s : Finset (CenteredEigenIndex hW)) :
    s.sum (fun i => centeredEigenvalue hW i ^ 2) ≤
      kernelSqNorm mu (centeredKernel W mu) := by
  let hK := centeredKernel_goodK hW
  let row : Omega → Lp Real 2 mu := fun x =>
    OddCycleBound.Spectral.L2Kernel.goodL2 (mu := mu)
      (OddCycleBound.Spectral.L2Kernel.goodK_row hK x)
  have hdiagEnergy :
      s.sum (fun i => centeredEigenvalue hW i ^ 2) =
        s.sum (fun i => ‖centeredKernelOp hW (centeredEigenmode hW i)‖ ^ 2) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hdiag :
        centeredKernelOp hW (centeredEigenmode hW i) =
          centeredEigenvalue hW i • centeredEigenmode hW i := by
      rw [centeredKernelOp_eq_centeredGraphonOp hW]
      exact centeredEigenmode_diagonal hW i
    have hnorm : ‖centeredEigenmode hW i‖ = 1 :=
      (centeredEigenmode_orthonormal hW).norm_eq_one i
    calc
      centeredEigenvalue hW i ^ 2 = |centeredEigenvalue hW i| ^ 2 := by
        rw [sq_abs]
      _ = ‖centeredEigenvalue hW i • centeredEigenmode hW i‖ ^ 2 := by
        rw [norm_smul, hnorm, mul_one, Real.norm_eq_abs]
      _ = ‖centeredKernelOp hW (centeredEigenmode hW i)‖ ^ 2 := by
        rw [hdiag]
  have hrowEnergy :
      s.sum (fun i => ‖centeredKernelOp hW (centeredEigenmode hW i)‖ ^ 2) =
        ∫ x, s.sum (fun i =>
          inner Real (row x) (centeredEigenmode hW i) ^ 2) ∂mu := by
    simpa [centeredKernelOp, hK, row] using
      (sum_norm_kernelOpGoodKCLM_sq_eq_integral_sum_row_inner_l2_sq
        (mu := mu) (centeredKernel_goodK hW)
        (by norm_num : (0 : Real) ≤ 4) (abs_centeredKernel_le_four hW)
        (centeredKernel_symm hW) (centeredEigenmode hW) s)
  have hleftInt : Integrable (fun x : Omega =>
      s.sum (fun i => inner Real (row x) (centeredEigenmode hW i) ^ 2)) mu := by
    simpa [hK, row] using
      (integrable_sum_goodK_row_inner_l2_sq
        (mu := mu) (centeredKernel_goodK hW)
        (by norm_num : (0 : Real) ≤ 4) (abs_centeredKernel_le_four hW)
        (centeredEigenmode hW) s)
  have hrowInt : Integrable (fun x : Omega => inner Real (row x) (row x)) mu := by
    simpa [hK, row] using
      (OddCycleBound.Spectral.L2Kernel.integrable_goodK_row_inner_self
        (mu := mu) (centeredKernel_goodK hW))
  have hpoint : ∀ x : Omega,
      s.sum (fun i => inner Real (row x) (centeredEigenmode hW i) ^ 2) ≤
        inner Real (row x) (row x) := by
    intro x
    exact sum_inner_sq_le_self_of_orthonormal
      (centeredEigenmode_orthonormal hW) (row x) s
  calc
    s.sum (fun i => centeredEigenvalue hW i ^ 2) =
        s.sum (fun i => ‖centeredKernelOp hW (centeredEigenmode hW i)‖ ^ 2) :=
      hdiagEnergy
    _ = ∫ x, s.sum (fun i =>
          inner Real (row x) (centeredEigenmode hW i) ^ 2) ∂mu := hrowEnergy
    _ ≤ ∫ x, inner Real (row x) (row x) ∂mu :=
      integral_mono hleftInt hrowInt hpoint
    _ = kernelSqNorm mu (centeredKernel W mu) := by
      simpa [hK, row] using
        (OddCycleBound.Spectral.L2Kernel.integral_goodK_row_inner_self_eq_kernelSqNorm
          (mu := mu) (centeredKernel_goodK hW))

noncomputable def centeredTraceSq (hW : IsGraphon W mu) : Real :=
  ∑' i : CenteredEigenIndex hW, centeredEigenvalue hW i ^ 2

end CenteredSpectrum

end OddCycleBound.IntermediateRegion
