import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.GraphonShiftIdentity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.DenseRegion
open OddCycleBound.Spectral.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega → Omega → Real}

def complementEigenvalue (hW : IsGraphon W mu)
    (i : CenteredEigenIndex hW) : Real :=
  -centeredEigenvalue hW i

/--
@isnad1 id=eq.4h5v.s7.6a9a2240f634 from=translated src=- shape=e704b657 vocab=1d36fb37
-/
theorem complement_leading_eigenvalue_unique
    (hW : IsGraphon W mu)
    (hq : (1 : Real) / 3 < 1 - edgeDensity W mu)
    {i j : CenteredEigenIndex hW}
    (hi : 1 - edgeDensity W mu < complementEigenvalue hW i)
    (hj : 1 - edgeDensity W mu < complementEigenvalue hW j) :
    i = j := by
  classical
  by_contra hij
  have hbound := centeredEigenvalue_finite_square_bound hW ({i, j} : Finset _)
  have hkernel := centeredKernel_hilbertSchmidt_bound hW
  have hsquares :
      centeredEigenvalue hW i ^ 2 + centeredEigenvalue hW j ^ 2 ≤
        edgeDensity W mu * (1 - edgeDensity W mu) := by
    have hfinite :
        centeredEigenvalue hW i ^ 2 + centeredEigenvalue hW j ^ 2 ≤
          kernelSqNorm mu (centeredKernel W mu) := by
      simpa [hij, add_comm] using hbound
    have hkernel' :
        kernelSqNorm mu (centeredKernel W mu) ≤
          edgeDensity W mu * (1 - edgeDensity W mu) := by
      nlinarith [sq_nonneg ‖centeredDegreeL2 hW‖]
    exact hfinite.trans hkernel'
  have hq0 : 0 ≤ 1 - edgeDensity W mu := by linarith
  have hiSq := mul_self_lt_mul_self hq0 hi
  have hjSq := mul_self_lt_mul_self hq0 hj
  dsimp [complementEigenvalue] at hiSq hjSq
  nlinarith

/--
@isnad1 id=eq.0h2v.s12.94758ff1dd49 from=translated src=- shape=88571b37 vocab=2ca34b36
-/
lemma centerProjection_oneL2 :
    centerProjection (Omega := Omega) (mu := mu)
        (oneL2 (Omega := Omega) mu) = 0 := by
  unfold centerProjection
  simp only [sub_apply, one_apply_eq_self, InnerProductSpace.rankOne_apply]
  rw [inner_oneL2_oneL2, one_smul, sub_self]

/--
@isnad1 id=eq.1h4v.s7.e4375a9d4251 from=translated src=- shape=d87b5736 vocab=cf06b03b
-/
theorem inner_oneL2_centeredEigenmode_eq_zero
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW) :
    inner Real (oneL2 (Omega := Omega) mu) (centeredEigenmode hW i) = 0 := by
  let P := centerProjection (Omega := Omega) (mu := mu)
  have hPone : P (oneL2 (Omega := Omega) mu) = 0 :=
    centerProjection_oneL2
  have hzero :
      inner Real (oneL2 (Omega := Omega) mu)
        (centeredGraphonOp hW (centeredEigenmode hW i)) = 0 := by
    unfold centeredGraphonOp
    change inner Real (oneL2 (Omega := Omega) mu)
      (P (kernelOpCLM (mu := mu) hW (P (centeredEigenmode hW i)))) = 0
    rw [← (centerProjection_isSymmetric
      (Omega := Omega) (mu := mu)).apply_clm, hPone, inner_zero_left]
  rw [centeredEigenmode_diagonal hW i, inner_smul_right] at hzero
  have hne : centeredEigenvalue hW i ≠ 0 := by
    exact nonzeroEigenvalue_ne (centeredGraphonOp hW) i
  exact (mul_eq_zero.mp hzero).resolve_left hne

/--
@isnad1 id=hasgoodr.1h4v.s5.1fce975e9ca4 from=translated src=- shape=f80a55ac vocab=e9fd9640
-/
theorem centeredEigenmode_hasGoodRepresentative
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW) :
    OddCycleBound.Spectral.InfiniteSpectral.HasGoodRepresentative (mu := mu)
      (centeredEigenmode hW i) := by
  let hK := centeredKernel_goodK hW
  let hf : Good (kernelOp (centeredKernel W mu) mu
      (fun y : Omega => centeredEigenmode hW i y)) :=
    good_kernelOp_goodK_l2 (mu := mu) hK
      (by norm_num : (0 : Real) ≤ 4) (abs_centeredKernel_le_four hW)
      (centeredEigenmode hW i)
  have himage :
      centeredKernelOp hW (centeredEigenmode hW i) =
        goodL2 (mu := mu) hf := by
    unfold centeredKernelOp
    rw [kernelOpGoodKCLM_eq_kernelOpGoodKL2OfL2_apply
      (mu := mu) hK (by norm_num : (0 : Real) ≤ 4)
      (abs_centeredKernel_le_four hW) (centeredKernel_symm hW)]
    rfl
  have hdiag :
      centeredKernelOp hW (centeredEigenmode hW i) =
        centeredEigenvalue hW i • centeredEigenmode hW i := by
    rw [centeredKernelOp_eq_centeredGraphonOp hW]
    exact centeredEigenmode_diagonal hW i
  have hne : centeredEigenvalue hW i ≠ 0 :=
    nonzeroEigenvalue_ne (centeredGraphonOp hW) i
  exact
    OddCycleBound.Spectral.InfiniteSpectral.hasGoodRepresentative_of_nonzero_eigenmode_and_good_operator_image
      hf himage hdiag hne

/--
@isnad1 id=ex.1h4v.s8.05108925a68a from=translated src=- shape=5fd6c69c vocab=39c2d9a7
-/
theorem exists_good_centeredEigenfunction
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW) :
    ∃ (phi : Omega → Real), ∃ hphi : Good phi,
      centeredEigenmode hW i = goodL2 (mu := mu) hphi ∧
      mean mu phi = 0 ∧
      (∫ x, phi x * phi x ∂mu) = 1 := by
  rcases centeredEigenmode_hasGoodRepresentative hW i with
    ⟨phi, hphi, hrep⟩
  have hmean := inner_oneL2_centeredEigenmode_eq_zero hW i
  rw [hrep, inner_oneL2_goodL2_eq_mean hphi] at hmean
  have hnorm : ‖centeredEigenmode hW i‖ = 1 :=
    (centeredEigenmode_orthonormal hW).norm_eq_one i
  have hnormSq : ‖goodL2 (mu := mu) hphi‖ ^ 2 = 1 := by
    rw [← hrep, hnorm]
    norm_num
  rw [norm_goodL2_sq_eq_integral_mul hphi] at hnormSq
  exact ⟨phi, hphi, hrep, hmean, hnormSq⟩

end OddCycleBound.IntermediateRegion
