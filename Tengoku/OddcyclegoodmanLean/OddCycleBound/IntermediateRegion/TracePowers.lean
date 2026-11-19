import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.SpectralFoundation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.Spectral
open OddCycleBound.Spectral.InfiniteSpectral
open OddCycleBound.Spectral.L2Kernel

universe u v

section BoundedKernelTrace

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {K : Omega → Omega → Real}

/--
@isnad1 id=eq.4h6v.s8.52f57a641b58 from=translated src=- shape=d640c390 vocab=a9136c7d
-/
lemma kernelOpGoodKCLM_iter_goodL2_eq_compPow
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    {f : Omega → Real} (hf : Good f) (n : Nat) :
    clmIter (mu := mu) (kernelOpGoodKCLM (mu := mu) hK hC0 hKC) (n + 1)
        (goodL2 (mu := mu) hf) =
      kernelOpL2OfGoodK (mu := mu) (goodK_compPow (μ := mu) hK n) hf := by
  rw [kernelOpGoodKCLM_iter_goodL2 (mu := mu) hK hC0 hKC hf (n + 1)]
  rw [← kernelOpL2OfGoodK_compPow_eq_goodL2_iter_succ
    (mu := mu) hK hf n]

/--
@isnad1 id=eq.4h5v.s8.e6f1cac00b7b from=translated src=- shape=6edbd01e vocab=2ee69688
-/
lemma trace_compPow_eq_integral_row_inner_goodK_clmIter
    (hK : GoodK K) {C : Real} (hC0 : 0 ≤ C)
    (hKC : ∀ x y, |K x y| ≤ C)
    (hsymm : ∀ x y, K x y = K y x) (k : Nat) :
    trace mu (compPow mu K (k + 2)) =
      ∫ x, inner Real
        (goodL2 (mu := mu) (goodK_row hK x))
        (clmIter (mu := mu) (kernelOpGoodKCLM (mu := mu) hK hC0 hKC)
          (k + 1) (goodL2 (mu := mu) (goodK_row hK x))) ∂mu := by
  have hpowk : GoodK (compPow mu K k) := goodK_compPow (μ := mu) hK k
  have hpowks : GoodK (compPow mu K (k + 1)) :=
    goodK_compPow (μ := mu) hK (k + 1)
  have htrace_rotate :
      trace mu (compPow mu K (k + 2)) =
        trace mu (comp mu (compPow mu K (k + 1)) K) := by
    change trace mu (comp mu K (compPow mu K (k + 1))) =
      trace mu (comp mu (compPow mu K (k + 1)) K)
    exact trace_comp_comm (μ := mu) hK hpowks
  rw [htrace_rotate, trace]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  let hrow : Good (fun y : Omega => K x y) := goodK_row hK x
  have hiter :
      clmIter (mu := mu) (kernelOpGoodKCLM (mu := mu) hK hC0 hKC) (k + 1)
          (goodL2 (mu := mu) hrow) =
        kernelOpL2OfGoodK (mu := mu) hpowk hrow := by
    exact kernelOpGoodKCLM_iter_goodL2_eq_compPow
      (mu := mu) hK hC0 hKC hrow k
  have hkernel :
      kernelOp K mu
          (fun y : Omega =>
            (kernelOpL2OfGoodK (mu := mu) hpowk hrow : Lp Real 2 mu) y)
          x =
        kernelOp K mu (kernelOp (compPow mu K k) mu (fun y => K x y)) x := by
    unfold kernelOp
    refine integral_congr_ae ?_
    filter_upwards [kernelOpL2OfGoodK_ae_eq (mu := mu) hpowk hrow] with y hy
    rw [hy]
    simp [kernelOp]
  calc
    comp mu (compPow mu K (k + 1)) K x x
        = kernelOp (compPow mu K (k + 1)) mu (fun y : Omega => K x y) x := by
          unfold comp kernelOp
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          change compPow mu K (k + 1) x y * K y x =
            compPow mu K (k + 1) x y * K x y
          rw [hsymm y x]
    _ = kernelOp K mu (kernelOp (compPow mu K k) mu (fun y => K x y)) x := by
          rw [← kernelOp_comp_eq_kernelOp_kernelOp
            (mu := mu) hK hpowk hrow]
          rfl
    _ = kernelOp K mu
          (fun y : Omega =>
            (kernelOpL2OfGoodK (mu := mu) hpowk hrow : Lp Real 2 mu) y)
          x := hkernel.symm
    _ = inner Real (goodL2 (mu := mu) hrow)
          (kernelOpL2OfGoodK (mu := mu) hpowk hrow) := by
          rw [inner_goodK_row_l2_eq_kernelOp (mu := mu) hK
            (kernelOpL2OfGoodK (mu := mu) hpowk hrow) x]
    _ = inner Real (goodL2 (mu := mu) hrow)
          (clmIter (mu := mu) (kernelOpGoodKCLM (mu := mu) hK hC0 hKC)
            (k + 1) (goodL2 (mu := mu) hrow)) := by rw [hiter]

end BoundedKernelTrace

section IndexedExpansion

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable {ι : Type v}

end IndexedExpansion

section CenteredTrace

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega → Omega → Real}

/--
@isnad1 id=le.1h4v.s5.ab0ad9e6233b from=translated src=- shape=5e8be34f vocab=14efc1ad
-/
theorem abs_centeredEigenvalue_le_four (hW : IsGraphon W mu)
    (i : CenteredEigenIndex hW) :
    |centeredEigenvalue hW i| ≤ 4 := by
  have hnormMode : ‖centeredEigenmode hW i‖ = 1 :=
    (centeredEigenmode_orthonormal hW).norm_eq_one i
  have hop : ‖centeredKernelOp hW‖ ≤ 4 := by
    exact norm_kernelOpGoodKCLM_le (mu := mu) (centeredKernel_goodK hW)
      (by norm_num : (0 : Real) ≤ 4) (abs_centeredKernel_le_four hW)
  calc
    |centeredEigenvalue hW i| =
        ‖centeredEigenvalue hW i • centeredEigenmode hW i‖ := by
          rw [norm_smul, hnormMode, mul_one, Real.norm_eq_abs]
    _ = ‖centeredKernelOp hW (centeredEigenmode hW i)‖ := by
          rw [centeredKernelOp_eq_centeredGraphonOp hW,
            centeredEigenmode_diagonal hW i]
    _ ≤ ‖centeredKernelOp hW‖ * ‖centeredEigenmode hW i‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ = ‖centeredKernelOp hW‖ * 1 := by rw [hnormMode]
    _ ≤ 4 * 1 := mul_le_mul_of_nonneg_right hop (by norm_num)
    _ = 4 := by norm_num

end CenteredTrace

end OddCycleBound.IntermediateRegion
