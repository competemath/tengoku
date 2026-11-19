import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.SafeSubspace

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
variable {W : Omega -> Omega -> Real}

def leadingEigenvaluePos (phi : Omega -> Real) (x : Omega) : Real :=
  (|phi x| + phi x) / 2

noncomputable def leadingEigenvalueAbsMean (mu : Measure Omega)
    (phi : Omega -> Real) : Real :=
  ∫ x, |phi x| ∂mu

noncomputable def leadingEigenvalueShapeZ (mu : Measure Omega)
    (phi : Omega -> Real) : Real :=
  leadingEigenvalueAbsMean mu phi ^ 2

noncomputable def leadingEigenvalueShapeB (mu : Measure Omega)
    (phi : Omega -> Real) : Real :=
  ∫ x, |phi x| * phi x ∂mu

def leadingEigenvalueResidual (a b : Real) (phi : Omega -> Real) : Omega -> Real :=
  (fun x => |phi x|) - (fun _ => a) - b • phi

lemma good_leadingEigenvaluePos {phi : Omega -> Real} (hphi : Good phi) :
    Good (leadingEigenvaluePos phi) := by
  let h := good_smul ((2 : Real)⁻¹)
    (good_add (good_abs hphi) hphi)
  convert h using 1
  funext x
  simp [leadingEigenvaluePos, Pi.smul_apply, div_eq_mul_inv]
  ring

omit [MeasurableSpace Omega] in
lemma leadingEigenvaluePos_nonneg (phi : Omega -> Real) (x : Omega) :
    0 <= leadingEigenvaluePos phi x := by
  unfold leadingEigenvaluePos
  nlinarith [neg_le_abs (phi x)]

omit [MeasurableSpace Omega] in
lemma le_leadingEigenvaluePos (phi : Omega -> Real) (x : Omega) :
    phi x <= leadingEigenvaluePos phi x := by
  unfold leadingEigenvaluePos
  nlinarith [le_abs_self (phi x)]

lemma good_leadingEigenvalueResidual {phi : Omega -> Real} (hphi : Good phi)
    (a b : Real) :
    Good (leadingEigenvalueResidual a b phi) := by
  unfold leadingEigenvalueResidual
  exact good_sub
    (good_sub (good_abs hphi) (good_const (Omega := Omega) a))
    (good_smul b hphi)

theorem centeredGraphonOp_compl_goodL2_eq_neg
    (hW : IsGraphon W mu) {f : Omega -> Real} (hf : Good f)
    (hmean : mean mu f = 0) :
    centeredGraphonOp (isGraphon_compl hW) (goodL2 (mu := mu) hf) =
      -centeredGraphonOp hW (goodL2 (mu := mu) hf) := by
  let P := centerProjection (Omega := Omega) (mu := mu)
  have hcenter : P (goodL2 (mu := mu) hf) = goodL2 (mu := mu) hf :=
    centerProjection_apply_of_mean_zero hf hmean
  have hkernel :
      kernelOpCLM (mu := mu) (isGraphon_compl hW)
          (goodL2 (mu := mu) hf) =
        -kernelOpCLM (mu := mu) hW (goodL2 (mu := mu) hf) := by
    rw [kernelOpCLM_goodL2_eq_goodL2, kernelOpCLM_goodL2_eq_goodL2]
    let hU := good_kernelOp (isGraphon_compl hW) hf
    let hneg := good_smul (-1 : Real) (good_kernelOp hW hf)
    have heq :
        goodL2 (mu := mu) hU = goodL2 (mu := mu) hneg := by
      apply MemLp.toLp_congr
        (good_memLp_two hU) (good_memLp_two hneg)
      exact ae_of_all _ fun x => by
        change kernelOp (compl W) mu f x =
          (-1 : Real) * kernelOp W mu f x
        rw [kernelOp_compl hW hf x, hmean]
        ring
    rw [heq, goodL2_smul (-1 : Real) (good_kernelOp hW hf)]
    simp
  unfold centeredGraphonOp
  change P
      (kernelOpCLM (mu := mu) (isGraphon_compl hW)
        (P (goodL2 (mu := mu) hf))) =
    -P
      (kernelOpCLM (mu := mu) hW
        (P (goodL2 (mu := mu) hf)))
  rw [hcenter, hkernel, map_neg]

theorem kernelOpCLM_compl_leading_eigenvalue_eq_hub_add
    (hW : IsGraphon W mu) (i : CenteredEigenIndex hW)
    {phi : Omega -> Real} (hphi : Good phi)
    (hrep : centeredEigenmode hW i = goodL2 (mu := mu) hphi)
    (hmean : mean mu phi = 0) :
    let hU := isGraphon_compl hW
    let c := inner Real (centeredDegreeL2 hU) (centeredEigenmode hW i)
    kernelOpCLM (mu := mu) hU (centeredEigenmode hW i) =
      c • oneL2 (Omega := Omega) mu +
        complementEigenvalue hW i • centeredEigenmode hW i := by
  dsimp only
  let one := oneL2 (Omega := Omega) mu
  let P := centerProjection (Omega := Omega) (mu := mu)
  let T := kernelOpCLM (mu := mu) (isGraphon_compl hW)
  let v := centeredEigenmode hW i
  let c := inner Real (centeredDegreeL2 (isGraphon_compl hW)) v
  have hvcenter : P v = v := by
    dsimp [P, v]
    rw [hrep]
    exact centerProjection_apply_of_mean_zero hphi hmean
  have hcoefficient : inner Real one (T v) = c := by
    have hT : T.toLinearMap.IsSymmetric :=
      kernelOpCLM_isSymmetric (isGraphon_compl hW)
    have hP : P.toLinearMap.IsSymmetric :=
      centerProjection_isSymmetric
    calc
      inner Real one (T v) = inner Real (T one) v :=
        (hT.apply_clm one v).symm
      _ = inner Real (P (T one)) v := by
        rw [hP.apply_clm, hvcenter]
      _ = inner Real (centeredDegreeL2 (isGraphon_compl hW)) v := by
        dsimp [one, T, P]
        rw [centerProjection_kernelOpCLM_one_eq_centeredDegreeL2]
      _ = c := rfl
  have hbody : P (T v) = complementEigenvalue hW i • v := by
    have hcomp :
        centeredGraphonOp (isGraphon_compl hW) v =
          -centeredGraphonOp hW v := by
      dsimp [v]
      rw [hrep]
      exact centeredGraphonOp_compl_goodL2_eq_neg hW hphi hmean
    calc
      P (T v) = centeredGraphonOp (isGraphon_compl hW) v := by
        unfold centeredGraphonOp
        change P (T v) = P (T (P v))
        rw [hvcenter]
      _ = -centeredGraphonOp hW v := hcomp
      _ = complementEigenvalue hW i • v := by
        rw [centeredEigenmode_diagonal]
        simp [complementEigenvalue, v]
  have hdecomp : T v = inner Real one (T v) • one + P (T v) := by
    dsimp [P]
    unfold centerProjection
    simp only [sub_apply, one_apply_eq_self,
      InnerProductSpace.rankOne_apply]
    abel
  simpa [one, T, v, c, hcoefficient, hbody] using hdecomp

end OddCycleBound.IntermediateRegion
