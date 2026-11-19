import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.GraphonKrylovBridge
import Tengoku.OddcyclegoodmanLean.OddCycleBound.Spectral.CompactGraphonOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.DenseRegion
open OddCycleBound.Spectral
open OddCycleBound.Spectral.L2Kernel
open OddCycleBound.Spectral.CompactSpectral

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

noncomputable def centeredKernel (W : Omega -> Omega -> Real) (mu : Measure Omega) :
    Omega -> Omega -> Real :=
  fun x y => W x y - degree W mu x - degree W mu y + edgeDensity W mu

omit [IsProbabilityMeasure mu] in
lemma degree_nonneg (hW : IsGraphon W mu) (x : Omega) :
    0 <= degree W mu x := by
  exact integral_nonneg fun y => hW.nonneg x y

lemma degree_le_one (hW : IsGraphon W mu) (x : Omega) :
    degree W mu x <= 1 := by
  rw [degree]
  calc
    (∫ y, W x y ∂mu) <= ∫ _y, (1 : Real) ∂mu := by
      exact integral_mono
        ((goodK_of_isGraphon hW).integrable_row x)
        (integrable_const 1)
        (fun y => hW.le_one x y)
    _ = 1 := by simp

lemma centeredKernel_goodK (hW : IsGraphon W mu) :
    GoodK (centeredKernel W mu) := by
  have hrow : GoodK (fun x _y => degree W mu x) :=
    goodK_rowBroadcast (good_degree hW)
  have hcol : GoodK (fun _x y => degree W mu y) := by
    obtain ⟨C, hC0, hC⟩ := (good_degree hW).bdd
    exact ⟨(good_degree hW).meas.measurable.comp measurable_snd,
      ⟨C, hC0, fun _x y => hC y⟩⟩
  have hconst : GoodK (fun _x _y : Omega => edgeDensity W mu) :=
    goodK_rowBroadcast
      (DenseRegion.good_const (Omega := Omega) (edgeDensity W mu))
  change GoodK
    (fun x y => W x y - degree W mu x - degree W mu y + edgeDensity W mu)
  exact goodK_add
    (goodK_sub (goodK_sub (goodK_of_isGraphon hW) hrow) hcol) hconst

omit [IsProbabilityMeasure mu] in
lemma centeredKernel_symm (hW : IsGraphon W mu) (x y : Omega) :
    centeredKernel W mu x y = centeredKernel W mu y x := by
  unfold centeredKernel
  rw [hW.symm x y]
  ring

lemma abs_centeredKernel_le_four (hW : IsGraphon W mu) (x y : Omega) :
    |centeredKernel W mu x y| <= 4 := by
  have hWx0 := hW.nonneg x y
  have hWx1 := hW.le_one x y
  have hdx0 := degree_nonneg hW x
  have hdx1 := degree_le_one hW x
  have hdy0 := degree_nonneg hW y
  have hdy1 := degree_le_one hW y
  have hq0 := edgeDensity_nonneg hW
  have hq1 := edgeDensity_le_one hW
  rw [abs_le]
  constructor <;> unfold centeredKernel <;> linarith

theorem kernelOpCLM_isCompact (hW : IsGraphon W mu) :
    IsCompactOperator (kernelOpCLM (mu := mu) hW) := by
  exact canonicalGraphonCompact_of_hilbertSchmidtFiniteRankApproxFor
    (mu := mu) hW (graphonHilbertSchmidtFiniteRankApproxFor (mu := mu) hW)

theorem centeredGraphonOp_isCompact (hW : IsGraphon W mu) :
    IsCompactOperator (centeredGraphonOp hW) := by
  unfold centeredGraphonOp
  exact ((kernelOpCLM_isCompact (mu := mu) hW).comp_clm
    (centerProjection (Omega := Omega) (mu := mu))).clm_comp
      (centerProjection (Omega := Omega) (mu := mu))

end OddCycleBound.IntermediateRegion
