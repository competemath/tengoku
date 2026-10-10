import Tengoku.OpenaiMath.OAI.Analysis.BackwardIntertwiners.SpectralProjections

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

open scoped Classical

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coordinateShift (n : ℤ) : GlobalHilbert →L[ℂ] GlobalHilbert :=
  (fiberReindex (Equiv.addRight (-n))).toLinearIsometry.toContinuousLinearMap.compLpL 2 baseMeasure
lemma coordinateShift_ae (n : ℤ) (f : GlobalHilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ j, coordinateShift n f x j = f x (j-n) := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (fiberReindex (Equiv.addRight (-n))).toLinearIsometry.toContinuousLinearMap f] with x hx j
  change coordinateShift n f x = fiberReindex (Equiv.addRight (-n)) (f x) at hx
  rw [hx]
  rfl
lemma coordinateShift_zero : coordinateShift 0 = 1 := by
  ext1 f
  apply Lp.ext
  filter_upwards [coordinateShift_ae 0 f] with x hx
  ext j
  simpa using hx j
lemma coordinateShift_add (m n : ℤ) : coordinateShift (m+n) = coordinateShift m * coordinateShift n := by
  ext1 f
  apply Lp.ext
  filter_upwards [coordinateShift_ae (m+n) f,coordinateShift_ae m (coordinateShift n f),
    coordinateShift_ae n f] with x hmn hm hn
  ext j
  change coordinateShift (m+n) f x j = coordinateShift m (coordinateShift n f) x j
  rw [hmn,hm,hn]
  exact congrArg (fun k : ℤ => f x k) (by omega)
lemma coordinateShift_norm_le (n : ℤ) (f : GlobalHilbert) : ‖coordinateShift n f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (fiberReindex (Equiv.addRight (-n))).toLinearIsometry.toContinuousLinearMap f] with x hx
  change coordinateShift n f x = fiberReindex (Equiv.addRight (-n)) (f x) at hx
  rw [hx]
  exact le_of_eq ((fiberReindex _).norm_map _)
lemma coordinateShift_norm (n : ℤ) (f : GlobalHilbert) : ‖coordinateShift n f‖ = ‖f‖ := by
  apply le_antisymm (coordinateShift_norm_le n f)
  have h : coordinateShift (-n) (coordinateShift n f) = f := by
    have hh := congrArg (fun T : GlobalHilbert →L[ℂ] GlobalHilbert => T f) (coordinateShift_add (-n) n)
    simpa only [neg_add_cancel,coordinateShift_zero,one_apply_eq_self,mul_apply_eq_comp] using hh.symm
  have hn := coordinateShift_norm_le (-n) (coordinateShift n f)
  rwa [h] at hn

def shiftIsometry (n : ℤ) : GlobalHilbert ≃ₗᵢ[ℂ] GlobalHilbert where
  toFun := coordinateShift n
  invFun := coordinateShift (-n)
  map_add' := (coordinateShift n).map_add
  map_smul' := (coordinateShift n).map_smul
  left_inv f := by
    have h := congrArg (fun T : GlobalHilbert →L[ℂ] GlobalHilbert => T f) (coordinateShift_add (-n) n)
    simpa only [neg_add_cancel,coordinateShift_zero,one_apply_eq_self,mul_apply_eq_comp] using h.symm
  right_inv f := by
    have h := congrArg (fun T : GlobalHilbert →L[ℂ] GlobalHilbert => T f) (coordinateShift_add n (-n))
    simpa only [add_neg_cancel,coordinateShift_zero,one_apply_eq_self,mul_apply_eq_comp] using h.symm
  norm_map' := coordinateShift_norm n

def shiftUnit : (GlobalHilbert →L[ℂ] GlobalHilbert)ˣ where
  val := coordinateShift 1
  inv := coordinateShift (-1)
  val_inv := by rw [←coordinateShift_add]; norm_num [coordinateShift_zero]
  inv_val := by rw [←coordinateShift_add]; norm_num [coordinateShift_zero]

def betaRootSymbol : DiagonalSymbol :=
  ⟨fun x j => (Real.sqrt (explicitBeta x j):ℂ),
    ⟨fun j => Complex.continuous_ofReal.measurable.comp (Real.continuous_sqrt.measurable.comp (measurable_explicitBeta j)),
      1, zero_le_one, fun x j => by
        simp only [Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        apply Real.sqrt_le_one.mpr
        exact (explicitBeta_le x j).trans (Real.exp_le_one_iff.mpr (by norm_num))⟩⟩
lemma betaRootSymbol_star : star betaRootSymbol = betaRootSymbol := by
  apply Subtype.ext
  funext x j
  exact Complex.conj_ofReal _
lemma betaRootSymbol_sq : betaRootSymbol * betaRootSymbol = betaSymbol 0 := by
  apply Subtype.ext
  funext x j
  change (Real.sqrt (explicitBeta x j):ℂ) * (Real.sqrt (explicitBeta x j):ℂ) = (explicitBeta x (j+0):ℂ)
  rw [add_zero,←Complex.ofReal_mul,Real.mul_self_sqrt (explicitBeta_pos _ _).le]
local instance realOperatorTower : IsScalarTower ℝ (GlobalHilbert →L[ℂ] GlobalHilbert) (GlobalHilbert →L[ℂ] GlobalHilbert) where
  smul_assoc scalar first second := by ext vector; rfl
local instance realOperatorCommute : SMulCommClass ℝ (GlobalHilbert →L[ℂ] GlobalHilbert) (GlobalHilbert →L[ℂ] GlobalHilbert) where
  smul_comm scalar first second := by
    apply ContinuousLinearMap.ext
    intro vector
    exact (first.map_smul_of_tower scalar (second vector)).symm
local instance complexNormalCalculus : ContinuousFunctionalCalculus ℂ (GlobalHilbert →L[ℂ] GlobalHilbert) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus
local instance complexClosedCalculus : NonUnitalClosedEmbeddingContinuousFunctionalCalculus ℂ (GlobalHilbert →L[ℂ] GlobalHilbert) IsStarNormal :=
  IsStarNormal.instNonUnitalContinuousFunctionalCalculus
local instance realSelfAdjointCalculus : NonUnitalContinuousFunctionalCalculus ℝ (GlobalHilbert →L[ℂ] GlobalHilbert) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus (A := GlobalHilbert →L[ℂ] GlobalHilbert)

end
end BackwardIntertwiners

end OAI
