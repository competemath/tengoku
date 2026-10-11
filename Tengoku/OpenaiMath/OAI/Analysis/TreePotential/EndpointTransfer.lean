import Tengoku.OpenaiMath.OAI.Analysis.TreePotential.RealModuli

namespace OAI

noncomputable section
open Set
open scoped ENNReal
open Set Filter Topology
open scoped Classical

namespace BoundedTreePotentials
section RealEndpointTransfer
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma averagedModulusReal_lower (h : ¬IsAUC E) {a t : ℝ}
    (ha : (a : EReal)≤ averagedModulus E t) : a≤ averagedModulusReal E t := by
  apply EReal.coe_le_coe_iff.mp
  rwa [averagedModulusReal_coe E (infiniteDimensional_of_not_isAUC E h)]

lemma maximumModulusReal_lower (h : ¬IsAUC E) {a t : ℝ}
    (ha : (a : EReal)≤ maximumModulus E t) : a≤ maximumModulusReal E t := by
  apply EReal.coe_le_coe_iff.mp
  rwa [maximumModulusReal_coe E (infiniteDimensional_of_not_isAUC E h)]

lemma oneSidedModulusReal_zero (h : ¬IsAUC E) {t : ℝ}
    (ht : oneSidedModulus E t=0) : oneSidedModulusReal E t=0 := by
  apply EReal.coe_eq_coe_iff.mp
  rw [oneSidedModulusReal_coe E (infiniteDimensional_of_not_isAUC E h),ht]
  rfl
end RealEndpointTransfer

namespace TreeCalculus

end TreeCalculus

namespace FreeRoot

end FreeRoot

section CostRealObstructions
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

end CostRealObstructions

namespace CostHeads

theorem linear_averaged_modulus_real {t : ℝ} (ht : 0< t) :
    Real.sqrt (1+t^2/16)-1≤ averagedModulusReal LinearOuter t :=
  averagedModulusReal_lower (linearOuter_no_equivalent_AUC (.refl ℝ _)) (linear_averaged_modulus ht)

theorem quadratic_averaged_modulus_real {t : ℝ} (ht : 0< t) :
    Real.sqrt (1+t^2/16)-1≤ averagedModulusReal QuadraticOuter t :=
  averagedModulusReal_lower (quadraticOuter_no_equivalent_AUC (.refl ℝ _)) (quadratic_averaged_modulus ht)

theorem quadratic_maximum_modulus_real {t : ℝ} (ht : 0< t) :
    Real.sqrt (1+t^2/16)-1≤ maximumModulusReal QuadraticOuter t :=
  maximumModulusReal_lower (quadraticOuter_no_equivalent_AUC (.refl ℝ _)) (quadratic_maximum_modulus ht)

theorem quadratic_maximum_modulus_real_positive {t : ℝ} (ht : 0< t) :
    0< maximumModulusReal QuadraticOuter t := by
  apply EReal.coe_lt_coe_iff.mp
  rw [maximumModulusReal_coe QuadraticOuter
    (infiniteDimensional_of_not_isAUC _ (quadraticOuter_no_equivalent_AUC (.refl ℝ _)))]
  exact quadratic_maximum_modulus_positive ht
end CostHeads

namespace Segments

theorem start_maximum_modulus_real {t : ℝ} (ht : 0< t) :
    Real.sqrt (1+t^2/64)-1≤ maximumModulusReal StartSpace t :=
  maximumModulusReal_lower (start_no_equivalent_AUC (.refl ℝ _)) (start_maximum_modulus ht)

section RealObstructions
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

end RealObstructions
end Segments
end BoundedTreePotentials

end

end OAI
