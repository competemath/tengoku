import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_LaurentCoeff
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_coeffMap_qExpand
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_coeff_jqModC_pow_self
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_coeff_jqModC_pow_of_lt
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_coeff_jqModC_neg_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve

namespace ModularCurve

section CoeffMapSupply

variable {R S : Type*} [CommRing R] [CommRing S]

/--
@isnad1 id=eq.0h4v.s9.768819a1ab66 from=translated src=- shape=3c04b3c9 vocab=18211310
-/
theorem coeffMap_ofPowerSeries (f : R →+* S) (p : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R p) = HahnSeries.ofPowerSeries ℤ S (p.map f) := by
  ext k
  rw [coeffMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

end CoeffMapSupply

section JExpansion

variable (R : Type*) [CommRing R]

end JExpansion

section QExpandAlg

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

def qExpandAlgHomC : LaurentSeries K →ₐ[K] LaurentSeries K where
  __ := qExpand K N
  commutes' c := by
    show qExpand K N (algebraMap K (LaurentSeries K) c) = algebraMap K (LaurentSeries K) c
    rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

/--
@isnad1 id=eq.0h3v.s9.c31e8132e215 from=translated src=- shape=f552a4f7 vocab=8f514ec5
-/
@[simp]
theorem qExpandAlgHomC_apply (f : LaurentSeries K) : qExpandAlgHomC K N f = qExpand K N f := rfl

end QExpandAlg

section FunctionField

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

def divisorExpansionsC : Set (LaurentSeries K) :=
  {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = qExpand K d (jqModC K)}

def modularFunctionFieldFullC : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K (divisorExpansionsC K N)

end FunctionField

section Jacobian

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]

end Jacobian

end ModularCurve

end
