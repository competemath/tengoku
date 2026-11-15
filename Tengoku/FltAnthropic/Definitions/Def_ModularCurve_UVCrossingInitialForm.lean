import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingModel
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_UVCrossingDominantIndices

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u

namespace ModularCurve.UVCrossingModel

noncomputable section

open IsLocalRing

variable {W : Type u} [CommRing W]

def unitPart (ϖ c : W) : W :=
  (pow_multiplicity_dvd ϖ c).choose

/--
@isnad1 id=eq.0h3v.s5.6e82aa476f2c from=translated src=- shape=7c581378 vocab=2a45eef6
-/
theorem pow_multiplicity_mul_unitPart (ϖ c : W) : ϖ ^ multiplicity ϖ c * unitPart ϖ c = c :=
  (pow_multiplicity_dvd ϖ c).choose_spec.symm

variable [IsDomain W] [IsDiscreteValuationRing W]

open Classical in

def leadingResidue (ϖ c : W) : ResidueField W :=
  if c = 0 then 0 else residue W (unitPart ϖ c)

open Classical in

def initialFormOfSet (ϖ : W) (S : Set ℤ) (ab : PowerSeries W × PowerSeries W) :
    LaurentPolynomial (ResidueField W) :=
  if hS : S.Finite then
    ∑ n ∈ hS.toFinset, LaurentPolynomial.C (leadingResidue ϖ (nfCoeff ab n)) * LaurentPolynomial.T n
  else 0

open Classical in

/--
@isnad1 id=eq.1h5v.s7.9f9fb69de8f5 from=translated src=- shape=6192d87f vocab=19ee85b4
-/
theorem initialFormOfSet_apply (ϖ : W) {S : Set ℤ} (hS : S.Finite)
    (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    (initialFormOfSet ϖ S ab).coeff n = if n ∈ S then leadingResidue ϖ (nfCoeff ab n) else 0 := by
  classical
  rw [initialFormOfSet, dite_eq_left hS]
  simp only [← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_sum,
    AddMonoidAlgebra.coeff_single]
  erw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply, Finset.sum_ite_eq', Set.Finite.mem_toFinset]

def initialForm (ϖ : W) (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) :
    LaurentPolynomial (ResidueField W) :=
  initialFormOfSet ϖ (dominantIndices v E t ab) ab

/--
@isnad1 id=eq.0h6v.s6.23447a8263d5 from=translated src=- shape=607b958b vocab=3afddf19
-/
theorem initialForm_def (ϖ : W) (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) :
    initialForm ϖ v E t ab = initialFormOfSet ϖ (dominantIndices v E t ab) ab := rfl

end

end ModularCurve.UVCrossingModel
