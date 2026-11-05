module

public import Tengoku.KummerCriterion.KummerCriterion.TotallyRealSubfield.ClassGroup
public import Tengoku.Seed.NumberTheory.NumberField.DedekindZeta
import Tengoku.KummerCriterion.KummerCriterion.HMinus.ClassNumberFormula
import Tengoku.Seed.Analysis.SpecialFunctions.Bernstein

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Class-number factors for `hMinus` reduction

This file packages the complex-valued class-number factors and their basic
cyclotomic simplifications used in the `hMinus` reduction chain.
-/

@[expose] public section

noncomputable section

open NumberField

namespace KummerCriterion

section Factors

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]

def cyclotomicClassNumberFactor : ℂ :=
  (((((2 * p : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ (p - 2))) /
    ((2 * Real.pi) ^ ((p - 1) / 2) * Units.regulator K) : ℝ) : ℂ)

/--
@isnad1 id=eq.1h2v.s6.7c2575350995 from=translated src=- shape=2a87bf18 vocab=b3c263ce
-/
lemma h_formula_cyclotomic_complex (hp_odd' : p ≠ 2) :
    ((h K : ℕ) : ℂ) =
      ((NumberField.dedekindZeta_residue K : ℝ) : ℂ) *
        cyclotomicClassNumberFactor (p := p) (K := K) := by
  simpa [cyclotomicClassNumberFactor] using congrArg (fun x : ℝ => (x : ℂ))
    (h_formula_cyclotomic (p := p) (K := K) hp_odd')

def maximalRealSubfieldClassNumberFactor : ℂ :=
  (((((Units.torsionOrder (NumberField.maximalRealSubfield K) : ℝ) *
      Real.sqrt |discr (NumberField.maximalRealSubfield K)|) /
    (2 ^ InfinitePlace.nrRealPlaces (NumberField.maximalRealSubfield K) *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces (NumberField.maximalRealSubfield K) *
        Units.regulator (NumberField.maximalRealSubfield K)) : ℝ) : ℂ))

/--
@isnad1 id=eq.0h1v.s6.895cc13590b7 from=translated src=- shape=45a47e1e vocab=0868c108
-/
lemma hPlus_formula_complex :
    ((hPlus K : ℕ) : ℂ) =
      ((NumberField.dedekindZeta_residue (NumberField.maximalRealSubfield K) : ℝ) : ℂ) *
        maximalRealSubfieldClassNumberFactor (K := K) := by
  simpa [maximalRealSubfieldClassNumberFactor] using congrArg (fun x : ℝ => (x : ℂ))
    (hPlus_formula (K := K))

/--
@isnad1 id=eq.1h2v.s6.5cd8e0b7f4ce from=translated src=- shape=4b52fb3d vocab=0868c108
-/
theorem hPlus_formula_of_Kplus_residue
    {KplusResidue : ℂ}
    (hresPlus :
      ((NumberField.dedekindZeta_residue (NumberField.maximalRealSubfield K) : ℝ) : ℂ) =
        KplusResidue) :
    ((hPlus K : ℕ) : ℂ) =
      maximalRealSubfieldClassNumberFactor (K := K) * KplusResidue := by
  rw [hPlus_formula_complex (K := K), hresPlus]
  ring

omit [IsCMField K] in
/--
@isnad1 id=ne.0h1v.s4.17848ec9277b from=translated src=- shape=21777def vocab=c80651f1
-/
lemma maximalRealSubfieldClassNumberFactor_ne_zero :
  maximalRealSubfieldClassNumberFactor (K := K) ≠ 0 := by
  let L := NumberField.maximalRealSubfield K
  let A : ℝ :=
    2 ^ InfinitePlace.nrRealPlaces L *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces L * Units.regulator L
  let B : ℝ := (Units.torsionOrder L : ℝ) * Real.sqrt |discr L|
  have hA_pos : 0 < A := by
    dsimp [A]
    refine mul_pos ?_ (Units.regulator_pos L)
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hB_pos : 0 < B := by
    dsimp [B]
    refine mul_pos ?_ ?_
    · exact_mod_cast Units.torsionOrder_pos L
    · exact Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero L)))
  have hq_pos : 0 < B / A := div_pos hB_pos hA_pos
  change (((B / A : ℝ) : ℂ) ≠ 0)
  exact_mod_cast hq_pos.ne'

def cyclotomicRelativeLValueCoefficient : ℂ :=
  cyclotomicClassNumberFactor (p := p) (K := K) /
    maximalRealSubfieldClassNumberFactor (K := K)

/-- The `K⁺` class-number scalar used in the cyclotomic `hMinus` reduction.-/
abbrev cyclotomicHPlusFactor : ℂ :=
  maximalRealSubfieldClassNumberFactor (K := K)

omit hp [IsCyclotomicExtension {p} ℚ K] [IsCMField K] in
/--
@isnad1 id=eq.0h2v.s5.dafc98ae1b40 from=translated src=- shape=53d669ca vocab=e1be02fc
-/
lemma cyclotomicClassNumberFactor_eq_relative_coefficient_mul_hPlusFactor :
    cyclotomicClassNumberFactor (p := p) (K := K) =
      cyclotomicRelativeLValueCoefficient (p := p) (K := K) *
        cyclotomicHPlusFactor (K := K) := by
  symm
  rw [cyclotomicRelativeLValueCoefficient, cyclotomicHPlusFactor, div_eq_mul_inv, mul_assoc,
    inv_mul_cancel₀ (maximalRealSubfieldClassNumberFactor_ne_zero (K := K)), mul_one]

end Factors

end KummerCriterion
