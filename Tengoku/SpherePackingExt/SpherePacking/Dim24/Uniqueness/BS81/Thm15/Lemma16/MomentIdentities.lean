module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm14.Package
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16.SphereAvgMoments24.Inner
public import Tengoku.Seed.Analysis.InnerProductSpace.Basic
public import Tengoku.Seed.RingTheory.MvPolynomial.Homogeneous
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Moment identities for BS81 Lemma 16

We apply the spherical-design identity (BS81 equation (14)) to the homogeneous polynomials
`x ↦ (⟪x, v⟫ : ℝ) ^ k` for `k = 2,4`. Using the explicit spherical averages on `Ω₂₄`, this yields
numerical identities for the corresponding sums over an equality-case code `C` of size `196560`.

## Main statements
* `sum_inner_sq_eq_8190`
* `sum_inner_pow_four_eq_945`
-/

namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16

noncomputable section

open scoped RealInnerProductSpace BigOperators

open Polynomial MvPolynomial

open Uniqueness.BS81.Thm14

local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)

/-!
We specialize the BS81 design axiom (equation (14)) to the homogeneous polynomials
`p_k(x) = (∑ i, vᵢ Xᵢ)^k`, whose evaluation is `x ↦ (⟪x,v⟫)^k`.
-/

def innerLinearPoly (v : ℝ²⁴) : MvPolynomial (Fin 24) ℝ :=
  ∑ i : Fin 24, (MvPolynomial.C (v i)) * (MvPolynomial.X i)

private lemma sum_eq_card_mul_of_finsetAvg_eq (Cfin : Finset ℝ²⁴) (g : ℝ²⁴ → ℝ) (c : ℝ)
    (havg : finsetAvg Cfin g = c) : Cfin.sum g = (Cfin.card : ℝ) * c := by
  by_cases hC0 : Cfin.card = 0
  · have hCfin : Cfin = ∅ := Finset.card_eq_zero.mp hC0
    simp [hCfin]
  · have hcardR : (Cfin.card : ℝ) ≠ 0 := by exact_mod_cast hC0
    have hmul := congrArg (fun t : ℝ => (Cfin.card : ℝ) * t) (by
      simpa [finsetAvg] using havg)
    simpa [mul_assoc, hcardR] using hmul

end

end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma16
