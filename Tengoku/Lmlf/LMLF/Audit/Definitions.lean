import Tengoku.Lmlf.LMLF.Definitions
import Tengoku.Lmlf.LMLF.Quantitative.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Definition audits

This separately built consumer expands the Gamma identification theorem and records inexpensive
checks of the conventions inherited from Mathlib.  It is deliberately not imported by the semantic
library root.

These checks audit the selected Mathlib object.  They do not resolve the blueprint's outstanding
source-wide questions about Olver's analytic continuation and exceptional-value conventions.
-/

namespace LMLFTest.QB001

open QuantitativeAnalysis

/-- Empty-domain semantics remain vacuous.-/
theorem emptyDomain {X E : Type*} [NormedAddCommGroup E]
    (f a : X → E) (b : X → ℝ) : ErrorOn (∅ : Set X) f a b := by
  intro x hx
  exact hx.elim

/-- Equality on the domain produces exactly the zero majorant.-/
theorem exactZero {X E : Type*} [NormedAddCommGroup E]
    {D : Set X} {f a : X → E} (h : Set.EqOn f a D) :
    ErrorOn D f a (fun _ ↦ 0) := by
  exact ErrorOn.exact h

/-- Transitivity exposes the sum majorant in the conclusion.-/
theorem transSum {X E : Type*} [NormedAddCommGroup E]
    {D : Set X} {f a c : X → E} {b d : X → ℝ}
    (hfa : ErrorOn D f a b) (hac : ErrorOn D a c d) :
    ErrorOn D f c (fun x ↦ b x + d x) := by
  exact ErrorOn.trans hfa hac

end LMLFTest.QB001

namespace LMLFTest.Definitions.Gamma

/-- The integrand in the public Euler formula is integrable on its stated half-plane.-/
theorem eulerIntegrable {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ ↦ (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)) (Set.Ioi 0) := by
  exact LMLF.Definitions.gamma_eulerIntegrable hs

/-- Expanded regression check for the public Euler-integral identification.-/
theorem eulerFormula {s : ℂ} (hs : 0 < s.re) :
    Complex.Gamma s =
      ∫ x : ℝ in Set.Ioi 0, (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1) := by
  exact LMLF.Definitions.gamma_eq_eulerIntegral hs

/-- The Euler normalization gives `Gamma 1 = 1`.-/
theorem eulerAtOne : Complex.Gamma 1 = 1 := by
  rw [LMLF.Definitions.gamma_eq_eulerIntegral (s := 1) (by norm_num)]
  simpa only [Complex.GammaIntegral] using Complex.GammaIntegral_one

/-- The complex and real Mathlib Gamma functions agree on real inputs.-/
theorem realAgreement (s : ℝ) : Complex.Gamma (s : ℂ) = Real.Gamma s := by
  exact LMLF.Definitions.gamma_ofReal s

/-- Gamma respects complex conjugation.-/
theorem conjugation (s : ℂ) :
    Complex.Gamma (starRingEnd ℂ s) = starRingEnd ℂ (Complex.Gamma s) := by
  exact Complex.Gamma_conj s

/-- Mathlib totalizes Gamma to zero at every nonpositive integer.-/
theorem poleTotalization (n : ℕ) : Complex.Gamma (-(n : ℂ)) = 0 := by
  exact LMLF.Definitions.gamma_neg_nat_eq_zero n

end LMLFTest.Definitions.Gamma
