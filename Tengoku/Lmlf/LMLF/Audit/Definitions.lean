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

/-- Empty-domain semantics remain vacuous.
@isnad1 id=erroron.0h5v.s4.94bad41110e9 from=translated src=- shape=cb177463 vocab=7a8f7e28
-/
theorem emptyDomain {X E : Type*} [NormedAddCommGroup E]
    (f a : X → E) (b : X → ℝ) : ErrorOn (∅ : Set X) f a b := by
  intro x hx
  exact hx.elim

/-- Equality on the domain produces exactly the zero majorant.
@isnad1 id=erroron.1h5v.s5.33055e64da9c from=translated src=- shape=3a47b4fb vocab=5f3aa2e9
-/
theorem exactZero {X E : Type*} [NormedAddCommGroup E]
    {D : Set X} {f a : X → E} (h : Set.EqOn f a D) :
    ErrorOn D f a (fun _ ↦ 0) := by
  exact ErrorOn.exact h

/-- Transitivity exposes the sum majorant in the conclusion.
@isnad1 id=erroron.2h8v.s6.0c8e9b66ba56 from=translated src=- shape=a4a6550c vocab=8d33b6bc
-/
theorem transSum {X E : Type*} [NormedAddCommGroup E]
    {D : Set X} {f a c : X → E} {b d : X → ℝ}
    (hfa : ErrorOn D f a b) (hac : ErrorOn D a c d) :
    ErrorOn D f c (fun x ↦ b x + d x) := by
  exact ErrorOn.trans hfa hac

end LMLFTest.QB001

namespace LMLFTest.Definitions.Gamma

/-- The integrand in the public Euler formula is integrable on its stated half-plane.
@isnad1 id=integrab.1h1v.s6.01c926e44c28 from=translated src=- shape=3f9c28f9 vocab=6ad81451
-/
theorem eulerIntegrable {s : ℂ} (hs : 0 < s.re) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ ↦ (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1)) (Set.Ioi 0) := by
  exact LMLF.Definitions.gamma_eulerIntegrable hs

/-- Expanded regression check for the public Euler-integral identification.
@isnad1 id=eq.1h1v.s6.0349a18889b4 from=translated src=- shape=a593ece7 vocab=6048f096
-/
theorem eulerFormula {s : ℂ} (hs : 0 < s.re) :
    Complex.Gamma s =
      ∫ x : ℝ in Set.Ioi 0, (Real.exp (-x) : ℂ) * (x : ℂ) ^ (s - 1) := by
  exact LMLF.Definitions.gamma_eq_eulerIntegral hs

/-- The Euler normalization gives `Gamma 1 = 1`.
@isnad1 id=eq.0h0v.s3.b1f3e461e84e from=translated src=- shape=3c26ae4f vocab=a0908a67
-/
theorem eulerAtOne : Complex.Gamma 1 = 1 := by
  rw [LMLF.Definitions.gamma_eq_eulerIntegral (s := 1) (by norm_num)]
  simpa only [Complex.GammaIntegral] using Complex.GammaIntegral_one

/-- The complex and real Mathlib Gamma functions agree on real inputs.
@isnad1 id=eq.0h1v.s3.e61b54a2b955 from=translated src=- shape=c14c2a45 vocab=5c861297
-/
theorem realAgreement (s : ℝ) : Complex.Gamma (s : ℂ) = Real.Gamma s := by
  exact LMLF.Definitions.gamma_ofReal s

/-- Gamma respects complex conjugation.
@isnad1 id=eq.0h1v.s6.108870d52b46 from=translated src=- shape=808f42d9 vocab=b357a306
-/
theorem conjugation (s : ℂ) :
    Complex.Gamma (starRingEnd ℂ s) = starRingEnd ℂ (Complex.Gamma s) := by
  exact Complex.Gamma_conj s

/-- Mathlib totalizes Gamma to zero at every nonpositive integer.
@isnad1 id=eq.0h1v.s4.65da45abedea from=translated src=- shape=e107bfc8 vocab=a1ff51f1
-/
theorem poleTotalization (n : ℕ) : Complex.Gamma (-(n : ℂ)) = 0 := by
  exact LMLF.Definitions.gamma_neg_nat_eq_zero n

end LMLFTest.Definitions.Gamma
