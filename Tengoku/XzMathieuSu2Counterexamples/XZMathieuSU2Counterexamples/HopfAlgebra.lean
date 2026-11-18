import Tengoku.Seed.Analysis.Complex.Norm
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The quadratic unit sphere in two complex coordinates. -/

namespace XZMathieuSU2Counterexamples.Hopf

abbrev Space := ℂ × ℂ

def a (z : Space) : ℝ := Complex.normSq z.1 + Complex.normSq z.2
def Sphere := {z : Space // a z = 1}

/--
@isnad1 id=le.0h1v.s3.fcfdbf370353 from=translated src=- shape=b9369acb vocab=e04c3e25
-/
theorem a_nonneg (z : Space) : 0 ≤ a z :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/--
@isnad1 id=iff.0h1v.s4.0a6b6cfb878c from=translated src=- shape=3a75f94e vocab=e42eece7
-/
theorem a_eq_zero_iff (z : Space) : a z = 0 ↔ z = 0 := by
  simp only [a, add_eq_zero_iff_of_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _),
    Complex.normSq_eq_zero, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]

/--
@isnad1 id=eq.0h2v.s5.879fe16b765a from=translated src=- shape=044f21fd vocab=6993c3df
-/
theorem a_smul (c : ℂ) (z : Space) : a (c • z) = Complex.normSq c * a z := by
  simp [a, Complex.normSq_mul, mul_add]

end XZMathieuSU2Counterexamples.Hopf

/- Adapted from MathieuProperty/HopfAlgebra.lean at d7199cfcc342b3e0c332982740d1f3beecf01ab8.
Copyright (c) 2026 long-mathematics; MIT license, see LICENSE. -/
