import Tengoku.Seed.NumberTheory.Divisors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace ModularCurve

def sigmaPrimeTo (p n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter (fun d => ¬ p ∣ d), d

def eisensteinTwoCoeff (p n : ℕ) : ℤ := if n = 0 then (p : ℤ) - 1 else 24 * (sigmaPrimeTo p n : ℤ)

/--
@isnad1 id=eq.0h1v.s4.4403ca9c1b22 from=translated src=- shape=458cc6df vocab=e04012be
-/
theorem eisensteinTwoCoeff_zero (p : ℕ) : eisensteinTwoCoeff p 0 = (p : ℤ) - 1 := by
  simp [eisensteinTwoCoeff]

/--
@isnad1 id=eq.1h2v.s5.2d1d259d4ac8 from=translated src=- shape=0e45e8ab vocab=3a53d0ad
-/
theorem eisensteinTwoCoeff_of_ne_zero (p : ℕ) {n : ℕ} (hn : n ≠ 0) :
    eisensteinTwoCoeff p n = 24 * (sigmaPrimeTo p n : ℤ) := by
  simp [eisensteinTwoCoeff, hn]

end ModularCurve
