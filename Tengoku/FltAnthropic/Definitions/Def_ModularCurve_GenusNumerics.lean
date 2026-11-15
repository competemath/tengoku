import Tengoku.Seed.NumberTheory.LegendreSymbol.Basic
import Tengoku.Seed.FieldTheory.Finite.Basic
import Tengoku.Seed.Data.Nat.Totient
import Tengoku.Seed.NumberTheory.Divisors
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace ModularCurve

noncomputable def nuTwo (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + 1 = 0}

noncomputable def nuThree (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + x + 1 = 0}

def cuspCount (N : ℕ) : ℕ :=
  ∑ d ∈ N.divisors, Nat.totient (Nat.gcd d (N / d))

/--
@isnad1 id=eq.0h0v.s3.ae8f6ede9b87 from=translated src=- shape=3c26ae4f vocab=70004159
-/
@[simp]
lemma cuspCount_one : cuspCount 1 = 1 := by
  simp [cuspCount]

noncomputable def genusFormula (N : ℕ) : ℚ :=
  1 + (dedekindPsi N : ℚ) / 12 - (nuTwo N : ℚ) / 4 - (nuThree N : ℚ) / 3
    - (cuspCount N : ℚ) / 2

end ModularCurve
