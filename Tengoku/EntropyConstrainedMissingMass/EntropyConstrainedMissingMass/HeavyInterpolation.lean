import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.BranchEntropy
import Tengoku.Seed.Analysis.Calculus.ImplicitContDiff
import Tengoku.Seed.Analysis.Calculus.Deriv.Prod
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Real multiplicity interpolation of the heavy entropy branch. -/

open Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

namespace EntropyConstrainedMissingMass
noncomputable section

/-- The heavy root; outside its natural domain the value is immaterial.-/
def heavyRoot (h m : ℝ) : ℝ := by
  classical
  exact if he : ∃ z, z ∈ Ioo (1 / (m + 1)) 1 ∧ branchEntropy m z = h then he.choose else 0

private def entropyPair (u : ℝ × ℝ) : ℝ := branchEntropy u.1 u.2

/-- Repeated light mass at real multiplicity.-/
def heavyLight (h m : ℝ) : ℝ := (1 - heavyRoot h m) / m

/-- Positive logarithmic heavy/light mass ratio.-/
def heavySigma (h m : ℝ) : ℝ := Real.log (heavyRoot h m / heavyLight h m)

/-- Real sample-size missing-mass summand.-/
def realMissingMassTerm (s u : ℝ) : ℝ := u * (1-u)^s

/-- Its derivative on `u<1`, in a form convenient for sign comparisons.-/
def realMissingMassDeriv (s u : ℝ) : ℝ := (1-u)^(s-1) * (1-(s+1)*u)

/-- The heavy-family value, interpolated in both multiplicity and sample size.-/
def heavyValue (h s m : ℝ) : ℝ :=
  realMissingMassTerm s (heavyRoot h m) + m * realMissingMassTerm s (heavyLight h m)

/-- The sign-controlling expression in the manuscript.-/
def heavyPsi (s z q : ℝ) : ℝ :=
  realMissingMassDeriv s z - realMissingMassDeriv s q +
    s*q*Real.log (z/q)*(1-q)^(s-1)

end
end EntropyConstrainedMissingMass
