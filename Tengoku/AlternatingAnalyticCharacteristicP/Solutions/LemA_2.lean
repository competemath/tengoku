import Tengoku.Seed.Analysis.Normed.Field.Ultra
import Tengoku.Seed.Algebra.CharP.Defs
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.PositiveCharacteristic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proof of Lemma A.2

Uses `charP_isUltrametricDist` (AlternatingAnalytic/Analysis/PositiveCharacteristic.lean).
-/
namespace Tengoku.AlternatingAnalyticCharacteristicP end Tengoku.AlternatingAnalyticCharacteristicP open Tengoku.AlternatingAnalyticCharacteristicP
namespace AlternatingAnalyticChallenge.LemA_2

/-- A normed field of positive characteristic is nonarchimedean.-/
theorem nonarchimedean_of_charP_pos
    (K : Type*) [NormedField K] (p : ℕ) [CharP K p] (hp : 0 < p) :
    IsUltrametricDist K := by
  have : NeZero p := ⟨hp.ne'⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos K p
  exact charP_isUltrametricDist p

end AlternatingAnalyticChallenge.LemA_2
-- Tengoku: root names of this library moved to Tengoku.AlternatingAnalyticCharacteristicP so they do not collide with other libraries (generated)
