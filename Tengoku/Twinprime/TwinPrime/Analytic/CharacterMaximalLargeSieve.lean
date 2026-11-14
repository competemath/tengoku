import Tengoku.Twinprime.TwinPrime.Analytic.CharacterBilinear
import Tengoku.Twinprime.TwinPrime.Analytic.DyadicMaximal
import Tengoku.Twinprime.TwinPrime.Analytic.DyadicIntervalCover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Independently selected character endpoints in the large sieve

The fixed-interval large sieve controls the binary tree of interval sums.
Its dyadic maximal inequality then permits a different prefix endpoint for
every primitive character. No maximal estimate is assumed.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- The finite family of primitive characters at all positive levels up to Q.-/
def primitiveCharacterFamily (Q : ℕ) : Finset (Σ q : ℕ, DirichletCharacter ℂ q) :=
  (Icc 1 Q).sigma fun q =>
    (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive)

def primitiveCharacterWeight (p : Σ q : ℕ, DirichletCharacter ℂ q) : ℝ :=
  (p.1 : ℝ) / Nat.totient p.1

/--
@isnad1 id=le.0h1v.s4.4b98d988e0f2 from=translated src=- shape=1046a67b vocab=a395a1e8
-/
theorem primitiveCharacterWeight_nonneg (p : Σ q : ℕ, DirichletCharacter ℂ q) :
    0 ≤ primitiveCharacterWeight p := by unfold primitiveCharacterWeight; positivity

/-- The largest squared prefix norm in a padded dyadic interval.-/
def characterPrefixMaxSq {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ℕ → ℂ) (M k : ℕ) : ℝ :=
  (Icc M (M + 2 ^ k)).sup' ⟨M, mem_Icc.mpr ⟨le_rfl, Nat.le_add_right _ _⟩⟩
    (fun t => ‖∑ n ∈ Ico M t, a n * χ n‖ ^ 2)

end TwinPrime.Analytic
