/-
Nucleo Lean della campagna Agrawal (S45) — lotto 3: l'entanglement.
L'identità 5 = ζ³·ε²·(ζ−1)⁴ (audit §50) vale in OGNI anello
commutativo in cui ζ è radice di Φ₅: il cofattore esplicito rende la
prova una sola linear_combination. Campagna UNICO, 24 luglio 2026.
-/
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

variable {R : Type*} [CommRing R] {ζ : R}

/-- Da `Φ₅(ζ) = 0` segue `ζ⁵ = 1`.-/
theorem zeta_pow_five (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) :
    ζ ^ 5 = 1 := by
  linear_combination (ζ - 1) * hζ

/-- **Identità di entanglement aureo-ciclotomico** (§50): se `Φ₅(ζ) = 0`
allora `ζ³ · ε² · (ζ−1)⁴ = 5`, con `ε = 1 + ζ + ζ⁴` l'unità aurea.
In `Z[ζ₅]` intreccia il 5, l'unità fondamentale e l'uniformizzante.-/
theorem entanglement (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) :
    ζ ^ 3 * (1 + ζ + ζ ^ 4) ^ 2 * (ζ - 1) ^ 4 = 5 := by
  linear_combination (ζ ^ 11 - 5 * ζ ^ 10 + 10 * ζ ^ 9 - 8 * ζ ^ 8
    - 3 * ζ ^ 7 + 10 * ζ ^ 6 - 4 * ζ ^ 5 - 3 * ζ ^ 4 + ζ ^ 3
    + 5 * ζ - 5) * hζ

end AgrawalCore
