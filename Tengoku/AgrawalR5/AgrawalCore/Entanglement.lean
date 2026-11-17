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

/-- Da `Φ₅(ζ) = 0` segue `ζ⁵ = 1`.
@isnad1 id=eq.1h2v.s7.da257ec9e251 from=translated src=- shape=261398cf vocab=fd68a3c8
-/
theorem zeta_pow_five (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) :
    ζ ^ 5 = 1 := by
  linear_combination (ζ - 1) * hζ

/-- **Identità di entanglement aureo-ciclotomico** (§50): se `Φ₅(ζ) = 0`
allora `ζ³ · ε² · (ζ−1)⁴ = 5`, con `ε = 1 + ζ + ζ⁴` l'unità aurea.
In `Z[ζ₅]` intreccia il 5, l'unità fondamentale e l'uniformizzante.
@isnad1 id=eq.1h2v.s8.4b5ff6601a42 from=translated src=- shape=181ce340 vocab=9c1cdc1d
-/
theorem entanglement (hζ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0) :
    ζ ^ 3 * (1 + ζ + ζ ^ 4) ^ 2 * (ζ - 1) ^ 4 = 5 := by
  linear_combination (ζ ^ 11 - 5 * ζ ^ 10 + 10 * ζ ^ 9 - 8 * ζ ^ 8
    - 3 * ζ ^ 7 + 10 * ζ ^ 6 - 4 * ζ ^ 5 - 3 * ζ ^ 4 + ζ ^ 3
    + 5 * ζ - 5) * hζ

end AgrawalCore
