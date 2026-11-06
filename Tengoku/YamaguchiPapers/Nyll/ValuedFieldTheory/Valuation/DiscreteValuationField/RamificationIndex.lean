/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.NatCastValuation
import Tengoku.Seed.Algebra.Order.GroupWithZero.Canonical

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The value of the residue characteristic

For an integer-valued valuation in mixed characteristic, the positive exponent
of the residue prime gives the denominator estimates for logarithm and
exponential series. Neither completeness nor residue-field finiteness is needed.
-/

namespace Valuation

universe u

variable {K : Type u} [Field K]

/-- The nonnegative exponent of the value of a specified residue prime.-/
def residueRamificationIndex (v : Valuation K (WithZero (Multiplicative ℤ)))
    (p : ℕ) : ℕ :=
  (-WithZero.log (v (p : K))).toNat

/-- A residue characteristic has value strictly less than one.
@isnad1 id=lt.0h3v.s8.68430ef487ce from=translated src=- shape=a7f50450 vocab=b487f5c3
-/
theorem natCast_residueChar_lt_one
    (v : Valuation K (WithZero (Multiplicative ℤ))) (p : ℕ)
    [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    v (p : K) < 1 := by
  have hres : IsLocalRing.residue v.valuationSubring (p : v.valuationSubring) = 0 := by
    rw [map_natCast, CharP.cast_eq_zero]
  have hmem := (IsLocalRing.residue_eq_zero_iff (p : v.valuationSubring)).mp hres
  have hlt := (Valuation.mem_maximalIdeal_iff (v := v)).mp hmem
  exact_mod_cast hlt

end Valuation
