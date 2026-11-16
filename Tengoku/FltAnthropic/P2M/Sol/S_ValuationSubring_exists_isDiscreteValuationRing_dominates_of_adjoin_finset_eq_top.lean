import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional
import Tengoku.FltAnthropic.Theorems.Thm_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_transcendental_of_adjoin_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_adjoin_finset_eq_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_adjoin_finset_eq_top

set_option autoImplicit false

universe u v

open IsLocalRing

namespace ExtDvrFg

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/--
@isnad1 id=mem.1h3v.s6.e38696b5c301 from=translated src=- shape=70e49438 vocab=0f5a6cd0
-/
theorem nonunits_subset {E : Type v} [Field E] (V : ValuationSubring E) (z : E) (hz : z ∈ V.nonunits) : z ∈ V := by
  rw [ValuationSubring.mem_nonunits_iff] at hz
  exact (V.valuation_le_one_iff z).mp hz.le

end ExtDvrFg
