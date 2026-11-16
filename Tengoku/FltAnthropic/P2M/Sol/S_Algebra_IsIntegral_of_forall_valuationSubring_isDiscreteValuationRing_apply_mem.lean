import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_IsIntegral_of_forall_isPrime_isIntegral_quotient_mk
import Tengoku.FltAnthropic.Theorems.Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates
import Tengoku.FltAnthropic.Theorems.Thm_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_adjoin_finset_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_IsIntegral_of_forall_valuationSubring_isDiscreteValuationRing_apply_mem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_IsIntegral_of_forall_valuationSubring_isDiscreteValuationRing_apply_mem

set_option autoImplicit false

universe u v

open IsLocalRing

namespace IntValCrit

/--
@isnad1 id=mem.1h3v.s6.e38696b5c301 from=translated src=- shape=70e49438 vocab=0f5a6cd0
-/
theorem nonunits_subset {E : Type u} [Field E] (V : ValuationSubring E) (z : E) (hz : z ∈ V.nonunits) : z ∈ V := by
  rw [ValuationSubring.mem_nonunits_iff] at hz
  exact (V.valuation_le_one_iff z).mp hz.le

end IntValCrit
