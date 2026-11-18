import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_ContinuousUnramified
import Tengoku.FltAnthropic.Definitions.Def_DualSelmer_ExtConditions
import Tengoku.FltAnthropic.Definitions.Def_ExtCitation_KummerBridge
import Tengoku.FltAnthropic.Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_exists_normal_isUnramifiedOutside_of_le.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_exists_normal_isUnramifiedOutside_of_le

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem solution
    (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), F ≤ L ∧ L.IsUnramifiedOutside S ∧ Normal ℚ L := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  exact ⟨IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ), IntermediateField.le_normalClosure F, hF.normalClosure, normalClosure.normal ℚ F (AlgebraicClosure ℚ)⟩
