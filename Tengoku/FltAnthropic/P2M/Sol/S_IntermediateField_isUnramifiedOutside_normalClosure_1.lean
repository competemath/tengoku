import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_ContinuousUnramified
import Tengoku.FltAnthropic.Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_isUnramifiedOutside_normalClosure_1.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_isUnramifiedOutside_normalClosure_1
set_option autoImplicit false

open IntermediateField in

/--
@isnad1 id=and.1h2v.s12.e7598440a6e1 from=translated src=- shape=5d59c262 vocab=f9651fad
-/
theorem solution
    (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hF : F.IsUnramifiedOutside S) :
    F ≤ (normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ ∧
    FiniteDimensional ℚ ↥(normalClosure ℚ ↥F (AlgebraicClosure ℚ)) ∧
    IsGalois ℚ ↥(normalClosure ℚ ↥F (AlgebraicClosure ℚ)) ∧
    ((normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ).IsUnramifiedOutside S := by
  haveI : FiniteDimensional ℚ ↥F := hF.1
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by convert AlgebraicClosure.instIsAlgClosure ℚ; rfl; rfl
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ _
  have hle : F ≤ (normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ := fun x hx =>
    (IntermediateField.mem_restrictScalars ℚ).2 (IntermediateField.le_normalClosure F hx)
  have hle' : (normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ ≤ normalClosure ℚ ↥F (AlgebraicClosure ℚ) :=
    fun x hx => (IntermediateField.mem_restrictScalars ℚ).1 hx
  exact ⟨hle, normalClosure.is_finiteDimensional ℚ ↥F (AlgebraicClosure ℚ), IsGalois.normalClosure ℚ ↥F (AlgebraicClosure ℚ),
    hF.normalClosure.of_le hle'⟩
