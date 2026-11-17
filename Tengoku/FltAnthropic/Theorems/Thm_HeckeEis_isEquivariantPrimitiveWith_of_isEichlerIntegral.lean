import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral
import Tengoku.FltAnthropic.P2M.Sol.S_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped MatrixGroups ModularForm

/--
@isnad1 id=isequiva.2h4v.s12.c051f078f093 from=translated src=- shape=cb506931 vocab=4287cb82
-/
theorem HeckeEis.isEquivariantPrimitiveWith_of_isEichlerIntegral
    {n : ℕ} {Γ : Subgroup SL(2, ℤ)} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F)
    (hf : ∀ γ ∈ Γ, (f ∣[((n : ℤ) + 2)] γ) = f) :
    HeckeEis.IsEquivariantPrimitiveWith ((HeckeEis.binaryFormRepSL ℂ n).comp Γ.subtype) F := by exact @_root_.P2MW.S_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral.solution n Γ f F hF hf
