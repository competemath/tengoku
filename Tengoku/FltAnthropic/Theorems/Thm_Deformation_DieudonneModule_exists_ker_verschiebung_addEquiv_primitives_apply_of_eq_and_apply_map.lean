import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_ModpRealization
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittHomColimit
import Tengoku.FltAnthropic.P2M.Sol.S_Deformation_DieudonneModule_exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Deformation_DieudonneModule_exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

/--
@isnad1 id=ex.0h3v.s15.dd366544d57a from=translated src=- shape=b10e4a7a vocab=5a4eaa08
-/
theorem Deformation.DieudonneModule.exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map
    (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type*) [CommRing A] [HopfAlgebra k A] :
    ∃ e : (Deformation.DieudonneModule.verschiebung k p A).ker ≃+ ↥(primitives k A),
      (∀ (x : Deformation.wittHom k p 1 A)
          (hx : Deformation.DieudonneModule.of k p A 1 x ∈ (Deformation.DieudonneModule.verschiebung k p A).ker),
        (e ⟨Deformation.DieudonneModule.of k p A 1 x, hx⟩ : A) = (x : TruncatedWittVector p 1 A).coeff 0) ∧
      ∀ (ψ : A →ₐc[k] A) (z : (Deformation.DieudonneModule.verschiebung k p A).ker)
        (hz : Deformation.DieudonneModule.map k p ψ z ∈ (Deformation.DieudonneModule.verschiebung k p A).ker),
        (e ⟨Deformation.DieudonneModule.map k p ψ z, hz⟩ : A) = ψ (e z : A) := by exact @_root_.P2MW.S_Deformation_DieudonneModule_exists_ker_verschiebung_addEquiv_primitives_apply_of_eq_and_apply_map.solution k _ p _ _ A _ _
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
