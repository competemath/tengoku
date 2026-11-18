import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_C8Tower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_finrank_fixFld_sylowH.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_finrank_fixFld_sylowH

set_option autoImplicit false

open NumberField LanglandsTunnell

/--
@isnad1 id=eq.0h0v.s5.7801371ecbaa from=translated src=- shape=22b9ad3f vocab=f6e904cd
-/
theorem card_GL2_F3_aux : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
  rw [Matrix.card_GL_field]
  simp [ZMod.card, Fin.prod_univ_two]

/--
@isnad1 id=eq.0h2v.s9.e5fbb6792998 from=translated src=- shape=33570c2d vocab=28fcd795
-/
theorem solution {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
    (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Module.finrank ℚ ↥(fixFld (sylowH e)) = 3 := by
  have h16 : Module.finrank ↥(fixFld (sylowH e)) L = 16 := by
    rw [show fixFld (sylowH e) = IntermediateField.fixedField (sylowH e) from rfl,
      IntermediateField.finrank_fixedField_eq_card, card_sylowH]
  have h48 : Module.finrank ℚ L = 48 := by
    rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr e.toEquiv, card_GL2_F3_aux]
  have htower := Module.finrank_mul_finrank ℚ ↥(fixFld (sylowH e)) L
  rw [h16, h48] at htower
  omega
