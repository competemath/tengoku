import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

/--
@isnad1 id=isaffine.2h7v.s8.3e3aab04c1ea from=translated src=- shape=33fe2cde vocab=d2bf0f42
-/
theorem AlgebraicGeometry.isAffineOpen_pullback_fst_preimage_inf_snd_preimage
    {X Y S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by exact @_root_.P2MW.S_AlgebraicGeometry_isAffineOpen_pullback_fst_preimage_inf_snd_preimage.solution X Y S _ f g U hU V hV
