import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_isPullback_specMap_awayToAwayRight_awayToAwayLeft

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_isPullback_specMap_awayToAwayRight_awayToAwayLeft.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/--
@isnad1 id=ispullba.0h3v.s10.040361317091 from=translated src=- shape=510e7119 vocab=7af674f3
-/
theorem AlgebraicGeometry.isPullback_specMap_awayToAwayRight_awayToAwayLeft
    {R : Type u} [CommRing R] (f g : R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight f g :
        Localization.Away f →+* Localization.Away (f * g))))
      (Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayLeft g f :
        Localization.Away g →+* Localization.Away (f * g))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away g)))) := by exact @_root_.P2MW.S_AlgebraicGeometry_isPullback_specMap_awayToAwayRight_awayToAwayLeft.solution R _ f g
