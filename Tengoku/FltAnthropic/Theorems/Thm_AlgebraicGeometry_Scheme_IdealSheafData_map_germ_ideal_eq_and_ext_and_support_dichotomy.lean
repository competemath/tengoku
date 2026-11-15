import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_eq_and_ext_and_support_dichotomy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_eq_and_ext_and_support_dichotomy.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Scheme.IdealSheafData.map_germ_ideal_eq_and_ext_and_support_dichotomy {X : Scheme.{u}} :
    (∀ (I : X.IdealSheafData) (x : X) (V W : X.affineOpens) (hV : x ∈ (V : X.Opens)) (hW : x ∈ (W : X.Opens)),
      Ideal.map (X.presheaf.germ (V : X.Opens) x hV).hom (I.ideal V) =
        Ideal.map (X.presheaf.germ (W : X.Opens) x hW).hom (I.ideal W)) ∧
    (∀ (I J : X.IdealSheafData),
      (∀ x : X, ∃ (U : X.affineOpens) (hx : x ∈ (U : X.Opens)),
        Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom (I.ideal U) =
          Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom (J.ideal U)) → I = J) ∧
    (∀ (I : X.IdealSheafData) (U : X.affineOpens) (x : X) (hx : x ∈ (U : X.Opens)),
      (x ∉ (I.support : Set X) → Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom (I.ideal U) = ⊤) ∧
      (x ∈ (I.support : Set X) →
        Ideal.map (X.presheaf.germ (U : X.Opens) x hx).hom (I.ideal U) ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x))) := by exact @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_map_germ_ideal_eq_and_ext_and_support_dichotomy.solution X
