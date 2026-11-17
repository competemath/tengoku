import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_finrank_eq_finsum_length_stalk_of_isFinite_of_isAlgClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_finrank_eq_finsum_length_stalk_of_isFinite_of_isAlgClosed.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=eq.0h4v.s11.ce6afdf0c8cc from=translated src=- shape=101f4c95 vocab=1c46691e
-/
theorem AlgebraicGeometry.finrank_eq_finsum_length_stalk_of_isFinite_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f]
    (s : ↥(Spec (CommRingCat.of k))) :
    (f.finrank s : ℕ∞) =
      ∑ᶠ x : {x : Spec (CommRingCat.of k) ⟶ X // x ≫ f = 𝟙 (Spec (CommRingCat.of k))},
        Module.length (X.presheaf.stalk (x.1.base (IsLocalRing.closedPoint k)))
          (X.presheaf.stalk (x.1.base (IsLocalRing.closedPoint k))) := by exact @_root_.P2MW.S_AlgebraicGeometry_finrank_eq_finsum_length_stalk_of_isFinite_of_isAlgClosed.solution k _ _ X f _ s
