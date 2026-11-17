import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

theorem AlgebraicGeometry.closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top
    {S : Scheme.{u}} [IsAffine S] {A B : CommRingCat.{u}} (a : Spec A ⟶ S) (b : Spec B ⟶ S) :
    Subring.closure
      (Set.range (pullback.fst a b).appTop ∪ Set.range (pullback.snd a b).appTop) = ⊤ := by exact @_root_.P2MW.S_AlgebraicGeometry_closure_range_pullback_fst_appTop_union_range_snd_appTop_eq_top.solution S _ A B a b
