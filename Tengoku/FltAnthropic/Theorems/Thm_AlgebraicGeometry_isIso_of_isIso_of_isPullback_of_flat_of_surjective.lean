import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_of_flat_of_surjective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_isIso_of_isIso_of_isPullback_of_flat_of_surjective.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isIso_of_isPullback_of_flat_of_surjective
    {S S' A B A' B' : Scheme.{0}} (b : S' ⟶ S) [Flat b] [Surjective b] [QuasiCompact b]
    (pA : A ⟶ S) (pB : B ⟶ S) (φ : A ⟶ B) (hφ : φ ≫ pB = pA)
    (pA' : A' ⟶ S') (pB' : B' ⟶ S') (φ' : A' ⟶ B') (hφ' : φ' ≫ pB' = pA')
    (gA : A' ⟶ A) (gB : B' ⟶ B) (sqA : IsPullback gA pA' pA b) (sqB : IsPullback gB pB' pB b)
    (comm : φ' ≫ gB = gA ≫ φ) (hiso : IsIso φ') :
    IsIso φ := by exact @_root_.P2MW.S_AlgebraicGeometry_isIso_of_isIso_of_isPullback_of_flat_of_surjective.solution S S' A B A' B' b _ _ _ pA pB φ hφ pA' pB' φ' hφ' gA gB sqA sqB comm hiso
