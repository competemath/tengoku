import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open TensorProduct in

theorem Module.Flat.exists_ne_zero_flat_localization_tensorProduct
    {A B M : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [Module.Finite B M] :
    ∃ a : A, a ≠ 0 ∧
      Module.Flat A (Localization (Submonoid.powers (algebraMap A B a)) ⊗[B] M) := by exact @_root_.P2MW.S_Module_Flat_exists_ne_zero_flat_localization_tensorProduct.solution A B M _ _ _ _ _ _ _ _ _ _ _
