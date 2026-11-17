import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_IharaLemma_IdempotentSplitting
import Tengoku.FltAnthropic.P2M.Sol.S_IharaLemma_IdempotentSplitting_exists_basis_cornerSubmodule_coe_eq_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IharaLemma_IdempotentSplitting_exists_basis_cornerSubmodule_coe_eq_smul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem IharaLemma.IdempotentSplitting.exists_basis_cornerSubmodule_coe_eq_smul
    {B : Type} [CommRing B] (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n)
    {M : Type} [AddCommGroup M] [Module B M] {ι : Type} (b : Module.Basis ι B M) :
    ∃ bj : Module.Basis ι (S.CornerRing i) ↥(IharaLemma.cornerSubmodule (M := M) (S.e i)),
      ∀ k : ι, ((bj k : IharaLemma.cornerSubmodule (M := M) (S.e i)) : M) = S.e i • b k := by exact @_root_.P2MW.S_IharaLemma_IdempotentSplitting_exists_basis_cornerSubmodule_coe_eq_smul.solution B _ S i M _ _ ι b
