import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfKer
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct

universe u v w

/--
@isnad1 id=eq.0h5v.s14.67768d7528bf from=translated src=- shape=ff8ed9a2 vocab=1ec54bef
-/
theorem HopfAlgebra.hopfKer_baseChange_toSubmodule_eq_range_baseChange
    {R : Type u} [CommRing R] (R₁ : Type u) [CommRing R₁] [Algebra R R₁] [Module.Flat R R₁]
    {H : Type v} [CommRing H] [HopfAlgebra R H]
    {H' : Type w} [CommRing H'] [HopfAlgebra R H']
    (qc : H →ₐc[R] H') :
    Subalgebra.toSubmodule
        (HopfAlgebra.hopfKer (Bialgebra.TensorProduct.map (BialgHom.id R₁ R₁) qc :
          R₁ ⊗[R] H →ₐc[R₁] R₁ ⊗[R] H'))
      = LinearMap.range ((HopfAlgebra.hopfKer qc).val.toLinearMap.baseChange R₁) := by exact @_root_.P2MW.S_HopfAlgebra_hopfKer_baseChange_toSubmodule_eq_range_baseChange.solution R _ R₁ _ _ _ H _ _ H' _ _ qc
