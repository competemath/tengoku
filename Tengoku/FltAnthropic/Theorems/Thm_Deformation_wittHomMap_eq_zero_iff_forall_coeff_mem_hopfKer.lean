import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfKer
import Tengoku.FltAnthropic.P2M.Sol.S_Deformation_wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Deformation_wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v w

/--
@isnad1 id=iff.0h7v.s11.b4b4dc74993e from=translated src=- shape=086a873f vocab=677485d6
-/
theorem Deformation.wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A] {B : Type w} [CommRing B] [Bialgebra R B]
    (π : A →ₐc[R] B) (x : Deformation.wittHom R p n A) :
    Deformation.wittHomMap p n π x = 0 ↔
      ∀ i, (x : TruncatedWittVector p n A).coeff i ∈ HopfAlgebra.hopfKer π := by exact @_root_.P2MW.S_Deformation_wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer.solution R _ p _ n A _ _ B _ _ π x
