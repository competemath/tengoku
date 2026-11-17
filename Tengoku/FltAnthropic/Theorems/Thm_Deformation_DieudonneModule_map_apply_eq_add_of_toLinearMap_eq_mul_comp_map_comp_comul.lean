import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittHomColimit
import Tengoku.FltAnthropic.P2M.Sol.S_Deformation_DieudonneModule_map_apply_eq_add_of_toLinearMap_eq_mul_comp_map_comp_comul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Deformation_DieudonneModule_map_apply_eq_add_of_toLinearMap_eq_mul_comp_map_comp_comul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open scoped TensorProduct in

theorem Deformation.DieudonneModule.map_apply_eq_add_of_toLinearMap_eq_mul_comp_map_comp_comul
    (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime]
    {A : Type} [CommRing A] [Bialgebra R A] {B : Type} [CommRing B] [Bialgebra R B]
    (f g h : A →ₐc[R] B)
    (hh : (h : A →ₐ[R] B).toLinearMap =
      LinearMap.mul' R B ∘ₗ TensorProduct.map (f : A →ₐ[R] B).toLinearMap (g : A →ₐ[R] B).toLinearMap ∘ₗ
        Coalgebra.comul (R := R) (A := A))
    (x : Deformation.DieudonneModule R p A) :
    Deformation.DieudonneModule.map R p h x =
      Deformation.DieudonneModule.map R p f x + Deformation.DieudonneModule.map R p g x := by exact @_root_.P2MW.S_Deformation_DieudonneModule_map_apply_eq_add_of_toLinearMap_eq_mul_comp_map_comp_comul.solution R _ p _ A _ _ B _ _ f g h hh x
