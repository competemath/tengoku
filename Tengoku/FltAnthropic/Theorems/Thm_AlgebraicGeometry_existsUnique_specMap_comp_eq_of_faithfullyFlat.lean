import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.existsUnique_specMap_comp_eq_of_faithfullyFlat
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B B'] [Module.FaithfullyFlat B B']
    {T : Scheme.{u}} (φ' : Spec (CommRingCat.of B') ⟶ T)
    (h : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B' →+* B' ⊗[B] B')) ≫ φ' =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B' →ₐ[B] B' ⊗[B] B').toRingHom) ≫ φ') :
    ∃! φ : Spec (CommRingCat.of B) ⟶ T, Spec.map (CommRingCat.ofHom (algebraMap B B')) ≫ φ = φ' := by exact @_root_.P2MW.S_AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat.solution B B' _ _ _ _ T φ' h
