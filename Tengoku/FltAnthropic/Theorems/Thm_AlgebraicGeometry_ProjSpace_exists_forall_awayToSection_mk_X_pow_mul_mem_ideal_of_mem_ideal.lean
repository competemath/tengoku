import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ProjSpace
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

/--
@isnad1 id=ex.2h7v.s18.d658b52fea8b from=translated src=- shape=eb1cc37b vocab=6b47a90d
-/
theorem AlgebraicGeometry.ProjSpace.exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal
    (n : ℕ) (A : Type) [CommRing A] (𝓘 : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)).IdealSheafData)
    (i : Fin (n + 1)) (a : ℕ) (H : MvPolynomial (Fin (n + 1)) A) (hH : H.IsHomogeneous a)
    (hmem : (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
      (HomogeneousLocalization.mk
        { deg := a
          num := ⟨H, (MvPolynomial.mem_homogeneousSubmodule a H).mpr hH⟩
          den := ⟨X i ^ a, (MvPolynomial.mem_homogeneousSubmodule a _).mpr (MvPolynomial.isHomogeneous_X_pow i a)⟩
          den_mem := ⟨a, rfl⟩ }) ∈
      𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i) (ProjSpace.X_mem_one A n i) one_pos⟩)
    (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∀ j : Fin (n + 1),
      (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j))
        (HomogeneousLocalization.mk
          { deg := N + a
            num := ⟨X i ^ N * H, (MvPolynomial.mem_homogeneousSubmodule (N + a) _).mpr ((MvPolynomial.isHomogeneous_X_pow i N).mul hH)⟩
            den := ⟨X j ^ (N + a), (MvPolynomial.mem_homogeneousSubmodule (N + a) _).mpr (MvPolynomial.isHomogeneous_X_pow j (N + a))⟩
            den_mem := ⟨N + a, rfl⟩ }) ∈
        𝓘.ideal ⟨Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j),
          Proj.isAffineOpen_basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X j) (ProjSpace.X_mem_one A n j) one_pos⟩ := by exact @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_forall_awayToSection_mk_X_pow_mul_mem_ideal_of_mem_ideal.solution n A _ 𝓘 i a H hH hmem N₀
