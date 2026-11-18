import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ProjSpace
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_ProjSpace_awayToSection_mk_mem_span_iff_exists_X_pow_mul_mem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_ProjSpace_awayToSection_mk_mem_span_iff_exists_X_pow_mul_mem.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

/--
@isnad1 id=iff.1h6v.s17.ce9e92cd1ae9 from=translated src=- shape=64ecda23 vocab=6b5c720c
-/
theorem AlgebraicGeometry.ProjSpace.awayToSection_mk_mem_span_iff_exists_X_pow_mul_mem
    (n : ℕ) (A : Type) [CommRing A] (I : Ideal (MvPolynomial (Fin (n + 1)) A))
    (i : Fin (n + 1)) (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d) :
    (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
      (HomogeneousLocalization.mk
        { deg := d
          num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
          den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
          den_mem := ⟨d, rfl⟩ }) ∈
        Ideal.span { s | ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) A) (hF : F.IsHomogeneous d),
          F ∈ I ∧
          s = (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (X i))
              (HomogeneousLocalization.mk
                { deg := d
                  num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                  den := ⟨X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr (MvPolynomial.isHomogeneous_X_pow i d)⟩
                  den_mem := ⟨d, rfl⟩ }) } ↔
      ∃ N : ℕ, X i ^ N * F ∈ I := by exact @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_awayToSection_mk_mem_span_iff_exists_X_pow_mul_mem.solution n A _ I i d F hF
