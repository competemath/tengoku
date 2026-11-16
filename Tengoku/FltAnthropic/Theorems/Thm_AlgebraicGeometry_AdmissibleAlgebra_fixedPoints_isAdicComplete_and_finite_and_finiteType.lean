import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgebraicGeometry_AdmissibleAlgebra_fixedPoints_isAdicComplete_and_finite_and_finiteType

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgebraicGeometry_AdmissibleAlgebra_fixedPoints_isAdicComplete_and_finite_and_finiteType.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=and.6h4v.s12.0d5e6fc9ad1e from=translated src=- shape=a6870bb9 vocab=7b4e7146
-/
theorem AlgebraicGeometry.AdmissibleAlgebra.fixedPoints_isAdicComplete_and_finite_and_finiteType
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (R : Type) [CommRing R] [Algebra 𝒪 R]
    (hRc : IsAdicComplete (Ideal.span {algebraMap 𝒪 R π}) R)
    (hRtf : ∀ x : R, algebraMap 𝒪 R π * x = 0 → x = 0)
    (hRft : Algebra.FiniteType 𝒪 (R ⧸ Ideal.span {algebraMap 𝒪 R π}))
    (G : Type) [Group G] [Finite G] [MulSemiringAction G R] [SMulCommClass G 𝒪 R] :
    IsAdicComplete (Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π}) ↥(FixedPoints.subalgebra 𝒪 R G) ∧
    Module.Finite ↥(FixedPoints.subalgebra 𝒪 R G) R ∧
    Algebra.FiniteType 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G) ⧸ Ideal.span {algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π}) ∧
    (∀ k : ℕ, ∀ x : ↥(FixedPoints.subalgebra 𝒪 R G),
      (x : R) ∈ Ideal.span {(algebraMap 𝒪 R π) ^ k} → x ∈ Ideal.span {(algebraMap 𝒪 (↥(FixedPoints.subalgebra 𝒪 R G)) π) ^ k}) := by exact @_root_.P2MW.S_AlgebraicGeometry_AdmissibleAlgebra_fixedPoints_isAdicComplete_and_finite_and_finiteType.solution 𝒪 _ _ hdvr π hπ hcomplete R _ _ hRc hRtf hRft G _ _ _ _
