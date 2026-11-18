import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_isUnit_withConv_algHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_isUnit_withConv_algHom.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=isunit.0h4v.s7.abf4d526d423 from=translated src=- shape=56cb87e0 vocab=6c63fbc7
-/
theorem HopfAlgebra.isUnit_withConv_algHom
    {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [HopfAlgebra R A]
    {L : Type*} [CommSemiring L] [Algebra R L]
    (φ : WithConv (A →ₐ[R] L)) : IsUnit φ := by exact @_root_.P2MW.S_HopfAlgebra_isUnit_withConv_algHom.solution R _ A _ _ L _ _ φ
