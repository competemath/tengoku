import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_isUnramifiedAt_iff_isUnramifiedAt_fiber

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_isUnramifiedAt_iff_isUnramifiedAt_fiber.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

/--
@isnad1 id=iff.1h5v.s11.3554564504d7 from=translated src=- shape=bb1e47e2 vocab=ac036554
-/
theorem Algebra.isUnramifiedAt_iff_isUnramifiedAt_fiber
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Algebra.EssFiniteType R A]
    (P : Ideal R) [P.IsPrime] (Q : Ideal A) [Q.IsPrime] [Q.LiesOver P]
    (Q' : Ideal (P.Fiber A)) [Q'.IsPrime]
    (hQ' : Q = Q'.comap Algebra.TensorProduct.includeRight.toRingHom) :
    Algebra.IsUnramifiedAt R Q ↔ Algebra.IsUnramifiedAt P.ResidueField Q' := by exact @_root_.P2MW.S_Algebra_isUnramifiedAt_iff_isUnramifiedAt_fiber.solution R A _ _ _ _ P _ Q _ _ Q' _ hQ'
