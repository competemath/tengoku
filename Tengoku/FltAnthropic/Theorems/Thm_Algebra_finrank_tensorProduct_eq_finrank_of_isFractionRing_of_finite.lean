import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

/--
@isnad1 id=eq.1h6v.s9.0fa435d1d303 from=translated src=- shape=fbf9c16f vocab=055e8970
-/
theorem Algebra.finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {F F' : Type*} [Field F] [Field F'] [Algebra A F] [IsFractionRing A F]
    [Algebra B F'] [IsFractionRing B F'] (φ : F →+* F')
    (hφ : ∀ a : A, algebraMap B F' (algebraMap A B a) = φ (algebraMap A F a)) :
    Module.finrank K (K ⊗[A] B) = @Module.finrank F F' _ _ φ.toAlgebra.toModule := by exact @_root_.P2MW.S_Algebra_finrank_tensorProduct_eq_finrank_of_isFractionRing_of_finite.solution A B _ _ _ _ K _ _ _ F F' _ _ _ _ _ _ φ hφ
