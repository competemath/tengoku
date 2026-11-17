import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

theorem Algebra.eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Type u} [CommRing B] [Algebra R B] [NoZeroSMulDivisors R B]
    [IsReduced (TensorProduct R K B)] [Module.Finite K (TensorProduct R K B)]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
    (b : B) (hb : ∀ φ : B →ₐ[R] Ω, φ b = 0) : b = 0 := by exact @_root_.P2MW.S_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct.solution R _ _ K _ _ _ B _ _ _ _ _ Ω _ _ _ _ _ b hb
