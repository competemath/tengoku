import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

/--
@isnad1 id=bijectiv.1h5v.s14.cb7b110a104c from=translated src=- shape=38f0431d vocab=c0645745
-/
theorem AdicCompletion.bijective_of_forall_val_apply_eq_mk_apply
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module.Finite A M] [Module.Finite A N]
    (θ : AdicCompletion I (M →ₗ[A] N) →ₗ[A] (M →ₗ[A] AdicCompletion I N))
    (hθ : ∀ (x : AdicCompletion I (M →ₗ[A] N)) (n : ℕ) (g : M →ₗ[A] N),
      Submodule.Quotient.mk g = x.val n →
        ∀ m : M, (θ x m).val n = Submodule.Quotient.mk (g m)) :
    Function.Bijective θ := by exact @_root_.P2MW.S_AdicCompletion_bijective_of_forall_val_apply_eq_mk_apply.solution A _ _ I M N _ _ _ _ _ _ θ hθ
