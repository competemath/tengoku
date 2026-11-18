import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u

/--
@isnad1 id=ex.3h4v.s12.6fbc4e01ce54 from=translated src=- shape=e11eeb2f vocab=45f69b3b
-/
theorem Module.exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG)
    (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
    (τ : ∀ k, E (k + 1) →ₗ[R] E k) (hτs : ∀ k, Function.Surjective (τ k))
    (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1)))) :
    ∃ L : Submodule R (∀ k, E k),
      (∀ e : ∀ k, E k, e ∈ L ↔ ∀ k, τ k (e (k + 1)) = e k) ∧
      (∀ k, Function.Surjective ((LinearMap.proj k).comp L.subtype : L →ₗ[R] E k)) ∧
      (∀ k, LinearMap.ker ((LinearMap.proj k).comp L.subtype : L →ₗ[R] E k) =
        I ^ (k + 1) • (⊤ : Submodule R L)) := by exact @_root_.P2MW.S_Module_exists_submodule_pi_forall_surjective_ker_eq_pow_smul_top_of_adic_system.solution R _ I hI E _ _ τ hτs hτk
