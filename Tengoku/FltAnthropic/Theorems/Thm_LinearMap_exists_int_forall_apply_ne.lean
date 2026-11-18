import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LinearMap_exists_int_forall_apply_ne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LinearMap_exists_int_forall_apply_ne.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.1h6v.s9.3c4ba9ec40f0 from=translated src=- shape=473191ef vocab=c5dd35eb
-/
theorem LinearMap.exists_int_forall_apply_ne {K : Type*} [Field K] [CharZero K] {r : ℕ} {ι : Type*}
    (S : Finset ι) (f : ι → (Fin r → K) →ₗ[K] K) (a : ι → K) (hf : ∀ j ∈ S, f j ≠ 0) :
    ∃ c : Fin r → ℤ, ∀ j ∈ S, f j (fun i => (c i : K)) ≠ a j := by exact @_root_.P2MW.S_LinearMap_exists_int_forall_apply_ne.solution K _ _ r ι S f a hf
