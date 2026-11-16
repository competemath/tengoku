import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_norm_one_tmul_eq_algebraMap_norm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_norm_one_tmul_eq_algebraMap_norm.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v w

open scoped TensorProduct

/--
@isnad1 id=eq.0h4v.s9.2f3702e54c92 from=translated src=- shape=1b88840c vocab=c36cb0c2
-/
theorem Algebra.norm_one_tmul_eq_algebraMap_norm
    {K : Type u} [CommRing K] {L : Type v} [Ring L] [Algebra K L] [Module.Free K L] [Module.Finite K L]
    (K' : Type w) [CommRing K'] [Algebra K K'] (x : L) :
    Algebra.norm K' ((1 : K') ⊗ₜ[K] x : K' ⊗[K] L) = algebraMap K K' (Algebra.norm K x) := by exact @_root_.P2MW.S_Algebra_norm_one_tmul_eq_algebraMap_norm.solution K _ L _ _ _ _ K' _ _ x
