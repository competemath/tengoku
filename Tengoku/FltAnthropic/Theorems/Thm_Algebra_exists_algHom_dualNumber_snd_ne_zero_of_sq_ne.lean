import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_exists_algHom_dualNumber_snd_ne_zero_of_sq_ne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_exists_algHom_dualNumber_snd_ne_zero_of_sq_ne.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem Algebra.exists_algHom_dualNumber_snd_ne_zero_of_sq_ne
    (Ω : Type*) [Field Ω] (S : Type*) [CommRing S] [Algebra Ω S]
    (𝔪 : Ideal S) [𝔪.IsMaximal] (hres : Function.Surjective (algebraMap Ω (S ⧸ 𝔪)))
    (hne : 𝔪 ^ 2 ≠ 𝔪) :
    ∃ (φ : S →ₐ[Ω] DualNumber Ω) (s : S), TrivSqZeroExt.snd (φ s) ≠ 0 := by exact @_root_.P2MW.S_Algebra_exists_algHom_dualNumber_snd_ne_zero_of_sq_ne.solution Ω _ S _ _ 𝔪 _ hres hne
