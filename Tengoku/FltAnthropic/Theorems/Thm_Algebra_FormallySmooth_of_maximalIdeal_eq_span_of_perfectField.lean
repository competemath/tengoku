import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open IsLocalRing

theorem Algebra.FormallySmooth.of_maximalIdeal_eq_span_of_perfectField
    (K : Type u) [Field K] [PerfectField K] (𝒪 : Type v) [CommRing 𝒪] [IsLocalRing 𝒪] [IsDomain 𝒪] [IsNoetherianRing 𝒪]
    [Algebra K 𝒪] [Algebra.EssFiniteType K 𝒪]
    (u : 𝒪) (hu0 : u ≠ 0) (hu : maximalIdeal 𝒪 = Ideal.span {u}) :
    Algebra.FormallySmooth K 𝒪 := by exact @_root_.P2MW.S_Algebra_FormallySmooth_of_maximalIdeal_eq_span_of_perfectField.solution K _ _ 𝒪 _ _ _ _ _ _ u hu0 hu
