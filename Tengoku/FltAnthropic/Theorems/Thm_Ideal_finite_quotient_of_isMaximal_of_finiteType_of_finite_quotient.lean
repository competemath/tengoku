import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Ideal_finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Ideal_finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=finite.1h4v.s7.3ae83732e0aa from=translated src=- shape=56bacac2 vocab=5188a0cc
-/
theorem Ideal.finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient
    (A : Type) [CommRing A] (𝔪 : Ideal A) [𝔪.IsMaximal] [Finite (A ⧸ 𝔪)]
    (B : Type) [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (𝔭 : Ideal B) [𝔭.IsMaximal] (h𝔪 : Ideal.map (algebraMap A B) 𝔪 ≤ 𝔭) :
    Finite (B ⧸ 𝔭) := by exact @_root_.P2MW.S_Ideal_finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient.solution A _ 𝔪 _ _ B _ _ _ 𝔭 _ h𝔪
