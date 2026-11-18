import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped Topology

/--
@isnad1 id=ex.1h2v.s8.656603db3584 from=translated src=- shape=bb115a64 vocab=8a286d8c
-/
theorem ModularCurve.exists_meromorphic_logDeriv_eq_of_int_residue
    (m : ℂ → ℤ) (ω : ℂ → ℂ)
    (hres : ∀ a : ℂ, 0 < a.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      (∀ᶠ z in 𝓝[≠] a, ω z = (m a : ℂ) / (z - a) + g z) ∧ (m a = 0 → ω a = g a)) :
    ∃ G : ℂ → ℂ, ∀ a : ℂ, 0 < a.im →
      MeromorphicAt G a ∧ meromorphicOrderAt G a = (m a : WithTop ℤ) ∧
      (m a ≠ 0 → G a = 0) ∧
      (m a = 0 → AnalyticAt ℂ G a ∧ G a ≠ 0 ∧ HasDerivAt G (ω a * G a) a) := by exact @_root_.P2MW.S_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue.solution m ω hres
