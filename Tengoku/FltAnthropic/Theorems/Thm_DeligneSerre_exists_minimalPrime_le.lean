import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_DeligneSerre_exists_minimalPrime_le

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_DeligneSerre_exists_minimalPrime_le.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem DeligneSerre.exists_minimalPrime_le {T : Type*} [CommRing T] [Module.Finite ℤ T] [Module.IsTorsionFree ℤ T]
  (𝔪 : Ideal T) (h𝔪 : 𝔪.IsPrime) : ∃ 𝔭 ∈ minimalPrimes T, 𝔭 ≤ 𝔪 ∧ ∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0 := by exact @_root_.P2MW.S_DeligneSerre_exists_minimalPrime_le.solution T _ _ _ 𝔪 h𝔪
