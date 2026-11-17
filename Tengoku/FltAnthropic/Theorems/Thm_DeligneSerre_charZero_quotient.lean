import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_DeligneSerre_charZero_quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_DeligneSerre_charZero_quotient.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=charzero.1h2v.s7.5bf3ff39cd54 from=translated src=- shape=df44767e vocab=dd3755e0
-/
theorem DeligneSerre.charZero_quotient {T : Type*} [CommRing T] (𝔭 : Ideal T)
  (h𝔭 : ∀ (n : ℤ), (algebraMap ℤ T) n ∈ 𝔭 → n = 0) : CharZero (T ⧸ 𝔭) := by exact @_root_.P2MW.S_DeligneSerre_charZero_quotient.solution T _ 𝔭 h𝔭
