import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_EisensteinSeries_WeierstrassZeta
import Tengoku.FltAnthropic.P2M.Sol.S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped Real

/--
@isnad1 id=hassum.1h2v.s8.3a60789e3f6b from=translated src=- shape=861517a1 vocab=86df799d
-/
theorem EisensteinSeries.hasSum_weierstrassZeta_sub_mul_G2 (τ : UpperHalfPlane) (z : ℂ)
    (hz : ∀ v : Fin 2 → ℤ, z ≠ (v 0 : ℂ) * τ + v 1) :
    HasSum (fun m : ℕ => π * Complex.cot (π * (z + ((m : ℂ) + 1) * τ)) +
        π * Complex.cot (π * (z - ((m : ℂ) + 1) * τ)))
      (EisensteinSeries.weierstrassZeta τ z - z * EisensteinSeries.G2 τ -
        π * Complex.cot (π * z)) := by exact @_root_.P2MW.S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2.solution τ z hz
