import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_apply_eq_self_of_pow_apply_eq_self_of_wild

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_apply_eq_self_of_pow_apply_eq_self_of_wild.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v
/--
@isnad1 id=eq.4h7v.s9.f25a6a31d98b from=translated src=- shape=d461f6e3 vocab=c13df3f6
-/
theorem ValuationSubring.apply_eq_self_of_pow_apply_eq_self_of_wild {K : Type u} {L : Type v} [Field K] [Field L]
    [Algebra K L] (A : ValuationSubring L) {q : ℕ} (hA : ((q : ℕ) : L) ∈ A.nonunits) {σ : L ≃ₐ[K] L}
    (hwild : ∀ z : L, z ≠ 0 → σ z * z⁻¹ - 1 ∈ A.nonunits) {m : ℕ} (hm : m.Coprime q) {y : L}
    (h : (σ ^ m) y = y) : σ y = y := by exact @_root_.P2MW.S_ValuationSubring_apply_eq_self_of_pow_apply_eq_self_of_wild.solution K L _ _ _ A q hA σ hwild m hm y h
