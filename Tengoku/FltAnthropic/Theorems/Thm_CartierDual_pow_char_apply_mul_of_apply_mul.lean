import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.P2M.Sol.S_CartierDual_pow_char_apply_mul_of_apply_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CartierDual_pow_char_apply_mul_of_apply_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
open scoped TensorProduct

universe u v

theorem Tengoku.FltAnthropic.CartierDual.pow_char_apply_mul_of_apply_mul
    (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (B : Type v) [CommRing B] [Bialgebra k B] [Module.Free k B] [Module.Finite k B]
    (δ : CartierDual k B)
    (hδ : ∀ a b : B, δ (a * b) = δ a * Coalgebra.counit (R := k) b + Coalgebra.counit (R := k) a * δ b)
    (a b : B) :
    (δ ^ p) (a * b) = (δ ^ p) a * Coalgebra.counit (R := k) b + Coalgebra.counit (R := k) a * (δ ^ p) b := by exact @_root_.P2MW.S_CartierDual_pow_char_apply_mul_of_apply_mul.solution k _ p _ _ B _ _ _ _ δ hδ a b
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
