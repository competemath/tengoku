import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.P2M.Sol.S_CartierDual_exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CartierDual_exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

universe u v w

open IsLocalRing
open scoped TensorProduct

/--
@isnad1 id=ex.0h4v.s10.1d10fc6fe9e7 from=translated src=- shape=9527601b vocab=d4e96c70
-/
theorem Tengoku.FltAnthropic.CartierDual.exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra
    {S : Type u} [CommRing S] {B : Type v} [CommRing B] [Bialgebra S B] [Module.Finite S B] [Module.Free S B]
    (M : Type w) [Fintype M] [DecidableEq M]
    (f : B →ₗc[S] AddMonoidAlgebra S M) :
    ∃ e : M → CartierDual S B,
      (∀ m, IsIdempotentElem (e m)) ∧ (∀ a b, a ≠ b → e a * e b = 0) ∧ ∑ m, e m = 1 ∧
      ∀ b : B, f b = ∑ m, AddMonoidAlgebra.single m (e m b) := by exact @_root_.P2MW.S_CartierDual_exists_isIdempotentElem_eq_sum_single_of_coalgHom_addMonoidAlgebra.solution S _ B _ _ _ _ M _ _ f
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
