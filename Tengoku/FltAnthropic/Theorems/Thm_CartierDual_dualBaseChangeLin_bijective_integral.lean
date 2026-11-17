import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CharacterClosure
import Tengoku.FltAnthropic.P2M.Sol.S_CartierDual_dualBaseChangeLin_bijective_integral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CartierDual_dualBaseChangeLin_bijective_integral.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

open scoped TensorProduct

theorem Tengoku.FltAnthropic.CartierDual.dualBaseChangeLin_bijective_integral.{u, v, w}
    (O : Type u) [CommRing O] (O' : Type v) [CommRing O'] [Algebra O O']
    (A : Type w) [CommRing A] [HopfAlgebra O A] [Module.Finite O A] [Module.Free O A] :
    Function.Bijective (CartierDual.dualBaseChangeLin O O' A) ∧
    CartierDual.dualBaseChangeLin O O' A 1 = 1 ∧
    (∀ x y : O' ⊗[O] CartierDual O A,
        CartierDual.dualBaseChangeLin O O' A (x * y)
          = CartierDual.dualBaseChangeLin O O' A x * CartierDual.dualBaseChangeLin O O' A y) ∧
    (∀ w : O' ⊗[O] CartierDual O A,
        TensorProduct.map (CartierDual.dualBaseChangeLin O O' A) (CartierDual.dualBaseChangeLin O O' A)
            (Coalgebra.comul (R := O') w)
          = Coalgebra.comul (R := O') (CartierDual.dualBaseChangeLin O O' A w)) ∧
    (∀ (g : CartierDual O A) (x : O' ⊗[O] A),
        CartierDual.dualBaseChangeLin O O' A ((1 : O') ⊗ₜ[O] HopfAlgebraStruct.antipode (R := O) g) x
          = CartierDual.dualBaseChangeLin O O' A ((1 : O') ⊗ₜ[O] g) (HopfAlgebraStruct.antipode (R := O') x)) := by exact @_root_.P2MW.S_CartierDual_dualBaseChangeLin_bijective_integral.solution O _ O' _ _ A _ _ _ _
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
