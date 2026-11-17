import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AlgHom_liftEquiv_symm_withConv_mul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AlgHom_liftEquiv_symm_withConv_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open TensorProduct in
theorem AlgHom.liftEquiv_symm_withConv_mul
    (R : Type*) [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (A : Type*) [CommRing A] [Bialgebra R A]
    (B : Type*) [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f g : WithConv (S ⊗[R] A →ₐ[S] B)) :
    WithConv.toConv ((AlgHom.liftEquiv R S A B).symm (f * g).ofConv)
    = WithConv.toConv ((AlgHom.liftEquiv R S A B).symm f.ofConv)
      * WithConv.toConv ((AlgHom.liftEquiv R S A B).symm g.ofConv) := by exact @_root_.P2MW.S_AlgHom_liftEquiv_symm_withConv_mul.solution R _ S _ _ A _ _ B _ _ _ _ f g
