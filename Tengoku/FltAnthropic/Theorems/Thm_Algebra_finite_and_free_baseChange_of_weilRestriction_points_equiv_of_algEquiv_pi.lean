import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem Algebra.finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (H : Type u) [CommRing H] [Algebra B H] [Module.Finite B H] [Module.Free B H]
    (W : Type u) [CommRing W] [Algebra A W]
    (e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (H →ₐ[B] (B ⊗[A] T)))
    (he_nat : ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
      (f : W →ₐ[A] T), e T' (u.comp f) = (Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f))
    (A' : Type u) [CommRing A'] [Algebra A A'] (d : ℕ) (φ : (A' ⊗[A] B) ≃ₐ[A'] (Fin d → A')) :
    Module.Finite A' (A' ⊗[A] W) ∧ Module.Free A' (A' ⊗[A] W) := by exact @_root_.P2MW.S_Algebra_finite_and_free_baseChange_of_weilRestriction_points_equiv_of_algEquiv_pi.solution A _ B _ _ H _ _ _ _ W _ _ e he_nat A' _ _ d φ
