import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_exists_algHom_equiv_pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_exists_algHom_equiv_pi.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

universe u

/--
@isnad1 id=ex.0h3v.s10.65f5dbf26cdf from=translated src=- shape=c40b5a13 vocab=799406be
-/
theorem Algebra.exists_algHom_equiv_pi
    (A : Type u) [CommRing A] (ι : Type) [Finite ι]
    (H : ι → Type u) [∀ i, CommRing (H i)] [∀ i, Algebra A (H i)]
    [∀ i, Module.Finite A (H i)] [∀ i, Module.Free A (H i)] :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra A W),
      Module.Finite A W ∧ Module.Free A W ∧
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (∀ i, H i →ₐ[A] T),
        ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
          (f : W →ₐ[A] T),
          e T' (u.comp f) = fun i => u.comp (e T f i) := by exact @_root_.P2MW.S_Algebra_exists_algHom_equiv_pi.solution A _ ι _ H _ _ _ _
