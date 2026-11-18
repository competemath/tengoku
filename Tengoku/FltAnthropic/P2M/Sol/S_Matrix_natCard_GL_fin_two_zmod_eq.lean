import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_natCard_GL_fin_two_zmod_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_natCard_GL_fin_two_zmod_eq

set_option autoImplicit false

/--
@isnad1 id=eq.0h1v.s6.a06e67ade29b from=translated src=- shape=2718adb9 vocab=ac632517
-/
theorem solution (p : ℕ) [Fact p.Prime] :
    Nat.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]
