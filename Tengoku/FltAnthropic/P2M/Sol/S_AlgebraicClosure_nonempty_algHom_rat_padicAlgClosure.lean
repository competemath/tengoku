import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicClosure_nonempty_algHom_rat_padicAlgClosure.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicClosure_nonempty_algHom_rat_padicAlgClosure

theorem solution (p : ℕ) [Fact p.Prime] :
    Nonempty (AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]) := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    (AlgebraicClosure.instIsAlgClosure ℚ).isAlgebraic
  exact ⟨IsAlgClosed.lift⟩
