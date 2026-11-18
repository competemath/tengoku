import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow
import Tengoku.FltAnthropic.Theorems.Thm_Nat_macaulayPow_lt_macaulayPow_of_lt
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_ProjSpace
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Tengoku.FltAnthropic.Definitions.Def_Nat_MacaulayPow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq

set_option autoImplicit false
open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.HilbertFunctor
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GotzmannB29

theorem lt_of_lt {n : ℕ} {K : Type} [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (H : ℕ → ℕ) (g : ℕ) (hg : 1 ≤ g) (hH : ∀ e, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e))
    (d : ℕ) (hd : g ≤ d) (hlt : Module.finrank K (piece J d) < H d) :
    ∀ e, d ≤ e → Module.finrank K (piece J e) < H e := by
  intro e hde
  induction e with
  | zero =>
    obtain rfl : d = 0 := by omega
    exact hlt
  | succ e ih =>
    rcases Nat.lt_or_ge e d with h | h
    · obtain rfl : d = e + 1 := by omega
      exact hlt
    · calc Module.finrank K (piece J (e + 1)) ≤ Nat.macaulayPow e (Module.finrank K (piece J e)) :=
            MvPolynomial.finrank_piece_succ_le_macaulayPow n e (by omega) K J hJ
        _ < Nat.macaulayPow e (H e) := Nat.macaulayPow_lt_macaulayPow_of_lt (by omega) (ih h)
        _ = H (e + 1) := (hH e (by omega)).symm

theorem le_finrank_piece {n : ℕ} {K : Type} [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (H : ℕ → ℕ) (g : ℕ) (hg : 1 ≤ g) (hH : ∀ e, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e))
    (hev : ∃ D₀ : ℕ, ∀ e, D₀ ≤ e → Module.finrank K (piece J e) = H e)
    (d : ℕ) (hd : g ≤ d) : H d ≤ Module.finrank K (piece J d) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨D₀, hD₀⟩ := hev
  have := lt_of_lt J hJ H g hg hH d hd hlt (max d D₀) (le_max_left _ _)
  rw [hD₀ _ (le_max_right _ _)] at this
  exact lt_irrefl _ this

end GotzmannB29

open GotzmannB29 in
theorem solution
    (n g : ℕ) (hg : 1 ≤ g) (H : ℕ → ℕ)
    (hH : ∀ e : ℕ, g ≤ e → H (e + 1) = Nat.macaulayPow e (H e))
    (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J)
    (hev : ∃ D : ℕ, ∀ e : ℕ, D ≤ e → Module.finrank K (piece J e) = H e) :
    ∀ d : ℕ, g ≤ d → H d ≤ Module.finrank K (piece J d) := by
  intro d hd
  exact GotzmannB29.le_finrank_piece J hJ H g hg hH hev d hd
