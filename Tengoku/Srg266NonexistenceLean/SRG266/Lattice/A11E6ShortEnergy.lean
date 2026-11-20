/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CartanADualMinimum
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.E6CartanShortNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

theorem a11E6_short_trivial_class (a m t : ℤ) (A E : ℚ)
    (ha0 : 0 ≤ a) (ha11 : a ≤ 11)
    (hmin : (a : ℚ)*(12-a)/12 ≤ A) (hE0 : 0 ≤ E)
    (hA : A = 11*(a : ℚ)^2/12+2*(m : ℚ)) (hE : E = 2*(t : ℚ))
    (hsum : A+E = 9/4) :
    (a = 3 ∨ a = 9) ∧ A = 9/4 ∧ E = 0 := by
  have heqn : 11*a^2+24*(m+t) = 27 := by
    exact_mod_cast (show (11 : ℚ)*(a : ℚ)^2+24*((m : ℚ)+(t : ℚ)) = 27 by linarith)
  have ha : a = 3 ∨ a = 9 := by
    interval_cases a <;> norm_num at heqn ⊢ <;> omega
  have hlow : 9/4 ≤ A := by
    rcases ha with rfl | rfl <;> norm_num at hmin ⊢ <;> linarith
  exact ⟨ha, by linarith, by linarith⟩

theorem a11E6_short_nontrivial_class (a m t : ℤ) (A E : ℚ)
    (ha0 : 0 ≤ a) (ha11 : a ≤ 11)
    (hmin : (a : ℚ)*(12-a)/12 ≤ A) (hEmin : 4/3 ≤ E)
    (hA : A = 11*(a : ℚ)^2/12+2*(m : ℚ)) (hE : E = 4/3+2*(t : ℚ))
    (hsum : A+E = 9/4) :
    (a = 1 ∨ a = 11) ∧ A = 11/12 ∧ E = 4/3 := by
  have heqn : 11*a^2+24*(m+t) = 11 := by
    exact_mod_cast (show (11 : ℚ)*(a : ℚ)^2+24*((m : ℚ)+(t : ℚ)) = 11 by linarith)
  have hclasses : a = 1 ∨ a = 5 ∨ a = 7 ∨ a = 11 := by
    interval_cases a <;> norm_num at heqn ⊢ <;> omega
  have ha : a = 1 ∨ a = 11 := by
    rcases hclasses with h | h | h | h
    · exact Or.inl h
    · subst a; norm_num at hmin; linarith
    · subst a; norm_num at hmin; linarith
    · exact Or.inr h
  have hlow : 11/12 ≤ A := by
    rcases ha with rfl | rfl <;> norm_num at hmin ⊢ <;> linarith
  exact ⟨ha, by linarith, by linarith⟩

def A11E6ShortType (a : ℤ) (u : Fin 11 → ℚ) (v : Fin 6 → ℚ) : Prop :=
  ((a = 3 ∨ a = 9) ∧ cartanARatForm 11 u u = 9/4 ∧ E6Cartan.form v v = 0) ∨
  ((a = 1 ∨ a = 11) ∧ cartanARatForm 11 u u = 11/12 ∧ E6Cartan.form v v = 4/3 ∧
    ∃ c : ℤ, (c = -1 ∨ c = 1) ∧
      ∃ w ∈ coordinateIntegerLattice 6, v = w+c • E6Cartan.weight)

end SRG266.Lattice
