/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CartanADualGap
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.E6CartanShortNorm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

/--
@isnad1 id=or.5h2v.s7.ca65bd061ec2 from=translated src=- shape=8db1fd13 vocab=ad7264d9
-/
theorem norm_four_split_values (a e : ℚ) (ha : 0 ≤ a) (he : 0 ≤ e)
    (hsum : a+e = 4) (hgap : a ≠ 2/3)
    (hclass : (∃ m : ℤ, e = 2*(m : ℚ)) ∨ (∃ m : ℤ, e = 4/3+2*(m : ℚ))) :
    e = 0 ∨ e = 4/3 ∨ e = 2 ∨ e = 4 := by
  rcases hclass with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hm0 : 0 ≤ m := by exact_mod_cast (show (0 : ℚ) ≤ m by linarith)
    have hm2 : m ≤ 2 := by exact_mod_cast (show (m : ℚ) ≤ 2 by linarith)
    have hcases : m = 0 ∨ m = 1 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl | rfl <;> norm_num at hm <;> aesop
  · have hmlo : -4 ≤ 6*m := by
      exact_mod_cast (show (-4 : ℚ) ≤ 6*(m : ℚ) by linarith)
    have hmhi : 6*m ≤ 8 := by
      exact_mod_cast (show 6*(m : ℚ) ≤ 8 by linarith)
    have hcases : m = 0 ∨ m = 1 := by omega
    rcases hcases with rfl | rfl
    · exact Or.inr (Or.inl (by norm_num at hm; exact hm))
    · exact (hgap (by norm_num at hm; linarith)).elim

namespace E6Cartan

def Q15ProjectionArithmetic (v w : Fin 6 → ℚ) : Prop :=
  ∃ x y z : ℤ, 3*form v v = (x : ℚ) ∧ 3*form w w = (y : ℚ) ∧
    3*form v w = (z : ℚ) ∧
    (x = 0 ∨ x = 4 ∨ x = 6 ∨ x = 12) ∧
    (y = 0 ∨ y = 4 ∨ y = 6 ∨ y = 12) ∧
    z^2 ≤ x*y ∧ (x = 6 → y = 6 → 3 ∣ z)

end E6Cartan
end SRG266.Lattice
