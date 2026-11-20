/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.E6CartanDual
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.GramDeterminantSquare
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SmallCartanDeterminants
import Tengoku.Seed.Data.Rat.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

theorem int_sq_ne_twenty (d : ℤ) : d^2 ≠ 20 := by
  intro h
  have h0 := Int.emod_nonneg d (show (3 : ℤ) ≠ 0 by norm_num)
  have h3 := Int.emod_lt_of_pos d (show (0 : ℤ) < 3 by norm_num)
  have hr : d%3 = 0 ∨ d%3 = 1 ∨ d%3 = 2 := by omega
  have hm := congrArg (fun z : ℤ => z%3) h
  rw [pow_two, Int.mul_emod] at hm
  rcases hr with h | h | h <;> norm_num [h] at hm

theorem rat_sq_ne_twenty (d : ℚ) : d^2 ≠ 20 := by
  intro h
  have hsq : IsSquare (20 : ℚ) := ⟨d, by simpa only [pow_two] using h.symm⟩
  obtain ⟨z, hz⟩ := Rat.isSquare_intCast_iff.mp
    (show IsSquare ((20 : ℤ) : ℚ) from hsq)
  exact int_sq_ne_twenty z (by simpa only [pow_two] using hz.symm)

namespace E6Cartan

end E6Cartan
end SRG266.Lattice
