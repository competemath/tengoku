/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.DRootCoordinateMoment
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.EvenCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

def DRoot.ratVector {n : ℕ} (r : DRoot n) : Fin n → ℚ := intCoordsToRat r.vector

theorem DRoot.ratVector_mem_even {n : ℕ} (r : DRoot n) :
    r.ratVector ∈ evenCoordinateLattice n := by
  apply mem_evenCoordinateLattice.mpr
  obtain ⟨k, hk⟩ := r.sum_vector_even
  exact ⟨r.vector, rfl, k, by omega⟩

theorem DRoot.ratVector_norm {n : ℕ} (r : DRoot n) :
    standardRatForm n r.ratVector r.ratVector = 2 := by
  have h := r.intDot_self
  change (∑ i, r.vector i * r.vector i) = 2 at h
  change (∑ i, (r.vector i : ℚ) * (r.vector i : ℚ)) = 2
  exact_mod_cast h

theorem DRoot.ratVector_injective {n : ℕ} :
    Function.Injective (@DRoot.ratVector n) := by
  intro r s h
  apply DRoot.vector_injective
  funext i
  have hi := congrFun h i
  change (r.vector i : ℚ) = (s.vector i : ℚ) at hi
  exact_mod_cast hi

theorem DRoot.exists_ratVector_of_norm_two {n : ℕ} {a : Fin n → ℚ}
    (ha : a ∈ evenCoordinateLattice n) (hn : standardRatForm n a a = 2) :
    ∃ r : DRoot n, r.ratVector = a := by
  obtain ⟨z, rfl, _⟩ := mem_evenCoordinateLattice.mp ha
  have hz : intDot z z = 2 := by
    change (∑ i, z i * z i) = 2
    change (∑ i, (z i : ℚ) * (z i : ℚ)) = 2 at hn
    exact_mod_cast hn
  obtain ⟨r, hr⟩ := DRoot.exists_vector_eq_of_intDot_self_eq_two z hz
  exact ⟨r, congrArg intCoordsToRat hr⟩

theorem dRoot_rat_coordinate_zero_secondMoment (n : ℕ) :
    (∑ r : DRoot (n + 1), (r.ratVector 0) ^ 2) = 4 * (n : ℚ) := by
  change (∑ r : DRoot (n + 1), ((r.vector 0 : ℤ) : ℚ) ^ 2) = 4 * (n : ℚ)
  exact_mod_cast dRoot_coordinate_zero_secondMoment n

end SRG266.Lattice
