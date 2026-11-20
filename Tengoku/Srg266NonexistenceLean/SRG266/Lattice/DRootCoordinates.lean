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

/--
@isnad1 id=mem.0h2v.s6.4b8a87d1bca3 from=translated src=- shape=ccb03db0 vocab=623d3d1d
-/
theorem DRoot.ratVector_mem_even {n : ℕ} (r : DRoot n) :
    r.ratVector ∈ evenCoordinateLattice n := by
  apply mem_evenCoordinateLattice.mpr
  obtain ⟨k, hk⟩ := r.sum_vector_even
  exact ⟨r.vector, rfl, k, by omega⟩

/--
@isnad1 id=eq.0h2v.s8.b0817bd1a88d from=translated src=- shape=3363551f vocab=49e57137
-/
theorem DRoot.ratVector_norm {n : ℕ} (r : DRoot n) :
    standardRatForm n r.ratVector r.ratVector = 2 := by
  have h := r.intDot_self
  change (∑ i, r.vector i * r.vector i) = 2 at h
  change (∑ i, (r.vector i : ℚ) * (r.vector i : ℚ)) = 2
  exact_mod_cast h

/--
@isnad1 id=injectiv.0h1v.s3.f96645f1eeb7 from=translated src=- shape=0cd72c43 vocab=8a1caf30
-/
theorem DRoot.ratVector_injective {n : ℕ} :
    Function.Injective (@DRoot.ratVector n) := by
  intro r s h
  apply DRoot.vector_injective
  funext i
  have hi := congrFun h i
  change (r.vector i : ℚ) = (s.vector i : ℚ) at hi
  exact_mod_cast hi

/--
@isnad1 id=ex.2h2v.s9.f5372c207813 from=translated src=- shape=07d6436a vocab=414c5c78
-/
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

/--
@isnad1 id=eq.0h1v.s7.ae7428b22761 from=translated src=- shape=fcf8450e vocab=fccfbc4f
-/
theorem dRoot_rat_coordinate_zero_secondMoment (n : ℕ) :
    (∑ r : DRoot (n + 1), (r.ratVector 0) ^ 2) = 4 * (n : ℚ) := by
  change (∑ r : DRoot (n + 1), ((r.vector 0 : ℤ) : ℚ) ^ 2) = 4 * (n : ℚ)
  exact_mod_cast dRoot_coordinate_zero_secondMoment n

end SRG266.Lattice
