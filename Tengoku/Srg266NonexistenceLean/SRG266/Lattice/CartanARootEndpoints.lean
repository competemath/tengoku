/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.DRoot
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CartanADualMinimum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

/--
@isnad1 id=ex.2h2v.s7.979bdee2585a from=translated src=- shape=516c0c8e vocab=9da3fa2b
-/
theorem int_zero_sum_norm_two_endpoints {n : ℕ} (z : Fin n → ℤ)
    (hsum : (∑ i, z i) = 0) (hnorm : intDot z z = 2) :
    ∃ p q : Fin n, p ≠ q ∧ z = Pi.single p 1-Pi.single q 1 := by
  classical
  obtain ⟨⟨p, q, hpq, sp, sq⟩, hr⟩ := DRoot.exists_vector_eq_of_intDot_self_eq_two z hnorm
  have hs : signedUnit sp+signedUnit sq = 0 := by
    rw [← DRoot.sum_vector (⟨p, q, hpq, sp, sq⟩ : DRoot n), hr]
    exact hsum
  cases sp <;> cases sq <;> norm_num [signedUnit] at hs
  · refine ⟨q, p, ne_of_gt hpq, ?_⟩
    rw [← hr]
    ext i
    by_cases hip : i = p
    · subst i
      simp [DRoot.vector, signedUnit, ne_of_lt hpq]
    · by_cases hiq : i = q
      · subst i
        simp [DRoot.vector, signedUnit, ne_of_gt hpq]
      · simp [DRoot.vector, hip, hiq]
  · refine ⟨p, q, ne_of_lt hpq, ?_⟩
    rw [← hr]
    ext i
    by_cases hip : i = p
    · subst i
      simp [DRoot.vector, signedUnit, ne_of_lt hpq]
    · by_cases hiq : i = q
      · subst i
        simp [DRoot.vector, signedUnit, ne_of_gt hpq]
      · simp [DRoot.vector, hip, hiq]

/--
@isnad1 id=ex.3h2v.s9.f26864306140 from=translated src=- shape=86791845 vocab=27ac1ff0
-/
theorem rational_zero_sum_root_endpoints {n : ℕ} (x : Fin n → ℚ)
    (hx : x ∈ coordinateIntegerLattice n)
    (hsum : (∑ i, x i) = 0) (hnorm : standardRatForm n x x = 2) :
    ∃ p q : Fin n, p ≠ q ∧ x = Pi.single p 1-Pi.single q 1 := by
  classical
  obtain ⟨z, rfl⟩ := hx
  simp only [standardRatForm_apply, intCoordsToRat_apply] at hsum hnorm
  have hzsum : (∑ i, z i) = 0 := by exact_mod_cast hsum
  have hznorm : intDot z z = 2 := by
    change (∑ i, z i*z i) = 2
    exact_mod_cast hnorm
  obtain ⟨p, q, hpq, hz⟩ := int_zero_sum_norm_two_endpoints z hzsum hznorm
  refine ⟨p, q, hpq, ?_⟩
  rw [hz]
  ext i
  simp [intCoordsToRat_apply, Pi.single_apply]

/--
@isnad1 id=mem.0h2v.s8.14fdade45b3b from=translated src=- shape=a319c261 vocab=eafd5550
-/
theorem aSimpleVector_mem_integer {n : ℕ} (i : Fin n) :
    aSimpleVector i ∈ coordinateIntegerLattice (n+1) := by
  classical
  refine ⟨Pi.single i.castSucc 1-Pi.single i.succ 1, ?_⟩
  ext j
  simp [intCoordsToRat_apply, aSimpleVector, Pi.single_apply]

/--
@isnad1 id=mem.1h2v.s9.036572424738 from=translated src=- shape=a0f01809 vocab=7bbd7ccf
-/
theorem cartanAZeroSum_mem_integer (n : ℕ) {u : Fin n → ℚ}
    (hu : u ∈ coordinateIntegerLattice n) :
    cartanAZeroSum n u ∈ coordinateIntegerLattice (n+1) := by
  obtain ⟨z, rfl⟩ := hu
  change (∑ i, (z i : ℚ) • aSimpleVector i) ∈ coordinateIntegerLattice (n+1)
  simp only [Int.cast_smul_eq_zsmul]
  exact (coordinateIntegerLattice (n+1)).sum_mem (fun i _ =>
    (coordinateIntegerLattice (n+1)).smul_mem (z i) (aSimpleVector_mem_integer i))

end SRG266.Lattice
