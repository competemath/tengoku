/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.GramDivisibilityLattice
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.EvenCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped Matrix BigOperators Classical

/--
@isnad1 id=not.0h2v.s7.ba532d0a8c73 from=translated src=- shape=6c742425 vocab=7e000043
-/
theorem coordinateUnit_not_mem_even {n : ℕ} (i : Fin n) :
    Pi.single i (1 : ℚ) ∉ evenCoordinateLattice n := by
  rintro ⟨z, hz, heq⟩
  have hzi : z = Pi.single i 1 := by
    funext j
    have hj := congrFun heq j
    change (z j : ℚ) = (Pi.single i 1 : Fin n → ℚ) j at hj
    by_cases hji : j = i <;> simp [hji] at hj ⊢ <;> exact_mod_cast hj
  change Even (∑ j, z j) at hz
  rw [hzi] at hz
  simp at hz

/--
@isnad1 id=mem.0h3v.s7.44d772172546 from=translated src=- shape=1cacb4e9 vocab=28239a0c
-/
theorem coordinateUnit_add_mem_even {n : ℕ} (i j : Fin n) :
    Pi.single i (1 : ℚ) + Pi.single j 1 ∈ evenCoordinateLattice n := by
  apply mem_evenCoordinateLattice.mpr
  refine ⟨Pi.single i 1 + Pi.single j 1, ?_, ?_⟩
  · ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all
    norm_num
  · simp [Finset.sum_add_distrib]

/--
@isnad1 id=mem.0h3v.s7.b21026bce600 from=translated src=- shape=1cacb4e9 vocab=fdfd7c52
-/
theorem coordinateUnit_sub_mem_even {n : ℕ} (i j : Fin n) :
    Pi.single i (1 : ℚ) - Pi.single j 1 ∈ evenCoordinateLattice n := by
  apply mem_evenCoordinateLattice.mpr
  refine ⟨Pi.single i 1 - Pi.single j 1, ?_, ?_⟩
  · ext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;>
      simp_all
  · simp [Finset.sum_sub_distrib]

/--
@isnad1 id=eq.1h3v.s9.964ecf3a2a7f from=translated src=- shape=9209bad7 vocab=daddf247
-/
theorem coordinateUnit_add_norm {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    standardRatForm n (Pi.single i 1 + Pi.single j 1)
      (Pi.single i 1 + Pi.single j 1) = 2 := by
  norm_num [map_add, LinearMap.add_apply, standardRatForm_apply,
    Pi.single_apply, mul_ite, hij, hij.symm]

/--
@isnad1 id=eq.1h3v.s9.48d5d114d505 from=translated src=- shape=9209bad7 vocab=5281ff78
-/
theorem coordinateUnit_sub_norm {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    standardRatForm n (Pi.single i 1 - Pi.single j 1)
      (Pi.single i 1 - Pi.single j 1) = 2 := by
  norm_num [map_sub, LinearMap.sub_apply, standardRatForm_apply,
    Pi.single_apply, mul_ite, hij, hij.symm]

/--
@isnad1 id=not.7h11v.s13.a2419e456fba from=translated src=- shape=42099ef9 vocab=a6a9cd78
-/
theorem not_two_gramDivisibility_of_integral_root_projection
    {ι W U : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]
    {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (B : LinearMap.BilinForm ℚ W) (C : LinearMap.BilinForm ℚ U)
    (L : Submodule ℤ ((W × (Fin n → ℚ)) × U))
    (hD : ∀ a, (((0 : W), a), (0 : U)) ∈ L ↔ a ∈ evenCoordinateLattice n)
    (hproj : ∀ r ∈ L, prodForm (prodForm B (standardRatForm n)) C r r = 2 →
      r.1.2 ∈ coordinateIntegerLattice n)
    (A : Matrix ι ι ℤ) (hdiag : ∀ a, A a a = 2)
    (φ : (ι → ℤ) →ₗ[ℤ] ((W × (Fin n → ℚ)) × U))
    (hmem : ∀ z, φ z ∈ L)
    (hpair : ∀ z w, prodForm (prodForm B (standardRatForm n)) C (φ z) (φ w) =
      (Matrix.toBilin' A z w : ℚ))
    (hcover : ∀ r ∈ L, prodForm (prodForm B (standardRatForm n)) C r r = 2 →
      ∃ z, φ z = r) :
    ¬GramDivisibilityDescent 2 A := by
  intro hd
  let F := prodForm (prodForm B (standardRatForm n)) C
  let q : (W × (Fin n → ℚ)) × U := ((0, Pi.single i 1), 0)
  let rp : (W × (Fin n → ℚ)) × U := ((0, Pi.single i 1 + Pi.single j 1), 0)
  let rm : (W × (Fin n → ℚ)) × U := ((0, Pi.single i 1 - Pi.single j 1), 0)
  have hrp : rp ∈ L := (hD _).mpr (coordinateUnit_add_mem_even i j)
  have hrm : rm ∈ L := (hD _).mpr (coordinateUnit_sub_mem_even i j)
  have hnp : F rp rp = 2 := by
    simpa [F, rp, prodForm_apply] using coordinateUnit_add_norm hij
  have hnm : F rm rm = 2 := by
    simpa [F, rm, prodForm_apply] using coordinateUnit_sub_norm hij
  obtain ⟨zp, hzp⟩ := hcover rp hrp hnp
  obtain ⟨zm, hzm⟩ := hcover rm hrm hnm
  have hz : φ (zp + zm) = (2 : ℚ) • q := by
    rw [map_add, hzp, hzm]
    apply Prod.ext
    · apply Prod.ext
      · simp [rp, rm, q]
      · ext k
        change ((Pi.single i 1 : Fin n → ℚ) k + (Pi.single j 1 : Fin n → ℚ) k) +
          ((Pi.single i 1 : Fin n → ℚ) k - (Pi.single j 1 : Fin n → ℚ) k) =
          2 * (Pi.single i 1 : Fin n → ℚ) k
        ring
    · simp [rp, rm, q]
  have hqpair (a : ι) : ∃ k : ℤ, F (φ (Pi.single a 1)) q = (k : ℚ) := by
    have hn : F (φ (Pi.single a 1)) (φ (Pi.single a 1)) = 2 := by
      rw [hpair, Matrix.toBilin'_single, hdiag]
      norm_num
    obtain ⟨v, hv⟩ := mem_coordinateIntegerLattice.mp (hproj _ (hmem _) hn)
    refine ⟨v i, ?_⟩
    simpa [F, q, prodForm_apply, standardRatForm_apply, Pi.single_apply, mul_ite]
      using (hv i).symm
  have hqmem : q ∈ L := mem_of_gramDivisibilityDescent F L φ hmem A hpair
    (by norm_num) hd q (zp + zm) hz hqpair
  exact coordinateUnit_not_mem_even i ((hD _).mp hqmem)

end SRG266.Lattice
