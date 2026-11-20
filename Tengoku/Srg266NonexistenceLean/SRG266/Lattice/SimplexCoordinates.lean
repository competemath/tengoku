/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.IntegerCoordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Even

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

def coordinateSumForm (n : ℕ) : LinearMap.BilinForm ℚ (Fin n → ℚ) :=
  LinearMap.mk₂ ℚ (fun x y => (∑ i, x i) * ∑ i, y i)
    (by intros; simp [Finset.sum_add_distrib, add_mul])
    (by intros; simp [← Finset.mul_sum, mul_assoc])
    (by intros; simp [Finset.sum_add_distrib, mul_add])
    (by intros; simp [← Finset.mul_sum, mul_left_comm])

def simplexRatForm (n : ℕ) : LinearMap.BilinForm ℚ (Fin n → ℚ) :=
  standardRatForm n + coordinateSumForm n

@[simp]
theorem simplexRatForm_apply {n : ℕ} (x y : Fin n → ℚ) :
    simplexRatForm n x y = (∑ i, x i * y i) + (∑ i, x i) * ∑ i, y i := rfl

theorem simplexRatForm_isSymm (n : ℕ) : (simplexRatForm n).IsSymm := by
  constructor
  intro x y
  simp only [simplexRatForm_apply]
  congr 1
  · exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  · exact mul_comm _ _

theorem simplexRatForm_posDef (n : ℕ) :
    ∀ x : Fin n → ℚ, x ≠ 0 → 0 < simplexRatForm n x x := by
  intro x hx
  exact add_pos_of_pos_of_nonneg (standardRatForm_posDef n x hx) (mul_self_nonneg _)

theorem simplexRatForm_isIntegral (n : ℕ) :
    IsIntegral (simplexRatForm n) (coordinateIntegerLattice n) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  apply mem_one_iff.mpr
  refine ⟨(∑ i, x i * y i) + (∑ i, x i) * ∑ i, y i, ?_⟩
  simp only [simplexRatForm_apply, intCoordsToRat_apply]
  push_cast
  rfl

theorem simplexRatForm_isEven (n : ℕ) :
    IsEven (simplexRatForm n) (coordinateIntegerLattice n) := by
  rintro _ ⟨z, rfl⟩
  have hdiff : (2 : ℤ) ∣ (∑ i, z i * z i - ∑ i, z i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ => ?_
    convert (Int.even_mul_pred_self (z i)).two_dvd using 1
    ring
  have hsum := (Int.even_mul_succ_self (∑ i, z i)).two_dvd
  obtain ⟨k, hk⟩ := dvd_add hdiff hsum
  have heq : (∑ i, z i * z i) + (∑ i, z i) * (∑ i, z i) = 2 * k := by
    nlinarith [hk]
  refine ⟨k, ?_⟩
  change (∑ i, (z i : ℚ) * (z i : ℚ)) +
    (∑ i, (z i : ℚ)) * (∑ i, (z i : ℚ)) = 2 * (k : ℚ)
  exact_mod_cast heq

def simplexWeight (n : ℕ) : Fin n → ℚ := fun _ => 1 / ((n : ℚ) + 1)

theorem simplexWeight_pair {n : ℕ} (x : Fin n → ℚ) :
    simplexRatForm n (simplexWeight n) x = ∑ i, x i := by
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  simp only [simplexRatForm_apply, simplexWeight, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem simplexWeight_norm (n : ℕ) :
    simplexRatForm n (simplexWeight n) (simplexWeight n) = (n : ℚ) / ((n : ℚ) + 1) := by
  rw [simplexWeight_pair]
  simp [simplexWeight, div_eq_mul_inv]

theorem simplexWeight_mem_dual (n : ℕ) :
    simplexWeight n ∈ (simplexRatForm n).dualSubmodule (coordinateIntegerLattice n) := by
  rintro _ ⟨z, rfl⟩
  rw [simplexWeight_pair]
  exact mem_one_iff.mpr ⟨∑ i, z i, by simp⟩

theorem succ_smul_simplexWeight_mem (n : ℕ) :
    ((n : ℤ) + 1) • simplexWeight n ∈ coordinateIntegerLattice n := by
  refine mem_coordinateIntegerLattice.mpr ⟨fun _ => 1, ?_⟩
  intro i
  change (1 : ℚ) = ((n : ℤ) + 1) • (1 / ((n : ℚ) + 1))
  rw [zsmul_eq_mul]
  push_cast
  field_simp

theorem simplexWeight_zsmul_mem_iff {n : ℕ} (i₀ : Fin n) (m : ℤ) :
    m • simplexWeight n ∈ coordinateIntegerLattice n ↔ (n : ℤ) + 1 ∣ m := by
  constructor
  · intro hm
    obtain ⟨z, hz⟩ := mem_coordinateIntegerLattice.mp hm
    have h := hz i₀
    change (z i₀ : ℚ) = m • (1 / ((n : ℚ) + 1)) at h
    rw [zsmul_eq_mul] at h
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    have hQ : (m : ℚ) = ((n : ℚ) + 1) * (z i₀ : ℚ) := by
      field_simp at h
      linarith
    refine ⟨z i₀, ?_⟩
    exact_mod_cast hQ
  · rintro ⟨k, rfl⟩
    have heq : (((n : ℤ) + 1) * k) • simplexWeight n =
        k • (((n : ℤ) + 1) • simplexWeight n) := by module
    rw [heq]
    exact Submodule.smul_mem _ k (succ_smul_simplexWeight_mem n)

private theorem simplexRatForm_int_single {n : ℕ} (x : Fin n → ℚ) (i : Fin n) :
    simplexRatForm n x (intCoordsToRat (Pi.single i 1)) = x i + ∑ j, x j := by
  simp [simplexRatForm_apply, intCoordsToRat, Pi.single_apply, mul_ite]

theorem simplexRatForm_dual (n : ℕ) :
    (simplexRatForm n).dualSubmodule (coordinateIntegerLattice n) =
      coordinateIntegerLattice n ⊔ Submodule.span ℤ {simplexWeight n} := by
  apply le_antisymm
  · intro x hx
    have hz : ∀ i, ∃ z : ℤ, (z : ℚ) = x i + ∑ j, x j := by
      intro i
      have h := hx _ (intCoordsToRat_mem (Pi.single i 1))
      rw [simplexRatForm_int_single] at h
      exact mem_one_iff.mp h
    choose z hz using hz
    let a : ℤ := ∑ i, z i
    have ha : (a : ℚ) = ((n : ℚ) + 1) * ∑ i, x i := by
      change ((∑ i, z i : ℤ) : ℚ) = _
      push_cast
      simp_rw [hz]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hn : (n : ℚ) + 1 ≠ 0 := by positivity
    have heq : x = intCoordsToRat z + (-a) • simplexWeight n := by
      ext i
      change x i = (z i : ℚ) + (-a) • (1 / ((n : ℚ) + 1))
      rw [zsmul_eq_mul]
      push_cast
      rw [hz i, ha]
      field_simp
      ring
    rw [heq]
    exact Submodule.add_mem_sup (intCoordsToRat_mem z)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · refine sup_le (simplexRatForm_isIntegral n) (Submodule.span_le.mpr ?_)
    rintro _ (rfl : _ = simplexWeight n)
    exact simplexWeight_mem_dual n

end SRG266.Lattice
