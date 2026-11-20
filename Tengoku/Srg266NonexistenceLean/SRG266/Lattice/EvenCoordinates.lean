/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.IntegerCoordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.QuarterCoset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

def evenSumIntegers (n : ℕ) : Submodule ℤ (Fin n → ℤ) where
  carrier := {z | Even (∑ i, z i)}
  zero_mem' := by simp
  add_mem' := by
    intro z w hz hw
    change Even (∑ i, (z + w) i)
    simpa only [Pi.add_apply, Finset.sum_add_distrib] using hz.add hw
  smul_mem' := by
    intro a z hz
    change Even (∑ i, (a • z) i)
    simpa only [Pi.smul_apply, zsmul_eq_mul, Int.cast_id, ← Finset.mul_sum]
      using hz.mul_left a

def evenCoordinateLattice (n : ℕ) : Submodule ℤ (Fin n → ℚ) :=
  (evenSumIntegers n).map intCoordsToRat

theorem mem_evenCoordinateLattice {n : ℕ} {v : Fin n → ℚ} :
    v ∈ evenCoordinateLattice n ↔
      ∃ z : Fin n → ℤ, intCoordsToRat z = v ∧ Even (∑ i, z i) := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, rfl, hz⟩
  · rintro ⟨z, rfl, hz⟩
    exact ⟨z, hz, rfl⟩

theorem evenCoordinateLattice_le (n : ℕ) :
    evenCoordinateLattice n ≤ coordinateIntegerLattice n := by
  rintro v ⟨z, _, rfl⟩
  exact intCoordsToRat_mem z

theorem two_smul_mem_evenCoordinateLattice {n : ℕ} {v : Fin n → ℚ}
    (hv : v ∈ coordinateIntegerLattice n) :
    (2 : ℤ) • v ∈ evenCoordinateLattice n := by
  obtain ⟨z, rfl⟩ := hv
  refine ⟨(2 : ℤ) • z, ?_, map_zsmul intCoordsToRat 2 z⟩
  change Even (∑ i, (2 : ℤ) • z i)
  simp only [zsmul_eq_mul, ← Finset.mul_sum]
  exact even_two_mul _

theorem evenCoordinateLattice_isLattice (n : ℕ) :
    IsLattice ℚ (evenCoordinateLattice n) := by
  constructor
  · exact (coordinateIntegerLattice_isLattice n).fg.of_le (evenCoordinateLattice_le n)
  · refine top_unique ?_
    rw [← (coordinateIntegerLattice_isLattice n).spans]
    refine Submodule.span_le.mpr ?_
    intro v hv
    have h := Submodule.subset_span (R := ℚ) (two_smul_mem_evenCoordinateLattice hv)
    have h' := (Submodule.span ℚ (evenCoordinateLattice n : Set (Fin n → ℚ))).smul_mem
      (1 / 2 : ℚ) h
    have heq : (1 / 2 : ℚ) • (2 : ℤ) • v = v := by
      ext i
      simp [zsmul_eq_mul]
    rwa [heq] at h'

theorem evenCoordinateLattice_isIntegral (n : ℕ) :
    IsIntegral (standardRatForm n) (evenCoordinateLattice n) := by
  intro x hx y hy
  have hx' := evenCoordinateLattice_le n hx
  rw [← standardRatForm_dual_coordinateIntegerLattice] at hx'
  exact hx' y (evenCoordinateLattice_le n hy)

theorem evenCoordinateLattice_isEven (n : ℕ) :
    IsEven (standardRatForm n) (evenCoordinateLattice n) := by
  intro v hv
  obtain ⟨z, rfl, hz⟩ := mem_evenCoordinateLattice.mp hv
  have hdiff : (2 : ℤ) ∣ (∑ i, z i * z i - ∑ i, z i) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun i _ => ?_
    convert (Int.even_mul_pred_self (z i)).two_dvd using 1
    ring
  obtain ⟨k, hk⟩ := dvd_add hdiff hz.two_dvd
  refine ⟨k, ?_⟩
  have hk' : (∑ i, z i * z i) = 2 * k := by simpa using hk
  change (∑ i, (z i : ℚ) * (z i : ℚ)) = 2 * (k : ℚ)
  exact_mod_cast hk'

def coordinateSpinor (n : ℕ) : Fin n → ℚ := fun _ => 1 / 2

theorem coordinateSpinor_norm (n : ℕ) :
    standardRatForm n (coordinateSpinor n) (coordinateSpinor n) = (n : ℚ) / 4 := by
  simp [standardRatForm_apply, coordinateSpinor]
  ring

theorem coordinateSpinor_mem_dual (n : ℕ) :
    coordinateSpinor n ∈ (standardRatForm n).dualSubmodule (evenCoordinateLattice n) := by
  intro v hv
  obtain ⟨z, rfl, k, hk⟩ := mem_evenCoordinateLattice.mp hv
  apply mem_one_iff.mpr
  refine ⟨k, ?_⟩
  simp only [standardRatForm_apply, coordinateSpinor, intCoordsToRat_apply,
    ← Finset.mul_sum]
  have hk' : (∑ i, (z i : ℚ)) = (k : ℚ) + k := by exact_mod_cast hk
  rw [hk']
  ring

theorem four_smul_coordinateSpinor_mem (n : ℕ) :
    (4 : ℤ) • coordinateSpinor n ∈ evenCoordinateLattice n := by
  apply mem_evenCoordinateLattice.mpr
  refine ⟨fun _ => 2, ?_, ?_⟩
  · ext i
    norm_num [coordinateSpinor, zsmul_eq_mul]
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact even_two.mul_left _

theorem d7_spinor_order (m : ℤ) :
    m • coordinateSpinor 7 ∈ evenCoordinateLattice 7 ↔ 4 ∣ m := by
  exact zsmul_mem_iff_four_dvd_of_odd_quarter_norm
    (evenCoordinateLattice_isEven 7) (by decide : Odd (7 : ℤ))
    (by simpa using coordinateSpinor_norm 7) (four_smul_coordinateSpinor_mem 7) m

private theorem dot_int_single {n : ℕ} (x : Fin n → ℚ) (i : Fin n) (a : ℤ) :
    standardRatForm n x (intCoordsToRat (Pi.single i a)) = x i * (a : ℚ) := by
  simp [standardRatForm_apply, intCoordsToRat, Pi.single_apply, mul_ite]

theorem odd_evenCoordinateLattice_dual {n : ℕ} (hn : Odd n) (i₀ : Fin n) :
    (standardRatForm n).dualSubmodule (evenCoordinateLattice n) =
      evenCoordinateLattice n ⊔ Submodule.span ℤ {coordinateSpinor n} := by
  apply le_antisymm
  · intro x hx
    have hdiff : ∀ i, ∃ z : ℤ, (z : ℚ) = x i - x i₀ := by
      intro i
      have hv : intCoordsToRat (Pi.single i 1 - Pi.single i₀ 1) ∈
          evenCoordinateLattice n := by
        apply mem_evenCoordinateLattice.mpr
        refine ⟨_, rfl, ?_⟩
        simp [Finset.sum_sub_distrib]
      have h := hx _ hv
      simp only [map_sub, dot_int_single, Int.cast_one, mul_one] at h
      exact mem_one_iff.mp h
    choose z hz using hdiff
    have htwice : ∃ k : ℤ, (k : ℚ) = 2 * x i₀ := by
      have hv : intCoordsToRat (Pi.single i₀ 2) ∈ evenCoordinateLattice n := by
        apply mem_evenCoordinateLattice.mpr
        exact ⟨_, rfl, by simp⟩
      have h := hx _ hv
      simpa only [dot_int_single, Int.cast_ofNat, mul_comm] using mem_one_iff.mp h
    obtain ⟨k, hk⟩ := htwice
    let t : ℤ := ∑ i, z i
    let w : Fin n → ℤ := fun i => z i - t
    have hw : intCoordsToRat w ∈ evenCoordinateLattice n := by
      apply mem_evenCoordinateLattice.mpr
      refine ⟨w, rfl, ?_⟩
      have hn' : Odd (n : ℤ) := by exact_mod_cast hn
      have heven := (odd_one.sub_odd hn').mul_right t
      have heq : (∑ i, w i) = (1 - (n : ℤ)) * t := by
        simp only [w, Finset.sum_sub_distrib, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        change t - (n : ℤ) * t = _
        ring
      rwa [heq]
    have heq : x = intCoordsToRat w + (k + 2 * t) • coordinateSpinor n := by
      ext i
      change x i = ((z i - t : ℤ) : ℚ) + (k + 2 * t) • (1 / 2 : ℚ)
      rw [zsmul_eq_mul]
      push_cast
      rw [hz i, hk]
      ring
    rw [heq]
    exact Submodule.add_mem_sup hw
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _)))
  · refine sup_le (evenCoordinateLattice_isIntegral n) (Submodule.span_le.mpr ?_)
    rintro _ (rfl : _ = coordinateSpinor n)
    exact coordinateSpinor_mem_dual n

theorem d7_dual :
    (standardRatForm 7).dualSubmodule (evenCoordinateLattice 7) =
      evenCoordinateLattice 7 ⊔ Submodule.span ℤ {coordinateSpinor 7} :=
  odd_evenCoordinateLattice_dual (by decide) 0

end SRG266.Lattice
