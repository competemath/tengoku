/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Even
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

theorem four_dvd_of_odd_mul_square_eq_eight_mul {a m n : ℤ}
    (haodd : Odd a) (h : a * m ^ 2 = 8 * n) :
    4 ∣ m := by
  have h2 : (2 : ℤ) ∣ a * m ^ 2 := ⟨4 * n, by linarith⟩
  have hsq : (2 : ℤ) ∣ m ^ 2 :=
    (Int.isCoprime_two_left.mpr haodd).dvd_of_dvd_mul_left h2
  obtain ⟨b, rfl⟩ := Int.Prime.dvd_pow' Nat.prime_two hsq
  norm_num only [Nat.cast_ofNat] at h
  have hnext : a * b ^ 2 = 2 * n := by nlinarith [h]
  have hb2 : (2 : ℤ) ∣ b ^ 2 :=
    (Int.isCoprime_two_left.mpr haodd).dvd_of_dvd_mul_left ⟨n, hnext⟩
  obtain ⟨d, hd⟩ := Int.Prime.dvd_pow' Nat.prime_two hb2
  exact ⟨d, by omega⟩

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

theorem zsmul_mem_iff_four_dvd_of_odd_quarter_norm
    {B : LinearMap.BilinForm ℚ W} {P : Submodule ℤ W}
    (heven : IsEven B P) {u : W} {a : ℤ} (ha : Odd a) (hnorm : B u u = (a : ℚ) / 4)
    (hfour : (4 : ℤ) • u ∈ P) (m : ℤ) : m • u ∈ P ↔ 4 ∣ m := by
  constructor
  · intro hm
    obtain ⟨n, hn⟩ := heven _ hm
    have heqQ : (a : ℚ) * (m : ℚ) ^ 2 = 8 * (n : ℚ) := by
      simp only [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, hnorm] at hn
      nlinarith [hn]
    have heq : a * m ^ 2 = 8 * n := by exact_mod_cast heqQ
    exact four_dvd_of_odd_mul_square_eq_eight_mul ha heq
  · rintro ⟨k, rfl⟩
    have h : (4 * k) • u = k • ((4 : ℤ) • u) := by module
    rw [h]
    exact P.smul_mem k hfour

end SRG266.Lattice
