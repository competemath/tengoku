/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.EvenCoordinates
import Tengoku.Seed.Tactic.FinCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

/--
@isnad1 id=ex.1h1v.s9.8bd743df8edd from=translated src=- shape=6943c3d2 vocab=5ec7d27d
-/
theorem d7_dual_reduced {a : Fin 7 → ℚ}
    (ha : a ∈ (standardRatForm 7).dualSubmodule (evenCoordinateLattice 7)) :
    ∃ (v : Fin 7 → ℚ) (_ : v ∈ evenCoordinateLattice 7) (m : Fin 4),
      a = v + (m.val : ℤ) • coordinateSpinor 7 := by
  rw [d7_dual] at ha
  obtain ⟨v, hv, w, hw, heq⟩ := Submodule.mem_sup.mp ha
  obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hw
  let m : Fin 4 := ⟨(k % 4).toNat, by omega⟩
  have hm : (m.val : ℤ) = k % 4 := by dsimp [m]; omega
  refine ⟨v + (k / 4) • ((4 : ℤ) • coordinateSpinor 7),
    (evenCoordinateLattice 7).add_mem hv
      ((evenCoordinateLattice 7).smul_mem _ (four_smul_coordinateSpinor_mem 7)), m, ?_⟩
  rw [← heq, hm]
  have hk : k = 4 * (k / 4) + k % 4 := by omega
  conv_lhs => rw [hk]
  module

private theorem scalar_short_gap (m : Fin 4) (b n : ℤ) (d t : ℚ)
    (hd : 0 < d) (hd2 : d < 2)
    (hnorm : d = 7 * (m.val : ℚ) ^ 2 / 4 + 2 * (b : ℚ))
    (hpair : t + 7 * (m.val : ℚ) / 4 = n) :
    (2 - d) / 4 ≤ t ^ 2 := by
  fin_cases m
  · norm_num at hnorm hpair
    have hb0 : (0 : ℚ) < b := by linarith
    have hb1 : (b : ℚ) < 1 := by linarith
    have hb0' : 0 < b := by exact_mod_cast hb0
    have hb1' : b < 1 := by exact_mod_cast hb1
    omega
  · norm_num at hnorm hpair
    have hlo : (-1 : ℚ) < b := by linarith
    have hhi : (b : ℚ) < 1 := by linarith
    have hlo' : -1 < b := by exact_mod_cast hlo
    have hhi' : b < 1 := by exact_mod_cast hhi
    have hb : b = 0 := by omega
    subst b
    norm_num at hnorm
    have hn : n ≤ 1 ∨ 2 ≤ n := by omega
    rcases hn with hn | hn
    · have hnQ : (n : ℚ) ≤ 1 := by exact_mod_cast hn
      have ht : t ≤ -1 / 4 := by linarith
      nlinarith [sq_nonneg (t + 1 / 4)]
    · have hnQ : (2 : ℚ) ≤ n := by exact_mod_cast hn
      have ht : 1 / 4 ≤ t := by linarith
      nlinarith [sq_nonneg (t - 1 / 4)]
  · norm_num at hnorm hpair
    have hlo : (-4 : ℚ) < b := by linarith
    have hhi : (b : ℚ) < -2 := by linarith
    have hlo' : -4 < b := by exact_mod_cast hlo
    have hhi' : b < -2 := by exact_mod_cast hhi
    have hb : b = -3 := by omega
    subst b
    norm_num at hnorm
    have hn : n ≤ 3 ∨ 4 ≤ n := by omega
    rcases hn with hn | hn
    · have hnQ : (n : ℚ) ≤ 3 := by exact_mod_cast hn
      have ht : t ≤ -1 / 2 := by linarith
      nlinarith [sq_nonneg (t + 1 / 2)]
    · have hnQ : (4 : ℚ) ≤ n := by exact_mod_cast hn
      have ht : 1 / 2 ≤ t := by linarith
      nlinarith [sq_nonneg (t - 1 / 2)]
  · norm_num at hnorm hpair
    have hlo : (-8 : ℚ) < b := by linarith
    have hhi : (b : ℚ) < -6 := by linarith
    have hlo' : -8 < b := by exact_mod_cast hlo
    have hhi' : b < -6 := by exact_mod_cast hhi
    have hb : b = -7 := by omega
    subst b
    norm_num at hnorm
    have hn : n ≤ 5 ∨ 6 ≤ n := by omega
    rcases hn with hn | hn
    · have hnQ : (n : ℚ) ≤ 5 := by exact_mod_cast hn
      have ht : t ≤ -1 / 4 := by linarith
      nlinarith [sq_nonneg (t + 1 / 4)]
    · have hnQ : (6 : ℚ) ≤ n := by exact_mod_cast hn
      have ht : 1 / 4 ≤ t := by linarith
      nlinarith [sq_nonneg (t - 1 / 4)]

/--
@isnad1 id=le.4h2v.s11.a819e2f0a0ad from=translated src=- shape=4601e502 vocab=5f9a2e4d
-/
theorem d7_short_dual_gap {a : Fin 7 → ℚ}
    (ha : a ∈ (standardRatForm 7).dualSubmodule (evenCoordinateLattice 7))
    (hpos : 0 < standardRatForm 7 a a) (hsmall : standardRatForm 7 a a < 2)
    {t : ℚ} (hint : t + standardRatForm 7 a (coordinateSpinor 7) ∈ (1 : Submodule ℤ ℚ)) :
    (2 - standardRatForm 7 a a) / 4 ≤ t ^ 2 := by
  obtain ⟨v, hv, m, rfl⟩ := d7_dual_reduced ha
  obtain ⟨b, hb⟩ := evenCoordinateLattice_isEven 7 v hv
  obtain ⟨l, hl⟩ := mem_one_iff.mp (coordinateSpinor_mem_dual 7 v hv)
  have hl' : standardRatForm 7 v (coordinateSpinor 7) = (l : ℚ) := by
    rw [(standardRatForm_isSymm 7).eq]
    exact hl.symm
  have hsm : (m.val : ℤ) • coordinateSpinor 7 = (m.val : ℚ) • coordinateSpinor 7 := by module
  have hnorm : standardRatForm 7 (v + (m.val : ℤ) • coordinateSpinor 7)
      (v + (m.val : ℤ) • coordinateSpinor 7) =
      7 * (m.val : ℚ) ^ 2 / 4 + 2 * ((b + (m.val : ℤ) * l : ℤ) : ℚ) := by
    rw [hsm]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, hb, hl', ← hl, coordinateSpinor_norm]
    push_cast
    ring
  obtain ⟨n, hn⟩ := mem_one_iff.mp hint
  have hpair : t + 7 * (m.val : ℚ) / 4 = ((n - l : ℤ) : ℚ) := by
    rw [hsm] at hn
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
      smul_eq_mul, hl', coordinateSpinor_norm] at hn
    push_cast
    linarith
  exact scalar_short_gap m (b + (m.val : ℤ) * l) (n - l) _ t hpos hsmall hnorm hpair

end SRG266.Lattice
