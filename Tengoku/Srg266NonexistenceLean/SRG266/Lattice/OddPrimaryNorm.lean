/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Even
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Discriminant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {W : Type*} [AddCommGroup W] [Module ℚ W]
variable {B : LinearMap.BilinForm ℚ W} {N : Submodule ℤ W}

/--
@isnad1 id=even.4h6v.s8.08b09dadd908 from=translated src=- shape=94e5c43a vocab=193cfa46
-/
theorem even_numerator_of_odd_multiple {p m : ℤ} (hp : Odd p)
    (hN : IsEven B N) {u : W} (hu : p • u ∈ N)
    (hnorm : (p : ℚ) * B u u = (m : ℚ)) : Even m := by
  obtain ⟨k, hk⟩ := hN _ hu
  have hQ : (p : ℚ) * m = 2 * (k : ℚ) := by
    simp only [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul] at hk
    rwa [hnorm] at hk
  have hZ : p * m = 2 * k := by exact_mod_cast hQ
  exact even_iff_two_dvd.mpr
    ((Int.isCoprime_two_left.mpr hp).dvd_of_dvd_mul_left ⟨k, hZ⟩)

/--
@isnad1 id=ex.2h6v.s8.29483af974ec from=translated src=- shape=83624952 vocab=59cba6ee
-/
theorem GlueBasis.exists_even_diag {p : ℕ} (S : GlueBasis B N p)
    (hp : Odd (p : ℤ)) (hN : IsEven B N) (i : Fin S.rank) :
    ∃ m : ℤ, Even m ∧ ¬ (p : ℤ) ∣ m ∧ (p : ℚ) * B (S.vec i) (S.vec i) = (m : ℚ) := by
  obtain ⟨m, hndiv, hm⟩ := S.diag i
  exact ⟨m, even_numerator_of_odd_multiple hp hN
    (mem_torsionPart.mp (S.mem i)).2 hm, hndiv, hm⟩

omit [AddCommGroup W] [Module ℚ W] in
/--
@isnad1 id=ex.3h2v.s6.8a3de657c80d from=translated src=- shape=8d18f4c6 vocab=32e73e38
-/
theorem norm_mod_two_three {q : ℚ} {m : ℤ} (hm : Even m) (hunit : ¬ (3 : ℤ) ∣ m)
    (hq : 3 * q = (m : ℚ)) :
    ∃ r k : ℤ, (r = 2 ∨ r = 4) ∧ q = (r : ℚ) / 3 + 2 * (k : ℚ) := by
  have hr : m % 6 = 2 ∨ m % 6 = 4 := by
    obtain ⟨k, hk⟩ := hm
    omega
  refine ⟨m % 6, m / 6, hr, ?_⟩
  have hZ : m = 6 * (m / 6) + m % 6 := by omega
  have hQ : (m : ℚ) = 6 * ((m / 6 : ℤ) : ℚ) + ((m % 6 : ℤ) : ℚ) := by exact_mod_cast hZ
  linarith

omit [AddCommGroup W] [Module ℚ W] in
/--
@isnad1 id=ex.3h2v.s6.3c6746b099fe from=translated src=- shape=d7e882c9 vocab=32e73e38
-/
theorem norm_mod_two_five {q : ℚ} {m : ℤ} (hm : Even m) (hunit : ¬ (5 : ℤ) ∣ m)
    (hq : 5 * q = (m : ℚ)) :
    ∃ r k : ℤ, (r = 2 ∨ r = 4 ∨ r = 6 ∨ r = 8) ∧
      q = (r : ℚ) / 5 + 2 * (k : ℚ) := by
  have hr : m % 10 = 2 ∨ m % 10 = 4 ∨ m % 10 = 6 ∨ m % 10 = 8 := by
    obtain ⟨k, hk⟩ := hm
    omega
  refine ⟨m % 10, m / 10, hr, ?_⟩
  have hZ : m = 10 * (m / 10) + m % 10 := by omega
  have hQ : (m : ℚ) = 10 * ((m / 10 : ℤ) : ℚ) + ((m % 10 : ℤ) : ℚ) := by exact_mod_cast hZ
  linarith

omit [AddCommGroup W] [Module ℚ W] in

/--
@isnad1 id=ex.3h2v.s7.7f4f8f7c6b7c from=translated src=- shape=b2502d0d vocab=9cd12dae
-/
theorem normalized_norm_five {q : ℚ} {m : ℤ} (hm : Even m) (hunit : ¬ (5 : ℤ) ∣ m)
    (hq : 5 * q = (m : ℚ)) :
    ∃ a r k : ℤ, (a = 1 ∨ a = 2) ∧ (r = 2 ∨ r = 4) ∧
      (a : ℚ) ^ 2 * q = (r : ℚ) / 5 + 2 * (k : ℚ) := by
  obtain ⟨r, k, hr, hk⟩ := norm_mod_two_five hm hunit hq
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨1, 2, k, Or.inl rfl, Or.inl rfl, by simpa using hk⟩
  · exact ⟨1, 4, k, Or.inl rfl, Or.inr rfl, by simpa using hk⟩
  · refine ⟨2, 4, 2 + 4 * k, Or.inr rfl, Or.inr rfl, ?_⟩
    push_cast
    linarith
  · refine ⟨2, 2, 3 + 4 * k, Or.inr rfl, Or.inl rfl, ?_⟩
    push_cast
    linarith

omit [AddCommGroup W] [Module ℚ W] in

/--
@isnad1 id=dvd.4h5v.s7.30598d9940a3 from=translated src=- shape=73e94631 vocab=6fd26816
-/
theorem norm_denominator_unit {p r k : ℤ} {q : ℚ} (hp : p ≠ 0)
    (hcop : IsCoprime p r) (hq : q = (r : ℚ) / (p : ℚ) + 2 * (k : ℚ))
    (a : ℤ) (ha : (a : ℚ) * q ∈ (1 : Submodule ℤ ℚ)) : p ∣ a := by
  obtain ⟨b, hb⟩ := mem_one_iff.mp ha
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hQ : (a : ℚ) * r = (p : ℚ) * ((b : ℚ) - 2 * a * k) := by
    rw [hq] at hb
    field_simp at hb
    nlinarith [hb]
  have hZ : a * r = p * (b - 2 * a * k) := by exact_mod_cast hQ
  exact hcop.dvd_of_dvd_mul_right ⟨b - 2 * a * k, hZ⟩

end SRG266.Lattice
