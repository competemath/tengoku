import Tengoku.Seed.RingTheory.UniqueFactorizationDomain.Moebius
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

namespace SevenEighths.InverseMoment

open UniqueFactorizationMonoid

section Moebius

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]

/--
@isnad1 id=eq.1h2v.s5.51a2ef71e722 from=translated src=- shape=127ebc3d vocab=7b461c00
-/
theorem moebius_squarefree_sq {P : M} (hP : Squarefree P) :
    moebius P ^ 2 = 1 := by
  rw [hP.moebius_eq, ← pow_mul, mul_comm _ 2, pow_mul]
  norm_num

/--
@isnad1 id=eq.2h3v.s6.119392fc32a0 from=translated src=- shape=e8712e00 vocab=a620195a
-/
theorem moebius_overlap_recovery {n P : M} (hnP : IsRelPrime n P)
    (hP : Squarefree P) : moebius n = moebius (n * P) * moebius P := by
  rw [hnP.moebius_mul, mul_assoc, ← pow_two, moebius_squarefree_sq hP, mul_one]

/--
@isnad1 id=eq.3h5v.s8.90b75f461552 from=translated src=- shape=f0adf70d vocab=0ab09db5
-/
theorem moebius_character_overlap (ψ : M →* ℂ) {j n₀ P₀ : M}
    (hjn : IsRelPrime j n₀) (hnP : IsRelPrime n₀ P₀) (hP : Squarefree P₀) :
    (moebius (j * n₀) : ℂ) * ψ (j * n₀) * ψ (j * P₀) =
      (moebius j : ℂ) * (moebius P₀ : ℂ) * (moebius (n₀ * P₀) : ℂ) *
        ψ j ^ 2 * ψ (n₀ * P₀) := by
  have hμ : (moebius n₀ : ℂ) = (moebius (n₀ * P₀) : ℂ) * (moebius P₀ : ℂ) := by
    exact_mod_cast moebius_overlap_recovery hnP hP
  rw [hjn.moebius_mul, Int.cast_mul, map_mul, map_mul, map_mul, hμ]
  ring

/--
@isnad1 id=ex.8h6v.s8.f44f948393de from=translated src=- shape=8b70cf12 vocab=aade9367
-/
theorem hybrid_mask_quotients {k P c R r : M}
    (hk : Squarefree k) (hP : Squarefree P) (hc : Squarefree c)
    (hPc : IsRelPrime P c) (hRk : R ∣ k) (hrk : r ∣ k)
    (hRP : R ∣ P) (hrc : r ∣ c) :
    ∃ k' P' c' : M,
      k = (R * r) * k' ∧ P = R * P' ∧ c = r * c' ∧
      IsRelPrime R r ∧ IsRelPrime k' (R * r) ∧
      IsRelPrime P' R ∧ IsRelPrime c' r ∧
      Squarefree k' ∧ Squarefree P' ∧ Squarefree c' := by
  have hRr : IsRelPrime R r := (hPc.of_dvd_left hRP).of_dvd_right hrc
  obtain ⟨k', hk'⟩ := hRr.mul_dvd hRk hrk
  obtain ⟨P', hP'⟩ := hRP
  obtain ⟨c', hc'⟩ := hrc
  have hks : Squarefree ((R * r) * k') := hk' ▸ hk
  have hPs : Squarefree (R * P') := hP' ▸ hP
  have hcs : Squarefree (r * c') := hc' ▸ hc
  obtain ⟨hkrel, _, hksf⟩ := squarefree_mul_iff.mp hks
  obtain ⟨hPrel, _, hPsf⟩ := squarefree_mul_iff.mp hPs
  obtain ⟨hcrel, _, hcsf⟩ := squarefree_mul_iff.mp hcs
  exact ⟨k', P', c', hk', hP', hc', hRr, hkrel.symm,
    hPrel.symm, hcrel.symm, hksf, hPsf, hcsf⟩

end Moebius

/--
@isnad1 id=eq.1h1v.s5.3e2bc3ed7822 from=translated src=- shape=48d8693c vocab=d0d1dd84
-/
theorem inverse_eq_square_of_fourth_eq {z : ℂ} (hz : z ^ 4 = z) :
    z⁻¹ = z ^ 2 := by
  by_cases hzero : z = 0
  · simp [hzero]
  have hcube : z ^ 3 = 1 := by
    apply mul_left_cancel₀ hzero
    calc
      z * z ^ 3 = z ^ 4 := by ring
      _ = z := hz
      _ = z * 1 := by ring
  calc
    z⁻¹ = z⁻¹ * z ^ 3 := by rw [hcube, mul_one]
    _ = z ^ 2 := by field_simp

/--
@isnad1 id=eq.1h1v.s6.e9fb5155eb4f from=translated src=- shape=de0b2b38 vocab=d0d1dd84
-/
theorem inverse_cube_square_eq_sixth {z : ℂ} (h : z ^ 6 = 0 ∨ z ^ 6 = 1) :
    ((z ^ 3)⁻¹) ^ 2 = z ^ 6 := by
  rw [← inv_pow, ← pow_mul]
  norm_num
  rcases h with h | h <;> rw [h] <;> norm_num

/--
@isnad1 id=eq.1h4v.s8.c6a6596f8bb6 from=translated src=- shape=46fe4c5a vocab=3abdcdb5
-/
theorem inverse_square_cube_mask {M : Type*} [Monoid M]
    (ψ : M →* ℂ) (n b : M) (h : ψ b ^ 6 = 0 ∨ ψ b ^ 6 = 1) :
    (ψ (n * b ^ 3))⁻¹ ^ 2 = (ψ n)⁻¹ ^ 2 * ψ b ^ 6 := by
  rw [map_mul, map_pow, mul_inv_rev, mul_pow, inverse_cube_square_eq_sixth h]
  ring

/--
@isnad1 id=le.1h1v.s5.b9875f0ab51f from=translated src=- shape=407790ee vocab=5e02278c
-/
theorem overlap_scalar_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖z ^ 2‖ ≤ 1 := by
  rw [norm_pow]
  simpa using pow_le_pow_left₀ (norm_nonneg z) hz 2

end SevenEighths.InverseMoment

end OAI
