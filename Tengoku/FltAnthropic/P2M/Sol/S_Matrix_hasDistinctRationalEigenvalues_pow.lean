import Tengoku.FltAnthropic.Definitions.Def_TaylorWiles_Primes
import Tengoku.FltAnthropic.Theorems.Thm_Matrix_trace_pow_eq_sum_pow
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_hasDistinctRationalEigenvalues_pow.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_hasDistinctRationalEigenvalues_pow

open Matrix in
/--
@isnad1 id=hasdisti.4h4v.s8.e06aaa3f891e from=translated src=- shape=803ffa41 vocab=a810e90c
-/
theorem solution {𝕜 : Type*} [Field 𝕜]
    {M : Matrix (Fin 2) (Fin 2) 𝕜} {d : ℕ} (hd : 0 < d) (hM : M ^ d = 1)
    (h : M.HasDistinctRationalEigenvalues) {k : ℕ} (hk : k.Coprime d) :
    (M ^ k).HasDistinctRationalEigenvalues := by
  obtain ⟨α, β, hne, htr, hdet⟩ := h

  have hsum : α ^ d + β ^ d = 2 := by
    have h := Matrix.trace_pow_eq_sum_pow htr hdet d
    rw [hM] at h; simpa [Matrix.trace_one] using h.symm
  have hprod : α ^ d * β ^ d = 1 := by
    have h : (M ^ d).det = α ^ d * β ^ d := by rw [Matrix.det_pow, hdet, mul_pow]
    rw [hM] at h; simpa using h.symm
  have hzero : (α ^ d - 1) * (β ^ d - 1) = 0 := by linear_combination hprod - hsum
  have hαβd : α ^ d = 1 ∧ β ^ d = 1 := by
    rcases mul_eq_zero.mp hzero with h | h
    · have hα : α ^ d = 1 := sub_eq_zero.mp h
      exact ⟨hα, by rwa [hα, one_mul] at hprod⟩
    · have hβ : β ^ d = 1 := sub_eq_zero.mp h
      exact ⟨by rwa [hβ, mul_one] at hprod, hβ⟩
  obtain ⟨hαd, hβd⟩ := hαβd
  have hβ0 : β ≠ 0 := fun h0 => by rw [h0, zero_pow hd.ne'] at hβd; exact zero_ne_one hβd
  refine ⟨α ^ k, β ^ k, ?_, Matrix.trace_pow_eq_sum_pow htr hdet k, by rw [Matrix.det_pow, hdet, mul_pow]⟩
  intro hcontra
  apply hne
  set x : 𝕜 := α * β⁻¹ with hxdef
  have hxk : x ^ k = 1 := by
    rw [hxdef, mul_pow, inv_pow, hcontra, mul_inv_cancel₀ (pow_ne_zero k hβ0)]
  have hxd : x ^ d = 1 := by
    rw [hxdef, mul_pow, inv_pow, hαd, hβd, inv_one, mul_one]
  have hdvd : orderOf x ∣ 1 :=
    hk.gcd_eq_one ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hxk) (orderOf_dvd_of_pow_eq_one hxd)
  have hx1 : x = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  calc α = α * (β⁻¹ * β) := by rw [inv_mul_cancel₀ hβ0, mul_one]
    _ = x * β := by rw [hxdef, mul_assoc]
    _ = β := by rw [hx1, one_mul]
