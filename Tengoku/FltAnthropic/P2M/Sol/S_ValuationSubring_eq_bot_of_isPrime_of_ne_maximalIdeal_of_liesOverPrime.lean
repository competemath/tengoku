import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.FltAnthropic.Theorems.Thm_ValuationSubring_exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime

set_option autoImplicit false

/--
@isnad1 id=eq.3h3v.s10.8b5a2f3a8278 from=translated src=- shape=966136fd vocab=559c36f4
-/
theorem solution
    {p : ℕ} (hp : p.Prime) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (𝔮 : Ideal ↥A) [𝔮.IsPrime] (h𝔮 : 𝔮 ≠ IsLocalRing.maximalIdeal ↥A) : 𝔮 = ⊥ := by
  obtain ⟨μ, -, -, hmem⟩ := ValuationSubring.exists_absoluteValue_isNonarchimedean_mem_iff_le_one_of_liesOverPrime hp A hA
  by_contra hne
  apply h𝔮

  refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
  obtain ⟨x, hx𝔮, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  intro y hy
  by_cases hy0 : y = 0
  · rw [hy0]; exact 𝔮.zero_mem

  have hxpos : 0 < μ (x : AlgebraicClosure ℚ) := μ.pos (by exact_mod_cast hx0)
  have hy1 : μ (y : AlgebraicClosure ℚ) < 1 := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy
    by_contra hge
    push_neg at hge
    apply hy
    have hyinv : (y : AlgebraicClosure ℚ)⁻¹ ∈ A := by
      rw [hmem, map_inv₀]
      exact inv_le_one_of_one_le₀ hge
    have hyne : (y : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hy0
    refine IsUnit.of_mul_eq_one ⟨_, hyinv⟩ ?_
    apply Subtype.ext
    show (y : AlgebraicClosure ℚ) * (y : AlgebraicClosure ℚ)⁻¹ = 1
    exact mul_inv_cancel₀ hyne

  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hxpos hy1

  have hq : ((y : AlgebraicClosure ℚ) ^ m * (x : AlgebraicClosure ℚ)⁻¹) ∈ A := by
    rw [hmem, map_mul, map_inv₀, map_pow]
    rw [mul_inv_le_iff₀ hxpos, one_mul]
    exact hm.le
  have hym : y ^ m = x * ⟨_, hq⟩ := by
    apply Subtype.ext
    show ((y : AlgebraicClosure ℚ)) ^ m = (x : AlgebraicClosure ℚ) * ((y : AlgebraicClosure ℚ) ^ m * (x : AlgebraicClosure ℚ)⁻¹)
    have hxne : (x : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hx0
    field_simp
  exact Ideal.IsPrime.mem_of_pow_mem inferInstance m (hym ▸ 𝔮.mul_mem_right _ hx𝔮)
