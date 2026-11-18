import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LaurentSeries_coeff_pow_ringChar_eq_zero_of_not_dvd.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LaurentSeries_coeff_pow_ringChar_eq_zero_of_not_dvd

universe u

set_option autoImplicit false

namespace LaurentSeries
open _root_.LaurentSeries

open HahnSeries

variable {K : Type u} [CommRing K]

/--
@isnad1 id=charp.0h2v.s6.2a0879229479 from=translated src=- shape=b26e66a6 vocab=d41260d6
-/
theorem charP_of_coeff (ℓ : ℕ) [CharP K ℓ] : CharP (LaurentSeries K) ℓ :=
  charP_of_injective_ringHom (HahnSeries.C_injective (Γ := ℤ) (R := K)) ℓ

/--
@isnad1 id=eq.1h4v.s7.5001dc5b103d from=translated src=- shape=e812741a vocab=9982d0b1
-/
theorem coeff_pow_ringChar_eq_zero_of_not_dvd
    (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    (g : LaurentSeries K) (n : ℤ) (hn : ¬ (ℓ : ℤ) ∣ n) :
    (g ^ ℓ).coeff n = 0 := by
  classical
  haveI := charP_of_coeff (K := K) ℓ
  have hℓpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos

  set M : ℤ := max (n + 1) 0 with hM
  have hMn : n < (ℓ : ℤ) * M := by
    rcases le_or_gt 0 (n + 1) with h | h
    · have hM' : M = n + 1 := max_eq_left h
      have h1 : (1 : ℤ) ≤ ℓ := by exact_mod_cast hℓpos
      nlinarith
    · have hM' : M = 0 := max_eq_right (le_of_lt h)
      rw [hM', mul_zero]
      linarith

  set H : LaurentSeries K := ∑ k ∈ Finset.Ico g.order M, HahnSeries.single k (g.coeff k) with hH
  set T : LaurentSeries K := g - H with hT
  have hHcoeff : ∀ k : ℤ, H.coeff k = if k ∈ Finset.Ico g.order M then g.coeff k else 0 := by
    intro k
    rw [hH, HahnSeries.coeff_sum]
    simp_rw [HahnSeries.coeff_single]
    by_cases hk : k ∈ Finset.Ico g.order M
    · rw [ite_eq_left hk, Finset.sum_eq_single k]
      · rw [ite_eq_left rfl]
      · intro b _ hb
        exact ite_eq_right fun h => hb h.symm
      · intro hk'
        exact absurd hk hk'
    · rw [ite_eq_right hk]
      exact Finset.sum_eq_zero fun b hb => ite_eq_right fun h => by rw [h] at hk; exact hk hb
  have hTcoeff : ∀ k : ℤ, k < M → T.coeff k = 0 := by
    intro k hk
    rw [hT, HahnSeries.coeff_sub, hHcoeff]
    split_ifs with hmem
    · exact sub_self _
    · rw [Finset.mem_Ico, not_and_or, not_le] at hmem
      rcases hmem with hlt | hge
      · by_cases hg : g = 0
        · simp [hg]
        · rw [HahnSeries.coeff_eq_zero_of_lt_order hlt, sub_zero]
      · exact absurd hk (not_lt.mpr (le_of_not_gt hge))

  have hTtop : ((M : ℤ) : WithTop ℤ) ≤ T.orderTop :=
    HahnSeries.le_orderTop_iff_forall.mpr fun j hj => hTcoeff j (WithTop.coe_lt_coe.mp hj)
  have hTpow : (T ^ ℓ).coeff n = 0 := by
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    refine lt_of_lt_of_le ?_ HahnSeries.orderTop_nsmul_le_orderTop_pow
    refine lt_of_lt_of_le ?_ (nsmul_le_nsmul_right hTtop ℓ)
    rw [← WithTop.coe_nsmul, WithTop.coe_lt_coe, nsmul_eq_mul]
    exact hMn

  have hHpow : (H ^ ℓ).coeff n = 0 := by
    rw [hH, sum_pow_char]
    simp_rw [HahnSeries.single_pow]
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [HahnSeries.coeff_single_of_ne]
    intro hnk
    apply hn
    rw [hnk, ← natCast_zsmul, smul_eq_mul]
    exact dvd_mul_right _ _

  have hg : g = H + T := by rw [hT, add_sub_cancel]
  rw [hg, add_pow_char, HahnSeries.coeff_add, hHpow, hTpow, add_zero]

end LaurentSeries

/--
@isnad1 id=eq.1h4v.s7.5001dc5b103d from=translated src=- shape=e812741a vocab=9982d0b1
-/
theorem solution
    {K : Type u} [CommRing K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    (g : LaurentSeries K) (n : ℤ) (hn : ¬ (ℓ : ℤ) ∣ n) :
    (g ^ ℓ).coeff n = 0 :=
  LaurentSeries.coeff_pow_ringChar_eq_zero_of_not_dvd ℓ g n hn
