import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_exists_levelOne_qExpansion_eq_map_int_constantCoeff_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_exists_levelOne_qExpansion_eq_map_int_constantCoeff_one

set_option autoImplicit false

open scoped MatrixGroups
open ModularForm EisensteinSeries ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace EMONO

/--
@isnad1 id=eq.0h0v.s4.73dad4d2ed36 from=translated src=- shape=1f14c584 vocab=b8af7fdb
-/
theorem bernoulli_four : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_four]

/--
@isnad1 id=eq.0h0v.s4.dc687b70bc6b from=translated src=- shape=4683683d vocab=6da1d44e
-/
theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  have h5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one, bernoulli'_two,
    bernoulli'_three, bernoulli'_four, h5]
  norm_num [Nat.choose]

/--
@isnad1 id=eq.0h0v.s4.3573b4497d48 from=translated src=- shape=4683683d vocab=511b8776
-/
theorem bernoulli_six : bernoulli 6 = 1 / 42 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six]

noncomputable def P (c : ℤ) (k : ℕ) : PowerSeries ℤ := PowerSeries.mk fun m => if m = 0 then 1 else c * (ArithmeticFunction.sigma k m : ℤ)

/--
@isnad1 id=eq.0h2v.s5.9039019f41d6 from=translated src=- shape=f4860a93 vocab=e6e01e1c
-/
theorem constantCoeff_P (c : ℤ) (k : ℕ) : PowerSeries.constantCoeff (P c k) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, P, PowerSeries.coeff_mk, ite_eq_left rfl]

/--
@isnad1 id=eq.3h2v.s8.9abb8b170a3e from=translated src=- shape=c6c066dd vocab=da06c273
-/
theorem map_P_eq {k : ℕ} (hk : 3 ≤ k) (hk2 : Even k) (c : ℤ) (hc : (c : ℂ) = -(2 * k / bernoulli k : ℂ)) :
    (P c (k - 1)).map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 (⇑(E hk) : UpperHalfPlane → ℂ) := by
  ext m
  rw [PowerSeries.coeff_map, E_qExpansion_coeff hk hk2 m, P, PowerSeries.coeff_mk]
  split_ifs with hm
  · simp
  · simp only [map_mul, eq_intCast, Int.cast_natCast]
    rw [hc]

/--
@isnad1 id=eq.0h0v.s8.07ab15429ecb from=translated src=- shape=7698e0fc vocab=6238316a
-/
theorem map_P4 : (P 240 3).map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 (⇑E₄ : UpperHalfPlane → ℂ) := by
  refine map_P_eq (k := 4) (by norm_num) ⟨2, rfl⟩ 240 ?_
  rw [bernoulli_four]; push_cast; norm_num

/--
@isnad1 id=eq.0h0v.s8.91e2a7e779d7 from=translated src=- shape=ab275673 vocab=062552f3
-/
theorem map_P6 : (P (-504) 5).map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 (⇑E₆ : UpperHalfPlane → ℂ) := by
  refine map_P_eq (k := 6) (by norm_num) ⟨3, rfl⟩ (-504) ?_
  rw [bernoulli_six]; push_cast; norm_num

end EMONO

open EMONO in
/--
@isnad1 id=ex.1h3v.s9.3db980c68d24 from=translated src=- shape=a6f28448 vocab=bb488ec5
-/
theorem solution (a b : ℕ) (e : ℤ)
    (he : 4 * (a : ℤ) + 6 * (b : ℤ) = e) :
    ∃ (E : ModularForm 𝒮ℒ e) (P : PowerSeries ℤ),
      P.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ) ∧
      PowerSeries.constantCoeff P = 1 := by
  have hw : (a : ℤ) * 4 + (b : ℤ) * 6 = e := by rw [← he]; ring
  refine ⟨ModularForm.mcast hw ((E₄.pow a).mul (E₆.pow b)), EMONO.P 240 3 ^ a * EMONO.P (-504) 5 ^ b, ?_, ?_⟩
  · rw [map_mul, map_pow, map_pow, map_P4, map_P6, ModularForm.qExpansion_mcast,
      ModularForm.qExpansion_mul one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL]
  · rw [map_mul, map_pow, map_pow, constantCoeff_P, constantCoeff_P, one_pow, one_pow, one_mul]
