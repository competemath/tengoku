import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_forall_coeff_mem_of_forall_coeff_aeval_jqModC_mem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_forall_coeff_mem_of_forall_coeff_aeval_jqModC_mem

set_option autoImplicit false

open Polynomial ModularCurve

namespace GaussJE96

variable {L : Type*} [Field L]

/--
@isnad1 id=eq.0h2v.s8.95b9a8f56831 from=translated src=- shape=b940b4d3 vocab=90248186
-/
theorem algebraMap_laurent (c : L) : algebraMap L (LaurentSeries L) c = HahnSeries.C c := by
  rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
  show HahnSeries.ofPowerSeries ℤ L (algebraMap L (PowerSeries L) c) = _
  rw [← PowerSeries.C_eq_algebraMap, HahnSeries.ofPowerSeries_C]

/--
@isnad1 id=eq.0h4v.s8.adcc7066c337 from=translated src=- shape=81c0896b vocab=c79dce3e
-/
theorem coeff_algebraMap_mul (c : L) (x : LaurentSeries L) (m : ℤ) :
    (algebraMap L (LaurentSeries L) c * x).coeff m = c * x.coeff m := by
  rw [algebraMap_laurent, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

/--
@isnad1 id=eq.0h2v.s9.fa1f86c2d593 from=translated src=- shape=570812bc vocab=0f93e434
-/
theorem jqModC_pow (n : ℕ) :
    jqModC L ^ n = HahnSeries.single (-(n : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ L ((jNum ^ n).map (Int.castRingHom L)) := by
  rw [jqModC, mul_pow, HahnSeries.single_pow, one_pow, ← map_pow, ← map_pow]
  congr 2
  simp

/--
@isnad1 id=eq.0h3v.s8.6a48cd80d118 from=translated src=- shape=b1dc3855 vocab=a3d7c61c
-/
theorem coeff_jqModC_pow (n : ℕ) (m : ℤ) :
    (jqModC L ^ n).coeff m =
      if m + n < 0 then 0 else (((jNum ^ n).coeff (m + n).toNat : ℤ) : L) := by
  rw [jqModC_pow]
  have hm : m = (m + n) + (-(n : ℤ)) := by ring
  conv_lhs => rw [hm]
  rw [HahnSeries.coeff_single_mul_add, one_mul]
  split_ifs with hlt
  · exact ofPowerSeries_coeff_of_neg _ hlt
  · have h0 : 0 ≤ m + n := by omega
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le h0
    rw [hk, Int.toNat_natCast]
    rw [show ((k : ℕ) : ℤ) = (k : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
      eq_intCast]

/--
@isnad1 id=eq.1h3v.s7.8c4f368a6db8 from=translated src=- shape=d2e98f52 vocab=ee0679fb
-/
theorem coeff_jqModC_pow_of_lt {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) : (jqModC L ^ n).coeff m = 0 := by
  rw [coeff_jqModC_pow, ite_eq_left (by omega)]

/--
@isnad1 id=eq.0h2v.s7.38b11c23a55e from=translated src=- shape=91cba0af vocab=f0d4729d
-/
theorem coeff_jqModC_pow_self (n : ℕ) : (jqModC L ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [coeff_jqModC_pow, ite_eq_right (by omega)]
  have : (-(n : ℤ) + n).toNat = 0 := by simp
  rw [this, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_jNum, one_pow, Int.cast_one]

/--
@isnad1 id=mem.0h4v.s7.12fd68d8c59e from=translated src=- shape=f8abc195 vocab=ae217721
-/
theorem coeff_jqModC_pow_mem (R : Subring L) (n : ℕ) (m : ℤ) : (jqModC L ^ n).coeff m ∈ R := by
  rw [coeff_jqModC_pow]
  split_ifs
  · exact R.zero_mem
  · exact intCast_mem R _

/--
@isnad1 id=eq.0h5v.s6.cb58b2963db8 from=translated src=- shape=6f63ef8d vocab=19f158d2
-/
theorem coeff_finset_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries L) (m : ℤ) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, HahnSeries.coeff_add, ih]

/--
@isnad1 id=eq.0h3v.s9.7f7a38464853 from=translated src=- shape=b9dcc0b9 vocab=87e7eb6f
-/
theorem coeff_aeval (P : Polynomial L) (m : ℤ) :
    (aeval (jqModC L) P).coeff m = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * (jqModC L ^ i).coeff m := by
  conv_lhs => rw [aeval_eq_sum_range]
  rw [coeff_finset_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, coeff_algebraMap_mul]

/--
@isnad1 id=eq.0h2v.s8.1ba80e6c38a8 from=translated src=- shape=7839dc2a vocab=1597e4ca
-/
theorem coeff_aeval_neg_natDegree (P : Polynomial L) :
    (aeval (jqModC L) P).coeff (-(P.natDegree : ℤ)) = P.leadingCoeff := by
  rw [coeff_aeval, Finset.sum_eq_single_of_mem P.natDegree (Finset.mem_range.mpr (Nat.lt_succ_self _))]
  · rw [coeff_jqModC_pow_self, mul_one]; rfl
  · intro i hi hne
    have hi' : i < P.natDegree := by rw [Finset.mem_range] at hi; omega
    rw [coeff_jqModC_pow_of_lt (by omega), mul_zero]

/--
@isnad1 id=eq.1h3v.s8.99efb1fe61e0 from=translated src=- shape=4710c6d8 vocab=dad77bc1
-/
theorem coeff_aeval_of_lt (P : Polynomial L) {m : ℤ} (hm : m < -(P.natDegree : ℤ)) :
    (aeval (jqModC L) P).coeff m = 0 := by
  rw [coeff_aeval]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [coeff_jqModC_pow_of_lt (by omega), mul_zero]

/--
@isnad1 id=mem.2h5v.s8.053f1c7ffff3 from=translated src=- shape=3b2c4ca3 vocab=efd2919e
-/
theorem coeff_mem (R : Subring L) : ∀ (N : ℕ) (P : Polynomial L), P.natDegree ≤ N →
    (∀ n : ℤ, (aeval (jqModC L) P).coeff n ∈ R) → ∀ i : ℕ, P.coeff i ∈ R := by
  intro N
  induction N with
  | zero =>
    intro P hP h i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · have h0 := h 0
      have hlead := coeff_aeval_neg_natDegree (L := L) P
      rw [Nat.le_zero.mp hP] at hlead
      simp only [Nat.cast_zero, neg_zero] at hlead
      rw [hlead] at h0
      rw [Polynomial.leadingCoeff, Nat.le_zero.mp hP] at h0
      exact h0
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact R.zero_mem
  | succ N ih =>
    intro P hP h i

    have htop : P.coeff (N + 1) ∈ R := by
      by_cases hdeg : P.natDegree = N + 1
      · have h1 := h (-((N + 1 : ℕ) : ℤ))
        rw [← hdeg, coeff_aeval_neg_natDegree] at h1
        rw [← hdeg]; exact h1
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact R.zero_mem

    set c := P.coeff (N + 1) with hc
    set P' := P - C c * X ^ (N + 1) with hP'
    have hP'coeff : ∀ i, P'.coeff i = if i = N + 1 then 0 else P.coeff i := by
      intro i
      rw [hP', coeff_sub, coeff_C_mul_X_pow]
      split_ifs with hi
      · rw [hi, hc, sub_self]
      · rw [sub_zero]
    have hP'deg : P'.natDegree ≤ N := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro i hi
      rw [hP'coeff]
      split_ifs with hi'
      · rfl
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
    have hP'aeval : ∀ n : ℤ, (aeval (jqModC L) P').coeff n ∈ R := by
      intro n
      have : aeval (jqModC L) P' = aeval (jqModC L) P - algebraMap L (LaurentSeries L) c * jqModC L ^ (N + 1) := by
        rw [hP', map_sub, map_mul, aeval_C, map_pow, aeval_X]
      rw [this, HahnSeries.coeff_sub, coeff_algebraMap_mul]
      exact R.sub_mem (h n) (R.mul_mem htop (coeff_jqModC_pow_mem R _ _))
    have hIH := ih P' hP'deg hP'aeval
    by_cases hi : i = N + 1
    · rw [hi]; exact htop
    · have := hIH i
      rw [hP'coeff, ite_eq_right hi] at this
      exact this

end GaussJE96

/--
@isnad1 id=and.1h3v.s9.1fe224165e88 from=translated src=- shape=529e5d2a vocab=c8e6c1b2
-/
theorem solution
    {L : Type*} [Field L] (R : Subring L) (P : Polynomial L)
    (h : ∀ n : ℤ, (Polynomial.aeval (ModularCurve.jqModC L) P).coeff n ∈ R) :
    (∀ i : ℕ, P.coeff i ∈ R) ∧
      (P ≠ 0 → (Polynomial.aeval (ModularCurve.jqModC L) P).order = -(P.natDegree : ℤ)) := by
  classical
  refine ⟨GaussJE96.coeff_mem R P.natDegree P le_rfl h, fun hP => ?_⟩
  have hlead : (aeval (jqModC L) P).coeff (-(P.natDegree : ℤ)) ≠ 0 := by
    rw [GaussJE96.coeff_aeval_neg_natDegree]; exact leadingCoeff_ne_zero.mpr hP
  have hne : aeval (jqModC L) P ≠ 0 := fun h0 => hlead (by rw [h0]; rfl)
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero hlead
  · by_contra hlt
    push Not at hlt
    exact hne (HahnSeries.coeff_order_eq_zero.mp (GaussJE96.coeff_aeval_of_lt P hlt))
