import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.OneSidedPolynomial
import Tengoku.Seed.RingTheory.PowerSeries.Log

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators PowerSeries

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.DenseRegion
open PowerSeries

noncomputable def formalNegLogBase : PowerSeries Real :=
  PowerSeries.mk fun n => if n = 0 then 0 else (n : Real)⁻¹

noncomputable def formalNegLog (u : PowerSeries Real) : PowerSeries Real :=
  formalNegLogBase.subst u

@[simp] theorem coeff_formalNegLogBase (n : Nat) :
    PowerSeries.coeff n formalNegLogBase =
      if n = 0 then 0 else (n : Real)⁻¹ := by
  simp [formalNegLogBase]

@[simp] theorem constantCoeff_formalNegLogBase :
    PowerSeries.constantCoeff formalNegLogBase = 0 := by
  simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem coeff_mk_pow_eq_momentConv (s : Nat → Real) : ∀ r n : Nat,
    PowerSeries.coeff n ((PowerSeries.mk s) ^ r) = momentConv s r n
  | 0, n => by
      cases n <;> simp [momentConv]
  | r + 1, n => by
      rw [momentConv_succ, pow_succ', PowerSeries.coeff_mul]
      simp_rw [PowerSeries.coeff_mk, coeff_mk_pow_eq_momentConv s r]
      exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => s i * momentConv s r j) n

theorem momentConv_eq_zero_of_lt
    {s : Nat → Real} (hs0 : s 0 = 0) : ∀ {r n : Nat}, n < r →
      momentConv s r n = 0
  | 0, n, h => by omega
  | r + 1, n, h => by
      rw [momentConv_succ]
      apply Finset.sum_eq_zero
      intro k hk
      by_cases hk0 : k = 0
      · subst k
        simp [hs0]
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hnkr : n - k < r := by
          have hkn : k ≤ n := by
            have := Finset.mem_range.mp hk
            omega
          omega
        rw [momentConv_eq_zero_of_lt hs0 hnkr]
        simp

theorem coeff_formalNegLog_mk
    {s : Nat → Real} (hs0 : s 0 = 0) (m : Nat) :
    PowerSeries.coeff m (formalNegLog (PowerSeries.mk s)) =
      ∑ k ∈ Finset.range m,
        momentConv s (k + 1) m / (k + 1 : Nat) := by
  have hu : PowerSeries.HasSubst (PowerSeries.mk s) := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simpa [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using hs0
  unfold formalNegLog
  rw [PowerSeries.coeff_subst' hu]
  rw [finsum_eq_sum_of_support_subset
    (s := Finset.range (m + 1))]
  · rw [Finset.sum_range_succ']
    simp only [coeff_formalNegLogBase,
      ite_eq_left, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : k + 1 ≠ 0 := Nat.succ_ne_zero k
    rw [ite_eq_right hk1, coeff_mk_pow_eq_momentConv]
    norm_num [div_eq_mul_inv]
    ring
  · intro d hd
    simp only [Function.mem_support] at hd
    by_contra hmem
    have hmd : m < d := by
      have hnot : ¬ d < m + 1 := by
        intro hdlt
        exact hmem (Finset.mem_range.mpr hdlt)
      omega
    have hzero : PowerSeries.coeff m ((PowerSeries.mk s) ^ d) = 0 := by
      rw [coeff_mk_pow_eq_momentConv,
        momentConv_eq_zero_of_lt hs0 hmd]
    exact hd (by simp [hzero])

theorem derivative_formalNegLogBase :
    PowerSeries.derivative Real formalNegLogBase =
      PowerSeries.mk (fun _ : Nat => (1 : Real)) := by
  ext n
  rw [PowerSeries.coeff_derivative]
  simp only [formalNegLogBase, PowerSeries.coeff_mk,
    Nat.succ_ne_zero, ite_false]
  have hn : ((n + 1 : Nat) : Real) ≠ 0 := by positivity
  field_simp
  push_cast
  rfl

theorem subst_geom_eq_inv_one_sub
    {u : PowerSeries Real} (hu0 : PowerSeries.constantCoeff u = 0) :
    (PowerSeries.mk (fun _ : Nat => (1 : Real))).subst u = (1 - u)⁻¹ := by
  have hu : PowerSeries.HasSubst u :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hu0
  apply (PowerSeries.eq_inv_iff_mul_eq_one (by simp [hu0])).2
  have hsub : (1 - PowerSeries.X : PowerSeries Real).subst u = 1 - u := by
    rw [PowerSeries.subst_sub hu]
    rw [PowerSeries.subst_X hu]
    congr 1
    rw [← PowerSeries.coe_substAlgHom hu]
    exact map_one _
  rw [← hsub, ← PowerSeries.subst_mul hu,
    show PowerSeries.mk (fun _ : Nat => (1 : Real)) =
      PowerSeries.mk (1 : Nat → Real) by rfl,
    PowerSeries.mk_one_mul_one_sub_eq_one Real]
  rw [← PowerSeries.coe_substAlgHom hu]
  exact map_one _

@[simp] theorem constantCoeff_formalNegLog
    {u : PowerSeries Real} (hu0 : PowerSeries.constantCoeff u = 0) :
    PowerSeries.constantCoeff (formalNegLog u) = 0 := by
  unfold formalNegLog
  exact PowerSeries.constantCoeff_subst_eq_zero hu0 _
    constantCoeff_formalNegLogBase

noncomputable def unsignedUCoeff
    (p : Real) (s : Nat → Real) (n : Nat) : Real :=
  if 2 ≤ n then
    ∑ j ∈ Finset.range (n - 1), p ^ (n - 2 - j) * s j
  else 0

@[simp] theorem unsignedUCoeff_zero (p : Real) (s : Nat → Real) :
    unsignedUCoeff p s 0 = 0 := by simp [unsignedUCoeff]

end OddCycleBound.IntermediateRegion
