import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Normalized complex derivatives used at the polynomial endpoint.
-/

namespace PiIrrationality

noncomputable def normalizedComplexDeriv (k : ℕ) (f : ℂ → ℂ) (x : ℂ) : ℂ :=
  iteratedDeriv k f x / (k.factorial : ℂ)

theorem normalizedComplexDeriv_const_mul (k : ℕ) (c : ℂ) (f : ℂ → ℂ) (x : ℂ) :
    normalizedComplexDeriv k (fun t => c * f t) x =
      c * normalizedComplexDeriv k f x := by
  unfold normalizedComplexDeriv
  rw [iteratedDeriv_const_mul_field]
  ring

theorem normalizedComplexDeriv_add (k : ℕ) (f g : ℂ → ℂ) (x : ℂ)
    (hf : ContDiffAt ℂ k f x) (hg : ContDiffAt ℂ k g x) :
    normalizedComplexDeriv k (fun t => f t + g t) x =
      normalizedComplexDeriv k f x + normalizedComplexDeriv k g x := by
  unfold normalizedComplexDeriv
  rw [iteratedDeriv_fun_add hf hg, add_div]

theorem normalizedComplexDeriv_sum {ι : Type*} (S : Finset ι)
    (k : ℕ) (f : ι → ℂ → ℂ) (x : ℂ)
    (hf : ∀ i ∈ S, ContDiffAt ℂ k (f i) x) :
    normalizedComplexDeriv k (fun t => ∑ i ∈ S, f i t) x =
      ∑ i ∈ S, normalizedComplexDeriv k (f i) x := by
  unfold normalizedComplexDeriv
  rw [iteratedDeriv_fun_sum hf, Finset.sum_div]

theorem normalizedComplexDeriv_shift_power (k m : ℕ) (x : ℂ) :
    normalizedComplexDeriv k (fun t : ℂ => (t - x) ^ m) x =
      if k = m then 1 else 0 := by
  unfold normalizedComplexDeriv
  rw [iteratedDeriv_comp_sub_const k (fun t : ℂ => t ^ m) x]
  simp only [sub_self, iteratedDeriv_fun_pow_zero]
  split_ifs with h
  · subst m
    simp [Nat.factorial_ne_zero]
  · simp

theorem iteratedDeriv_shift_power_mul_zero (k m : ℕ) (hkm : k < m)
    (f : ℂ → ℂ) (x : ℂ) (hf : ContDiffAt ℂ k f x) :
    iteratedDeriv k (fun t : ℂ => (t - x) ^ m * f t) x = 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hf]
  apply Finset.sum_eq_zero
  intro i hi
  have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [iteratedDeriv_comp_sub_const i (fun t : ℂ => t ^ m) x]
  simp only [sub_self, iteratedDeriv_fun_pow_zero, ite_eq_right (by omega : i ≠ m),
    Nat.cast_zero, mul_zero, zero_mul]

theorem negative_ascending_product (j k : ℕ) :
    (∏ i ∈ Finset.range k, (-(j + 1 : ℂ) - i)) =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) * ((j + k).choose k : ℂ) := by
  have hp : (∏ i ∈ Finset.range k, (-(j + 1 : ℂ) - i)) =
      (-1 : ℂ) ^ k * ((j + 1).ascFactorial k : ℂ) := by
    rw [Nat.ascFactorial_eq_prod_range]
    push_cast
    have hneg : (-1 : ℂ) ^ k = ∏ _i ∈ Finset.range k, (-1 : ℂ) := by simp
    rw [hneg, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    ring
  rw [hp, Nat.ascFactorial_eq_factorial_mul_choose]
  push_cast
  ring

theorem normalizedComplexDeriv_inv_power (j k : ℕ) (x : ℂ) :
    normalizedComplexDeriv k (fun t : ℂ => 1 / t ^ (j + 1)) x =
      (-1 : ℂ) ^ k * ((j + k).choose k : ℂ) / x ^ (j + k + 1) := by
  have hfun : (fun t : ℂ => 1 / t ^ (j + 1)) =
      (fun t : ℂ => t ^ (-((j + 1 : ℕ) : ℤ))) := by
    simp only [one_div, zpow_neg, zpow_natCast]
  rw [hfun]
  unfold normalizedComplexDeriv
  rw [iteratedDeriv_eq_iterate, iter_deriv_zpow]
  simp only [Int.cast_neg, Int.cast_natCast, Int.cast_add, Int.cast_one,
    Nat.cast_add, Nat.cast_one]
  rw [negative_ascending_product]
  have he : -((j : ℤ) + 1) - k = -((j + k + 1 : ℕ) : ℤ) := by omega
  rw [he, zpow_neg, zpow_natCast]
  have hk : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

theorem normalizedComplexDeriv_inv_add (j k : ℕ) (a x : ℂ) :
    normalizedComplexDeriv k (fun t : ℂ => 1 / (a + t) ^ (j + 1)) x =
      (-1 : ℂ) ^ k * ((j + k).choose k : ℂ) / (a + x) ^ (j + k + 1) := by
  unfold normalizedComplexDeriv
  rw [iteratedDeriv_comp_const_add k (fun t : ℂ => 1 / t ^ (j + 1)) a]
  exact normalizedComplexDeriv_inv_power j k (a + x)

theorem normalizedComplexDeriv_inv_sub (j k : ℕ) (a x : ℂ) :
    normalizedComplexDeriv k (fun t : ℂ => 1 / (a - t) ^ (j + 1)) x =
      ((j + k).choose k : ℂ) / (a - x) ^ (j + k + 1) := by
  unfold normalizedComplexDeriv
  rw [iteratedDeriv_comp_const_sub k (fun t : ℂ => 1 / t ^ (j + 1)) a]
  simp only [smul_eq_mul, mul_div_assoc]
  change (-1 : ℂ) ^ k * normalizedComplexDeriv k (fun t : ℂ => 1 / t ^ (j + 1)) (a - x) = _
  rw [normalizedComplexDeriv_inv_power]
  rw [← mul_div_assoc, ← mul_assoc, ← mul_pow]
  norm_num

end PiIrrationality
