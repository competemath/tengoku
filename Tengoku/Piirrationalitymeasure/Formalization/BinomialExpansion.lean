import Tengoku
import Tengoku.Piirrationalitymeasure.Formalization.Laurent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Finite combinatorial data for the normalized Leibniz expansion (2.9)--(2.11).
The expansion is indexed explicitly so that denominator and valuation lemmas
can inspect each summand rather than treating the Laurent coefficients as
opaque analytic objects.
-/

namespace PiIrrationality

structure LeibnizIndex (n : ℕ) where
  m0 : ℕ
  m1 : ℕ
  m2 : ℕ
  m3 : ℕ
  m4 : ℕ
  m5 : ℕ

def NestedIndexConditions (n i j k r s : ℕ) : Prop :=
  s ≤ r ∧ r ≤ k ∧ k ≤ j ∧ j ≤ i ∧ i ≤ n

theorem nestedIndexConditions_iff_mem_ranges (n i j k r s : ℕ) :
    NestedIndexConditions n i j k r s ↔
      i ∈ Finset.range (n + 1) ∧ j ∈ Finset.range (i + 1) ∧
        k ∈ Finset.range (j + 1) ∧ r ∈ Finset.range (k + 1) ∧
          s ∈ Finset.range (r + 1) := by
  simp [NestedIndexConditions]
  omega

def nestedDerivativeAllocation (n i j k r s : ℕ) : LeibnizIndex n :=
  ⟨s, r - s, k - r, j - k, i - j, n - i⟩

theorem nestedDerivativeAllocation_valid (n i j k r s : ℕ)
    (h : NestedIndexConditions n i j k r s) :
    (nestedDerivativeAllocation n i j k r s).m0 +
        (nestedDerivativeAllocation n i j k r s).m1 +
        (nestedDerivativeAllocation n i j k r s).m2 +
        (nestedDerivativeAllocation n i j k r s).m3 +
        (nestedDerivativeAllocation n i j k r s).m4 +
        (nestedDerivativeAllocation n i j k r s).m5 = n := by
  rcases h with ⟨hsr, hrk, hkj, hji, hin⟩
  simp [nestedDerivativeAllocation]
  omega

/-- Principal-part allocation convention, corresponding to the paper when `0 ≤ j`.-/
def LeibnizIndex.Valid (n : ℕ) (j : ℤ) (m : LeibnizIndex n) : Prop :=
  m.m0 + m.m1 + m.m2 + m.m3 + m.m4 + m.m5 = 5570 * n - j.toNat ∧
  m.m1 ≤ 2 * 1857 * n ∧
  m.m2 ≤ 3714 * n ∧
  m.m3 ≤ 3714 * n ∧
  m.m4 ≤ 3714 * n ∧
  m.m5 ≤ 3714 * n

def nestedLaurentAllocation (n : ℕ) (j : ℤ)
    (i j' k r s : ℕ) : LeibnizIndex n :=
  ⟨s, r - s, k - r, j' - k, i - j', 5570 * n - j.toNat - i⟩

theorem nestedLaurentAllocation_valid (n : ℕ) (j : ℤ)
    (i j' k r s : ℕ)
    (hcond : NestedIndexConditions (5570 * n - j.toNat) i j' k r s)
    (hm1 : r - s ≤ 2 * 1857 * n)
    (hm2 : k - r ≤ 3714 * n)
    (hm3 : j' - k ≤ 3714 * n)
    (hm4 : i - j' ≤ 3714 * n)
    (hm5 : 5570 * n - j.toNat - i ≤ 3714 * n) :
    LeibnizIndex.Valid n j (nestedLaurentAllocation n j i j' k r s) := by
  rcases hcond with ⟨hsr, hrk, hki, hij, hiN⟩
  have hsum : s + (r - s) + (k - r) + (j' - k) + (i - j') +
      (5570 * n - j.toNat - i) = 5570 * n - j.toNat := by
    omega
  dsimp [LeibnizIndex.Valid, nestedLaurentAllocation]
  refine ⟨hsum, hm1, hm2, hm3, hm4, hm5⟩

def binomialWeight (n : ℕ) (m : LeibnizIndex n) : ℕ :=
  (Nat.choose (5570 * n + m.m0) m.m0) *
  (Nat.choose (2 * 1857 * n) m.m1) *
  (Nat.choose (3714 * n) m.m2) *
  (Nat.choose (3714 * n) m.m3) *
  (Nat.choose (3714 * n) m.m4) *
  (Nat.choose (3714 * n) m.m5)

def gaussianTwoExponent (n : ℕ) (j : ℤ) (m : LeibnizIndex n) : ℤ :=
  (10 * 3714 - 4 * 5570 : ℤ) * n + 2 * j.toNat +
    2 * m.m1 - m.m4 - m.m5 - 2

theorem gaussianTwoExponent_eq_doubled_base_sub
    (n : ℕ) (j : ℤ) (m : LeibnizIndex n) :
    gaussianTwoExponent n j m =
      2 * ((5 * 3714 - 2 * 5570 : ℤ) * n - 1 + j.toNat + m.m1) -
        m.m4 - m.m5 := by
  dsimp [gaussianTwoExponent]
  norm_num
  ring

theorem gaussianTwoExponent_lower (n : ℕ) (j : ℤ) (m : LeibnizIndex n)
    (hm : LeibnizIndex.Valid n j m)
    (hjrange : j.toNat ≤ 5570 * n) :
    2 * 4645 * n + 3 * j.toNat - 2 ≤ gaussianTwoExponent n j m := by
  rcases hm with ⟨hsum, hm1, hm2, hm3, hm4, hm5⟩
  have hrest : m.m4 + m.m5 ≤ 5570 * n - j.toNat := by
    calc
      m.m4 + m.m5 ≤ m.m0 + m.m1 + m.m2 + m.m3 + m.m4 + m.m5 := by omega
      _ = 5570 * n - j.toNat := hsum
  have hrestZ : (m.m4 : ℤ) + (m.m5 : ℤ) ≤
      (5570 : ℤ) * n - j.toNat := by
    have hcast : ((5570 * n - j.toNat : ℕ) : ℤ) =
        (5570 : ℤ) * n - j.toNat := by
      rw [Nat.cast_sub hjrange]
      norm_num
    exact hcast ▸ (by exact_mod_cast hrest)
  dsimp [gaussianTwoExponent]
  norm_num at *
  omega

def fiveExponent (n : ℕ) (j : ℤ) : ℤ :=
  2 * (1857 + 3714 - 5570 : ℤ) * n + j.toNat

theorem fiveExponent_lower (n : ℕ) (j : ℤ) :
    2 * n ≤ fiveExponent n j := by
  dsimp [fiveExponent]
  norm_num

theorem gaussianTwoExponent_nonneg (n : ℕ) (j : ℤ) (m : LeibnizIndex n)
    (hm : LeibnizIndex.Valid n j m) (hn : 1 ≤ n)
    (hjrange : j.toNat ≤ 5570 * n) :
    0 ≤ gaussianTwoExponent n j m := by
  have h := gaussianTwoExponent_lower n j m hm hjrange
  omega

theorem fiveExponent_nonneg (n : ℕ) (j : ℤ) (hn : 1 ≤ n) :
    0 ≤ fiveExponent n j := by
  have h := fiveExponent_lower n j
  omega

def zeroLeibnizIndex (n : ℕ) : LeibnizIndex n :=
  ⟨0, 0, 0, 0, 0, 0⟩

theorem zeroLeibnizIndex_valid_top (n : ℕ) :
    LeibnizIndex.Valid n (5570 * n : ℤ) (zeroLeibnizIndex n) := by
  have hj : (5570 * n : ℤ).toNat = 5570 * n := by
    omega
  simp [LeibnizIndex.Valid, zeroLeibnizIndex, hj]

theorem zeroLeibnizIndex_weight (n : ℕ) :
    binomialWeight n (zeroLeibnizIndex n) = 1 := by
  simp [binomialWeight, zeroLeibnizIndex]

noncomputable def normalizedPowerDeriv (m k : ℕ) (x : ℝ) : ℝ :=
  iteratedDeriv k (fun y : ℝ => y ^ m) x / k.factorial

theorem normalizedPowerDeriv_eq_choose (m k : ℕ) (x : ℝ) (hk : k ≤ m) :
    normalizedPowerDeriv m k x = (m.choose k : ℝ) * x ^ (m - k) := by
  unfold normalizedPowerDeriv
  rw [iteratedDeriv_pow, Nat.descFactorial_eq_factorial_mul_choose]
  field_simp
  simp [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm]

theorem normalizedPowerDeriv_eq_zero (m k : ℕ) (x : ℝ) (hkm : m < k) :
    normalizedPowerDeriv m k x = 0 := by
  unfold normalizedPowerDeriv
  rw [iteratedDeriv_pow]
  rw [Nat.descFactorial_of_lt hkm]
  simp

theorem normalizedPowerDeriv_eq_choose_or_zero (m k : ℕ) (x : ℝ) :
    normalizedPowerDeriv m k x =
      if k ≤ m then (m.choose k : ℝ) * x ^ (m - k) else 0 := by
  by_cases hkm : k ≤ m
  · simp [hkm, normalizedPowerDeriv_eq_choose m k x hkm]
  · have hmk : m < k := Nat.lt_of_not_ge hkm
    simp [hkm, normalizedPowerDeriv_eq_zero m k x hmk]

theorem normalizedDeriv_mul {n : ℕ} {f g : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x) :
    normalizedDeriv n (fun y => f y * g y) x =
      ∑ i ∈ Finset.range (n + 1),
        normalizedDeriv i f x * normalizedDeriv (n - i) g x := by
  unfold normalizedDeriv
  change iteratedDeriv n (f * g) x / n.factorial = _
  rw [iteratedDeriv_mul hf hg]
  apply (div_eq_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))).2
  conv_rhs =>
    rw [Finset.sum_mul (s := Finset.range (n + 1))]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hchoose := Nat.choose_mul_factorial_mul_factorial hi'
  have hchooseR : (n.choose i : ℝ) * (i.factorial : ℝ) *
      ((n - i).factorial : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast hchoose
  field_simp
  calc
    (n.choose i : ℝ) * iteratedDeriv i f x * iteratedDeriv (n - i) g x *
        (i.factorial : ℝ) * (n - i).factorial =
      (iteratedDeriv i f x * iteratedDeriv (n - i) g x) *
        ((n.choose i : ℝ) * (i.factorial : ℝ) * (n - i).factorial) := by ring
    _ = (iteratedDeriv i f x * iteratedDeriv (n - i) g x) *
        (n.factorial : ℝ) := by rw [hchooseR]

theorem normalizedDeriv_mul_three {n : ℕ} {f g h : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hh : ContDiffAt ℝ n h x) :
    normalizedDeriv n (fun y => f y * g y * h y) x =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (i + 1),
          normalizedDeriv j f x * normalizedDeriv (i - j) g x *
            normalizedDeriv (n - i) h x := by
  have hfg : ContDiffAt ℝ n (fun y => f y * g y) x := hf.mul hg
  rw [show (fun y => f y * g y * h y) =
      (fun y => (f y * g y) * h y) by rfl]
  rw [normalizedDeriv_mul hfg hh]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hfi : ContDiffAt ℝ i f x := hf.of_le (by exact_mod_cast hi')
  have hgi : ContDiffAt ℝ i g x := hg.of_le (by exact_mod_cast hi')
  rw [normalizedDeriv_mul hfi hgi]
  rw [Finset.sum_mul]

theorem normalizedDeriv_mul_four {n : ℕ} {f g h l : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hh : ContDiffAt ℝ n h x) (hl : ContDiffAt ℝ n l x) :
    normalizedDeriv n (fun y => f y * g y * h y * l y) x =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (i + 1),
          ∑ k ∈ Finset.range (j + 1),
            normalizedDeriv k f x * normalizedDeriv (j - k) g x *
              normalizedDeriv (i - j) h x * normalizedDeriv (n - i) l x := by
  have hfgh : ContDiffAt ℝ n (fun y => f y * g y * h y) x :=
    (hf.mul hg).mul hh
  rw [show (fun y => f y * g y * h y * l y) =
      (fun y => (f y * g y * h y) * l y) by rfl]
  rw [normalizedDeriv_mul hfgh hl]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hfi : ContDiffAt ℝ i f x := hf.of_le (by exact_mod_cast hi')
  have hgi : ContDiffAt ℝ i g x := hg.of_le (by exact_mod_cast hi')
  have hhi : ContDiffAt ℝ i h x := hh.of_le (by exact_mod_cast hi')
  rw [normalizedDeriv_mul_three hfi hgi hhi]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul]

theorem normalizedDeriv_mul_five {n : ℕ} {f g h l u : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hh : ContDiffAt ℝ n h x) (hl : ContDiffAt ℝ n l x)
    (hu : ContDiffAt ℝ n u x) :
    normalizedDeriv n (fun y => f y * g y * h y * l y * u y) x =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (i + 1),
          ∑ k ∈ Finset.range (j + 1),
            ∑ r ∈ Finset.range (k + 1),
              normalizedDeriv r f x * normalizedDeriv (k - r) g x *
                normalizedDeriv (j - k) h x * normalizedDeriv (i - j) l x *
                normalizedDeriv (n - i) u x := by
  have hfghl : ContDiffAt ℝ n (fun y => f y * g y * h y * l y) x :=
    ((hf.mul hg).mul hh).mul hl
  rw [show (fun y => f y * g y * h y * l y * u y) =
      (fun y => (f y * g y * h y * l y) * u y) by rfl]
  rw [normalizedDeriv_mul hfghl hu]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hfi : ContDiffAt ℝ i f x := hf.of_le (by exact_mod_cast hi')
  have hgi : ContDiffAt ℝ i g x := hg.of_le (by exact_mod_cast hi')
  have hhi : ContDiffAt ℝ i h x := hh.of_le (by exact_mod_cast hi')
  have hli : ContDiffAt ℝ i l x := hl.of_le (by exact_mod_cast hi')
  rw [normalizedDeriv_mul_four hfi hgi hhi hli]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_mul]

theorem normalizedDeriv_mul_six {n : ℕ} {f g h l u v : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hh : ContDiffAt ℝ n h x) (hl : ContDiffAt ℝ n l x)
    (hu : ContDiffAt ℝ n u x) (hv : ContDiffAt ℝ n v x) :
    normalizedDeriv n (fun y => f y * g y * h y * l y * u y * v y) x =
      ∑ i ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (i + 1),
          ∑ k ∈ Finset.range (j + 1),
            ∑ r ∈ Finset.range (k + 1),
              ∑ s ∈ Finset.range (r + 1),
                normalizedDeriv s f x * normalizedDeriv (r - s) g x *
                  normalizedDeriv (k - r) h x * normalizedDeriv (j - k) l x *
                  normalizedDeriv (i - j) u x * normalizedDeriv (n - i) v x := by
  have hfghlu : ContDiffAt ℝ n (fun y => f y * g y * h y * l y * u y) x :=
    (((hf.mul hg).mul hh).mul hl).mul hu
  rw [show (fun y => f y * g y * h y * l y * u y * v y) =
      (fun y => (f y * g y * h y * l y * u y) * v y) by rfl]
  rw [normalizedDeriv_mul hfghlu hv]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hfi : ContDiffAt ℝ i f x := hf.of_le (by exact_mod_cast hi')
  have hgi : ContDiffAt ℝ i g x := hg.of_le (by exact_mod_cast hi')
  have hhi : ContDiffAt ℝ i h x := hh.of_le (by exact_mod_cast hi')
  have hli : ContDiffAt ℝ i l x := hl.of_le (by exact_mod_cast hi')
  have hui : ContDiffAt ℝ i u x := hu.of_le (by exact_mod_cast hi')
  rw [normalizedDeriv_mul_five hfi hgi hhi hli hui]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_mul]

theorem normalizedDeriv_regularizedZpowCore (n k : ℕ) :
    normalizedDeriv k (regularizedZpowCore n) (-5) =
      ∑ i ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range (i + 1),
          ∑ r ∈ Finset.range (j + 1),
            normalizedDeriv r (fun t : ℝ => t ^ (2 * 1857 * n)) (-5) *
              normalizedDeriv (j - r)
                (fun t : ℝ => (((t + 1)^2 + 4) ^ (3714 * n))) (-5) *
              normalizedDeriv (i - j)
                (fun t : ℝ => (((t - 1)^2 + 4) ^ (3714 * n))) (-5) *
              normalizedDeriv (k - i)
                (fun t : ℝ => (5 - t) ^ (-(5570 * n + 1) : ℤ)) (-5) := by
  have hf : ContDiffAt ℝ k
      (fun t : ℝ => t ^ (2 * 1857 * n)) (-5) := by fun_prop
  have hg : ContDiffAt ℝ k
      (fun t : ℝ => (((t + 1)^2 + 4) ^ (3714 * n))) (-5) := by fun_prop
  have hh : ContDiffAt ℝ k
      (fun t : ℝ => (((t - 1)^2 + 4) ^ (3714 * n))) (-5) := by fun_prop
  have hl : ContDiffAt ℝ k
      (fun t : ℝ => (5 - t) ^ (-(5570 * n + 1) : ℤ)) (-5) := by
    change ContDiffAt ℝ k
      (fun t : ℝ => (5 - t) ^ (-((5570 * n + 1 : ℕ) : ℤ))) (-5)
    have hi : ContDiffAt ℝ k
        (fun t : ℝ => ((5 - t) ^ (5570 * n + 1))⁻¹) (-5) := by
      fun_prop (disch := norm_num)
    simpa only [zpow_neg, zpow_natCast] using hi
  change normalizedDeriv k (fun t : ℝ =>
      t ^ (2 * 1857 * n) * (((t + 1)^2 + 4) ^ (3714 * n)) *
        (((t - 1)^2 + 4) ^ (3714 * n)) *
        (5 - t) ^ (-(5570 * n + 1) : ℤ)) (-5) = _
  rw [normalizedDeriv_mul_four hf hg hh hl]

theorem laurentCoeff_expansion_real (n : ℕ) (j : ℤ)
    (hj : 0 ≤ j ∧ j ≤ 5570 * n) :
    laurentCoeff n j =
      5 * (∑ i ∈ Finset.range (5570 * n - j.toNat + 1),
        ∑ j' ∈ Finset.range (i + 1),
          ∑ r ∈ Finset.range (j' + 1),
            normalizedDeriv r (fun t : ℝ => t ^ (2 * 1857 * n)) (-5) *
              normalizedDeriv (j' - r)
                (fun t : ℝ => (((t + 1)^2 + 4) ^ (3714 * n))) (-5) *
              normalizedDeriv (i - j')
                (fun t : ℝ => (((t - 1)^2 + 4) ^ (3714 * n))) (-5) *
              normalizedDeriv (5570 * n - j.toNat - i)
                (fun t : ℝ => (5 - t) ^ (-(5570 * n + 1) : ℤ)) (-5)) := by
  rw [laurentCoeff_eq_normalizedZpowCore n j hj]
  rw [normalizedDeriv_regularizedZpowCore]

theorem laurentCoeff_expansion_real_complete (n : ℕ) (j : ℤ)
    (hj : j ≤ 5570 * (n : ℤ)) :
    let k := (5570 * (n : ℤ) - j).toNat
    laurentCoeff n j =
      5 * (∑ i ∈ Finset.range (k + 1),
        ∑ j' ∈ Finset.range (i + 1),
          ∑ r ∈ Finset.range (j' + 1),
            normalizedDeriv r (fun t : ℝ => t ^ (2 * 1857 * n)) (-5) *
              normalizedDeriv (j' - r)
                (fun t : ℝ => (((t + 1)^2 + 4) ^ (3714 * n))) (-5) *
              normalizedDeriv (i - j')
                (fun t : ℝ => (((t - 1)^2 + 4) ^ (3714 * n))) (-5) *
              normalizedDeriv (k - i)
                (fun t : ℝ => (5 - t) ^ (-(5570 * n + 1) : ℤ)) (-5)) := by
  dsimp only
  rw [laurentCoeff_eq_normalizedDeriv n j hj,
    normalizedDeriv_regularized_eq_ZpowCore, normalizedDeriv_regularizedZpowCore]

theorem binomialWeight_integral (n : ℕ) (m : LeibnizIndex n) :
    ∃ z : ℤ, (binomialWeight n m : ℤ) = z := by
  exact ⟨binomialWeight n m, rfl⟩

theorem gaussian_factorization :
    (4 - 2 * Complex.I : ℂ) = 2 * (2 - Complex.I) := by
  apply Complex.ext <;> norm_num

theorem gaussian_factorization_conj :
    (4 + 2 * Complex.I : ℂ) = 2 * (2 + Complex.I) := by
  apply Complex.ext <;> norm_num

theorem gaussian_factorization_six_minus :
    (6 - 2 * Complex.I : ℂ) = 2 * (1 - Complex.I) * (2 + Complex.I) := by
  apply Complex.ext <;> norm_num

theorem gaussian_factorization_six_plus :
    (6 + 2 * Complex.I : ℂ) = 2 * (1 + Complex.I) * (2 - Complex.I) := by
  apply Complex.ext <;> norm_num

theorem gaussian_normSq_one_add_I :
    Complex.normSq (1 + Complex.I) = 2 := by
  norm_num [Complex.normSq]

theorem gaussian_normSq_two_add_I :
    Complex.normSq (2 + Complex.I) = 5 := by
  norm_num [Complex.normSq]

theorem gaussian_normSq_two_sub_I :
    Complex.normSq (2 - Complex.I) = 5 := by
  norm_num [Complex.normSq]

noncomputable def gaussianSummand (n : ℕ) (j : ℤ) (m : LeibnizIndex n) : ℂ :=
  (binomialWeight n m : ℂ) *
    2 ^ ((5 * 3714 - 2 * 5570) * n - 1 + j.toNat + m.m1) *
    5 ^ (2 * (1857 + 3714 - 5570) * n + j.toNat) *
    (1 - Complex.I) ^ (-m.m4 : ℤ) *
    (1 + Complex.I) ^ (-m.m5 : ℤ) *
    (2 + Complex.I) ^ (m.m2 + m.m5) *
    (2 - Complex.I) ^ (m.m3 + m.m4)

def conjugateIndex {n : ℕ} (m : LeibnizIndex n) : LeibnizIndex n :=
  ⟨m.m0, m.m1, m.m3, m.m2, m.m5, m.m4⟩

theorem conjugateIndex_involutive {n : ℕ} (m : LeibnizIndex n) :
    conjugateIndex (conjugateIndex m) = m := by
  cases m
  rfl

theorem binomialWeight_conjugateIndex (n : ℕ) (m : LeibnizIndex n) :
    binomialWeight n (conjugateIndex m) = binomialWeight n m := by
  simp [binomialWeight, conjugateIndex, mul_comm, mul_left_comm]

theorem gaussianSummand_conj (n : ℕ) (j : ℤ) (m : LeibnizIndex n) :
    star (gaussianSummand n j m) =
      gaussianSummand n j (conjugateIndex m) := by
  have hw' : binomialWeight n
      { m0 := m.m0, m1 := m.m1, m2 := m.m3, m3 := m.m2,
        m4 := m.m5, m5 := m.m4 } = binomialWeight n m := by
    simp [binomialWeight, mul_comm, mul_left_comm]
  simp [gaussianSummand, conjugateIndex, map_mul, map_pow, map_zpow, hw']
  ring

noncomputable def gaussianPaired (n : ℕ) (j : ℤ) (m : LeibnizIndex n) : ℂ :=
  gaussianSummand n j m + gaussianSummand n j (conjugateIndex m)

theorem gaussianPaired_is_real (n : ℕ) (j : ℤ) (m : LeibnizIndex n) :
    ∃ r : ℝ, (r : ℂ) = gaussianPaired n j m := by
  refine ⟨(gaussianPaired n j m).re, ?_⟩
  have hc := gaussianSummand_conj n j m
  apply Complex.ext
  · simp [gaussianPaired]
  · rw [gaussianPaired, ← hc]
    simp

theorem valid_index_sum_nonnegative (n : ℕ) (j : ℤ) (m : LeibnizIndex n)
    (hm : LeibnizIndex.Valid n j m) : 0 ≤ m.m0 + m.m1 + m.m2 + m.m3 + m.m4 + m.m5 := by
  omega

end PiIrrationality
