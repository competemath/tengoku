module

public import Tengoku.Expdb.Expdb.ExponentialSums.FixedExponentialSum
public import Tengoku

/-!
# Finite scale transfer for exponential sums

This module gives two ways to rewrite an exponential sum at a different length scale. Finite
Fourier inversion dilates a sum from scale `N` to `q * N`, while decomposition into residue
classes produces sums at scales approximately `N / q`. These identities are used to compare
the exponential-sum growth exponent at different values of `α`.
-/

@[expose] public section

open scoped Expdb FourierTransform

noncomputable section

namespace Expdb

/-! ## Finite Fourier orthogonality -/

private lemma sum_stdAddChar_mul_eq_ite (q m : ℕ) [NeZero q] :
    (∑ h : ZMod q, ZMod.stdAddChar (h * (m : ZMod q))) =
      if q ∣ m then (q : ℂ) else 0 := by
  rw [AddChar.sum_mulShift (m : ZMod q) (ZMod.isPrimitive_stdAddChar q)]
  simp only [ZMod.natCast_eq_zero_iff m q, ZMod.card]
  split_ifs <;> norm_num

private lemma stdAddChar_mul_nat_eq_fourierChar (q m : ℕ) [NeZero q] (h : ZMod q) :
    ZMod.stdAddChar (h * (m : ZMod q)) =
      (𝐞 ((h.val : ℝ) * (m : ℝ) / q) : ℂ) := by
  rw [← h.natCast_zmod_val, ← Nat.cast_mul, ZMod.stdAddChar_apply,
    ZMod.toCircle_natCast, Real.fourierChar_apply]
  push_cast
  rw [ZMod.val_natCast_of_lt h.val_lt]
  congr 1
  ring_nf

/-! ## Reindexing exponential sums -/

/-- Finite Fourier inversion expresses a sum at scale `N` as an average of sums dilated by `q`. -/
lemma exponentialSumAt_dilate (F : ℝ → ℝ) (T N : ℝ) (a b q : ℕ) [NeZero q]
    (hq : 0 < q) (hT : T ≠ 0) (hN : N ≠ 0) :
    exponentialSumAt F T N a b =
      (q : ℂ)⁻¹ * ∑ h : ZMod q,
        exponentialSumAt (fun u ↦ F u + (h.val : ℝ) * N / T * u)
          T (q * N) (q * a) (q * b) := by
  rw [exponentialSumAt]
  simp_rw [exponentialSumAt, oscillatory]
  rw [Finset.sum_comm]
  classical
  symm
  calc
    (q : ℂ)⁻¹ * ∑ m ∈ Finset.Icc (q * a) (q * b), ∑ h : ZMod q,
        (𝐞 (T * (F ((m : ℝ) / (q * N)) +
          (h.val : ℝ) * N / T * ((m : ℝ) / (q * N)))) : ℂ) =
        ∑ m ∈ Finset.Icc (q * a) (q * b),
          (q : ℂ)⁻¹ * ((𝐞 (T * F ((m : ℝ) / (q * N))) : ℂ) *
            ∑ h : ZMod q, ZMod.stdAddChar (h * (m : ZMod q))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      apply congrArg (fun z : ℂ ↦ (q : ℂ)⁻¹ * z)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      have harg :
          T * (F ((m : ℝ) / (q * N)) +
            (h.val : ℝ) * N / T * ((m : ℝ) / (q * N))) =
            T * F ((m : ℝ) / (q * N)) + (h.val : ℝ) * m / q := by
        field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast hq.ne', hT, hN]
      rw [harg, AddChar.map_add_eq_mul, stdAddChar_mul_nat_eq_fourierChar]
      exact Circle.coe_mul _ _
    _ = ∑ m ∈ Finset.Icc (q * a) (q * b),
          if q ∣ m then (𝐞 (T * F ((m : ℝ) / (q * N))) : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [sum_stdAddChar_mul_eq_ite]
      split_ifs with hdiv
      · field_simp [show (q : ℂ) ≠ 0 by exact_mod_cast hq.ne']
      · simp
    _ = ∑ n ∈ Finset.Icc a b, (𝐞 (T * F ((n : ℝ) / N)) : ℂ) := by
      symm
      rw [← Finset.sum_filter]
      apply Finset.sum_bij (fun n _ ↦ q * n)
      · intro n hn
        simp only [Finset.mem_Icc] at hn
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨Nat.mul_le_mul_left q hn.1, Nat.mul_le_mul_left q hn.2⟩,
          dvd_mul_right q n⟩
      · intro n₁ hn₁ n₂ hn₂ heq
        exact Nat.eq_of_mul_eq_mul_left hq heq
      · intro m hm
        simp only [Finset.mem_filter, Finset.mem_Icc] at hm
        obtain ⟨n, rfl⟩ := hm.2
        refine ⟨n, ?_, rfl⟩
        simp only [Finset.mem_Icc]
        constructor
        · exact Nat.le_of_mul_le_mul_left hm.1.1 hq
        · exact Nat.le_of_mul_le_mul_left hm.1.2 hq
      · intro n hn
        push_cast
        congr 3
        field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast hq.ne']

/-- Triangle-inequality form of `exponentialSumAt_dilate`. -/
lemma norm_exponentialSumAt_dilate_le (F : ℝ → ℝ) (T N : ℝ) (a b q : ℕ)
    [NeZero q]
    (hq : 0 < q) (hT : T ≠ 0) (hN : N ≠ 0) :
    ‖exponentialSumAt F T N a b‖ ≤
      ∑ h : ZMod q,
        ‖exponentialSumAt (fun u ↦ F u + (h.val : ℝ) * N / T * u)
          T (q * N) (q * a) (q * b)‖ / q := by
  rw [exponentialSumAt_dilate F T N a b q hq hT hN, norm_mul, norm_inv,
    Complex.norm_natCast]
  calc
    (q : ℝ)⁻¹ * ‖∑ h : ZMod q,
        exponentialSumAt (fun u ↦ F u + (h.val : ℝ) * N / T * u)
          T (q * N) (q * a) (q * b)‖ ≤
        (q : ℝ)⁻¹ * ∑ h : ZMod q,
          ‖exponentialSumAt (fun u ↦ F u + (h.val : ℝ) * N / T * u)
            T (q * N) (q * a) (q * b)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      simp only [div_eq_mul_inv]
      ring

/-- The scale induced by restricting a sum to the residue class `r mod q`. -/
def residueScale (N : ℝ) (q r : ℕ) : ℝ := (N - r) / q

/-- The affine phase induced by restricting a sum to the residue class `r mod q`. -/
def residuePhase (F : ℝ → ℝ) (N : ℝ) (r : ℕ) : ℝ → ℝ :=
  fun u ↦ F ((1 - (r : ℝ) / N) * u + (r : ℝ) / N)

/-- Evaluation of the residue-class phase at its rescaled integer arguments. -/
lemma residuePhase_identity (F : ℝ → ℝ) (N : ℝ) (q r m : ℕ)
    (hN : N ≠ 0) (hrN : (r : ℝ) < N) :
    residuePhase F N r ((m : ℝ) / residueScale N q r) =
      F (((q * m + r : ℕ) : ℝ) / N) := by
  simp only [residuePhase, residueScale]
  push_cast
  field_simp [sub_ne_zero.mpr (ne_of_gt hrN)]

/-- Reindex one residue class as an exponential sum with `residuePhase` and `residueScale`. -/
lemma exponentialSumAt_residue (F : ℝ → ℝ) (T N : ℝ) (a b q r : ℕ)
    (hq : 0 < q) (hr : r < q) (hra : r ≤ a) (hab : a ≤ b)
    (hN : N ≠ 0) (hrN : (r : ℝ) < N) :
    (∑ n ∈ Finset.Icc a b with n % q = r, oscillatory F T N n) =
      exponentialSumAt (residuePhase F N r) T (residueScale N q r)
        ((a - r) ⌈/⌉ q) ((b - r) / q) := by
  rw [exponentialSumAt]
  classical
  symm
  apply Finset.sum_bij (fun m _ ↦ q * m + r)
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · constructor
      · have ha : a - r ≤ q * m :=
          (ceilDiv_le_iff_le_mul hq).mp hm.1
        omega
      · have hb : q * m ≤ b - r := by
          simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq).mp hm.2
        omega
    · simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
  · intro m₁ hm₁ m₂ hm₂ heq
    exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel heq)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    have hnrepr : n = q * (n / q) + r := by
      have hnmod := hn.2
      have hdecomp := Nat.mod_add_div n q
      omega
    refine ⟨n / q, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      constructor
      · apply (ceilDiv_le_iff_le_mul hq).mpr
        omega
      · apply (Nat.le_div_iff_mul_le hq).mpr
        rw [Nat.mul_comm]
        omega
    · exact hnrepr.symm
  · intro m hm
    simp only [oscillatory]
    rw [residuePhase_identity F N q r m hN hrN]

end Expdb
