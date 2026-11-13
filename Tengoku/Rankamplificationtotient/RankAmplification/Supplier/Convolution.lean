import Tengoku.Rankamplificationtotient.RankAmplification.Supplier.Weights
import Tengoku.Rankamplificationtotient.RankAmplification.ShiftedConvolution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Supplier divisor convolution This module packages the finite supplier weights as a `FiniteDivisorWeight` and specializes the finite shifted-divisor convolution inequality. -/

namespace RankAmplification

/-! ## The canonical finite divisor weight -/

/-- Canonical finite divisor weight obtained from all supplier systems.-/
noncomputable def supplierFiniteDivisorWeight {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) : FiniteDivisorWeight where
  support := supplierDivisorSupport P x
  weight d := supplierWeight P x d
  weight_nonneg := fun d hd ↦ by positivity
  support_pos := fun d hd ↦ by
    classical
    change d ∈ (allSupplierSystems P x).image SupplierSystem.selectedDivisor at hd
    obtain ⟨s, hs, hsd⟩ := Finset.mem_image.mp hd
    rw [← hsd]
    exact s.selectedDivisor_pos

@[simp]
theorem supplierFiniteDivisorWeight_support {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) :
    (supplierFiniteDivisorWeight P x).support = supplierDivisorSupport P x :=
  rfl

@[simp]
theorem supplierFiniteDivisorWeight_weight {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x d : ℕ) :
    (supplierFiniteDivisorWeight P x).weight d = supplierWeight P x d :=
  rfl

theorem supplierFiniteDivisorWeight_weight_nonneg {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x d : ℕ) :
    0 ≤ (supplierFiniteDivisorWeight P x).weight d := by
  simp

theorem supplierFiniteDivisorWeight_support_pos {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) {d : ℕ}
    (hd : d ∈ (supplierFiniteDivisorWeight P x).support) :
    0 < d :=
  (supplierFiniteDivisorWeight P x).support_pos d hd

theorem supplierFiniteDivisorWeight_weight_pos_of_mem {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) {d : ℕ}
    (hd : d ∈ (supplierFiniteDivisorWeight P x).support) :
    0 < (supplierFiniteDivisorWeight P x).weight d := by
  have hnat : 0 < supplierWeight P x d :=
    (supplierWeight_pos_iff_mem_support P x d).mpr hd
  change (0 : ℝ) < (supplierWeight P x d : ℝ)
  exact_mod_cast hnat

private theorem supplier_eval_nat_sum_eq {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x N : ℕ) (hN : N ≠ 0) :
    (∑ d ∈ (supplierDivisorSupport P x).filter (· ∣ N), supplierWeight P x d) =
      supplierDivisorWeight P x N := by
  unfold supplierDivisorWeight
  apply Finset.sum_subset
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hd).2, hN⟩
  · intro d hdDivisors hdSupport
    have hdvd : d ∣ N := (Nat.mem_divisors.mp hdDivisors).1
    have hnotSupport : d ∉ supplierDivisorSupport P x := by
      intro hs
      exact hdSupport (Finset.mem_filter.mpr ⟨hs, hdvd⟩)
    exact Nat.eq_zero_of_not_pos fun hpos ↦
      hnotSupport ((supplierWeight_pos_iff_mem_support P x d).mp hpos)

theorem supplierFiniteDivisorWeight_eval {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x N : ℕ) (hN : N ≠ 0) :
    (supplierFiniteDivisorWeight P x).eval N = supplierDivisorWeight P x N := by
  rw [FiniteDivisorWeight.eval_eq_sum_filter]
  change (∑ d ∈ (supplierDivisorSupport P x).filter (· ∣ N),
    (supplierWeight P x d : ℝ)) = (supplierDivisorWeight P x N : ℝ)
  exact_mod_cast supplier_eval_nat_sum_eq P x N hN

theorem supplierFiniteDivisorWeight_mass {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) :
    (supplierFiniteDivisorWeight P x).mass = (supplierReciprocalMass P x : ℝ) := by
  change (∑ d ∈ supplierDivisorSupport P x,
    (supplierWeight P x d : ℝ) / (d : ℝ)) =
      ((∑ d ∈ supplierDivisorSupport P x,
        (supplierWeight P x d : ℚ) / (d : ℚ) : ℚ) : ℝ)
  push_cast
  rfl

theorem supplierFiniteDivisorWeight_tailMass {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x H : ℕ) :
    (supplierFiniteDivisorWeight P x).tailMass H =
      (supplierReciprocalTail P x H : ℝ) := by
  change (∑ d ∈ (supplierDivisorSupport P x).filter (H < ·),
    (supplierWeight P x d : ℝ) / (d : ℝ)) =
      ((∑ d ∈ (supplierDivisorSupport P x).filter (H < ·),
        (supplierWeight P x d : ℚ) / (d : ℚ) : ℚ) : ℝ)
  push_cast
  rfl

/-- The literal supplier version of `‖F_P‖_{∞,B}`.-/
noncomputable def supplierSupNorm {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x B : ℕ) : ℝ :=
  (supplierFiniteDivisorWeight P x).supNorm B

theorem supplierSupNorm_nonneg {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) {B : ℕ} (hB : 1 ≤ B) :
    0 ≤ supplierSupNorm P x B :=
  (supplierFiniteDivisorWeight P x).supNorm_nonneg hB

theorem supplierDivisorWeight_le_supplierSupNorm {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) {B N : ℕ}
    (hN : N ∈ Finset.Icc 1 B) :
    (supplierDivisorWeight P x N : ℝ) ≤ supplierSupNorm P x B := by
  have hNpos : 0 < N := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hN).1
  rw [← supplierFiniteDivisorWeight_eval P x N hNpos.ne']
  exact (supplierFiniteDivisorWeight P x).eval_le_supNorm hN

/-! ## Support arithmetic and the supplier convolution -/

theorem supplierFiniteDivisorWeight_primeFactor_gt_lowerCutoff {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) {d p : ℕ}
    (hd : d ∈ (supplierFiniteDivisorWeight P x).support)
    (hp : p.Prime) (hpd : p ∣ d) :
    y < p := by
  classical
  change d ∈ (allSupplierSystems P x).image SupplierSystem.selectedDivisor at hd
  obtain ⟨s, hs, hsd⟩ := Finset.mem_image.mp hd
  rw [← hsd] at hpd
  exact s.primeFactor_selectedDivisor_gt_lowerCutoff hp hpd

/-- The exact supplier-weight form of the paper's shifted convolution inequality (10.19).-/
theorem supplier_shifted_divisor_convolution {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x h : ℕ)
    (hh : 0 < h) (hhx : h ≤ x) (hhy : h ≤ y) :
    (∑ n ∈ Finset.Icc 1 x,
        (supplierDivisorWeight P x n : ℝ) *
          (supplierDivisorWeight P x (n + h) : ℝ)) ≤
      2 * x * (supplierReciprocalMass P x : ℝ) ^ 2 +
        4 * x * supplierSupNorm P x (2 * x) *
          (supplierReciprocalTail P x x.sqrt : ℝ) := by
  let W := supplierFiniteDivisorWeight P x
  have hlarge : ∀ d ∈ W.support, 0 < W.weight d →
      ∀ p : ℕ, p.Prime → p ∣ d → h < p := by
    intro d hd hwd p hp hpd
    exact hhy.trans_lt
      (supplierFiniteDivisorWeight_primeFactor_gt_lowerCutoff P x hd hp hpd)
  have hconv := W.shifted_divisor_convolution_supNorm hh hhx hlarge
  calc
    (∑ n ∈ Finset.Icc 1 x,
        (supplierDivisorWeight P x n : ℝ) *
          (supplierDivisorWeight P x (n + h) : ℝ)) =
        ∑ n ∈ Finset.Icc 1 x, W.eval n * W.eval (n + h) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      rw [supplierFiniteDivisorWeight_eval P x n hnpos.ne',
        supplierFiniteDivisorWeight_eval P x (n + h) (Nat.add_pos_left hnpos h).ne']
    _ ≤ 2 * x * W.mass ^ 2 +
        4 * x * W.supNorm (2 * x) * W.tailMass x.sqrt := hconv
    _ = 2 * x * (supplierReciprocalMass P x : ℝ) ^ 2 +
        4 * x * supplierSupNorm P x (2 * x) *
          (supplierReciprocalTail P x x.sqrt : ℝ) := by
      rw [supplierFiniteDivisorWeight_mass, supplierFiniteDivisorWeight_tailMass]
      rfl

end RankAmplification
