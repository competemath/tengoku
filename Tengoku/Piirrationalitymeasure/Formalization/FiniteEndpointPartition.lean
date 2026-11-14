import Tengoku.Piirrationalitymeasure.Formalization.FiniteStepIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Ordered finite endpoints, fixed boundary cuts, and endpoint-prefix comparisons. -/

namespace PiIrrationality

open Set

theorem exists_strictMono_enumeration {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : Function.Injective f) :
    ∃ e : Fin (Fintype.card ι) ≃ ι, StrictMono (fun k => f (e k)) := by
  classical
  letI : LinearOrder ι := LinearOrder.lift' f hf
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  exact ⟨e.toEquiv, fun _ _ h => e.strictMono h⟩

noncomputable def finiteEndpointPartition {n : ℕ} (a b : ℝ) (f : Fin n → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then a else if hk : k - 1 < n then f ⟨k - 1, hk⟩ else b

theorem finiteEndpointPartition_zero {n : ℕ} (a b : ℝ) (f : Fin n → ℝ) :
    finiteEndpointPartition a b f 0 = a := by simp [finiteEndpointPartition]

theorem finiteEndpointPartition_succ {n : ℕ} (a b : ℝ) (f : Fin n → ℝ) (k : ℕ) :
    finiteEndpointPartition a b f (k + 1) = if hk : k < n then f ⟨k, hk⟩ else b := by
  simp [finiteEndpointPartition]

theorem finiteEndpointPartition_internal {n : ℕ} (a b : ℝ) (f : Fin n → ℝ) (k : Fin n) :
    finiteEndpointPartition a b f (k.val + 1) = f k := by
  simp [finiteEndpointPartition_succ, k.isLt]

theorem finiteEndpointPartition_last {n : ℕ} (a b : ℝ) (f : Fin n → ℝ) :
    finiteEndpointPartition a b f (n + 1) = b := by
  simp [finiteEndpointPartition_succ]

theorem finiteEndpointPartition_monotone {n : ℕ} {a b : ℝ} {f : Fin n → ℝ}
    (hab : a ≤ b) (hf : Monotone f) (hI : ∀ k, f k ∈ Icc a b) :
    Monotone (finiteEndpointPartition a b f) := by
  apply monotone_nat_of_le_succ
  intro k
  cases k with
  | zero =>
    rw [finiteEndpointPartition_zero, finiteEndpointPartition_succ]
    split_ifs with hn
    · exact (hI ⟨0, hn⟩).1
    · exact hab
  | succ k =>
    rw [finiteEndpointPartition_succ, finiteEndpointPartition_succ]
    split_ifs with hk hk'
    · exact hf (by change k ≤ k + 1; omega)
    · exact (hI ⟨k, hk⟩).2
    · omega
    · rfl

theorem finiteEndpointPartition_adjacent_lt {n : ℕ} {a b : ℝ} {f : Fin n → ℝ}
    (hab : a < b) (hf : StrictMono f) (hI : ∀ k, f k ∈ Ioo a b) :
    ∀ k < n + 1, finiteEndpointPartition a b f k < finiteEndpointPartition a b f (k + 1) := by
  intro k hk
  cases k with
  | zero =>
    rw [finiteEndpointPartition_zero, finiteEndpointPartition_succ]
    split_ifs with hn
    · exact (hI ⟨0, hn⟩).1
    · exact hab
  | succ k =>
    have hkn : k < n := by omega
    rw [finiteEndpointPartition_succ, finiteEndpointPartition_succ, dite_eq_left hkn]
    split_ifs with hk'
    · exact hf (by change k < k + 1; omega)
    · exact (hI ⟨k, hkn⟩).2

theorem finiteEndpointPartition_cell_subset {n : ℕ} {a b : ℝ} {f : Fin n → ℝ}
    (hab : a ≤ b) (hf : Monotone f) (hI : ∀ k, f k ∈ Icc a b)
    {k : ℕ} (hk : k < n + 1) :
    Ioo (finiteEndpointPartition a b f k) (finiteEndpointPartition a b f (k + 1)) ⊆
      Ioo a b := by
  have hm := finiteEndpointPartition_monotone hab hf hI
  intro u hu
  have hL := hm (Nat.zero_le k)
  have hR := hm (by omega : k + 1 ≤ n + 1)
  rw [finiteEndpointPartition_zero] at hL
  rw [finiteEndpointPartition_last] at hR
  exact ⟨hL.trans_lt hu.1, hu.2.trans_le hR⟩

theorem finiteEndpointPartition_prefix {n : ℕ} {a b : ℝ} {f : Fin n → ℝ}
    (hab : a ≤ b) (hf : Monotone f) (hI : ∀ k, f k ∈ Icc a b)
    {k : ℕ} {u : ℝ}
    (hu : u ∈ Ioo (finiteEndpointPartition a b f k) (finiteEndpointPartition a b f (k + 1)))
    (j : Fin n) : f j ≤ u ↔ j.val < k := by
  have hm := finiteEndpointPartition_monotone hab hf hI
  constructor
  · intro hju
    by_contra hjk
    have h := hm (by omega : k + 1 ≤ j.val + 1)
    rw [finiteEndpointPartition_internal] at h
    linarith only [h, hu.2, hju]
  · intro hjk
    have h := hm (by omega : j.val + 1 ≤ k)
    rw [finiteEndpointPartition_internal] at h
    exact h.trans hu.1.le

end PiIrrationality
