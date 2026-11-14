import Tengoku.Piirrationalitymeasure.Formalization.FiniteStepIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Ordered finite endpoints, fixed boundary cuts, and endpoint-prefix comparisons. -/

namespace PiIrrationality

open Set

/--
@isnad1 id=ex.1h2v.s6.5bc6f755bc7c from=translated src=- shape=9570131f vocab=a080fe4a
-/
theorem exists_strictMono_enumeration {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : Function.Injective f) :
    ∃ e : Fin (Fintype.card ι) ≃ ι, StrictMono (fun k => f (e k)) := by
  classical
  letI : LinearOrder ι := LinearOrder.lift' f hf
  let e := Fintype.orderIsoFinOfCardEq ι rfl
  exact ⟨e.toEquiv, fun _ _ h => e.strictMono h⟩

noncomputable def finiteEndpointPartition {n : ℕ} (a b : ℝ) (f : Fin n → ℝ) (k : ℕ) : ℝ :=
  if k = 0 then a else if hk : k - 1 < n then f ⟨k - 1, hk⟩ else b

/--
@isnad1 id=eq.0h4v.s4.bb093833a3b0 from=translated src=- shape=51180b07 vocab=245b00cd
-/
theorem finiteEndpointPartition_zero {n : ℕ} (a b : ℝ) (f : Fin n → ℝ) :
    finiteEndpointPartition a b f 0 = a := by simp [finiteEndpointPartition]

/--
@isnad1 id=eq.0h5v.s5.2559783e37f9 from=translated src=- shape=648b5e99 vocab=1d312830
-/
theorem finiteEndpointPartition_succ {n : ℕ} (a b : ℝ) (f : Fin n → ℝ) (k : ℕ) :
    finiteEndpointPartition a b f (k + 1) = if hk : k < n then f ⟨k, hk⟩ else b := by
  simp [finiteEndpointPartition]

/--
@isnad1 id=eq.0h5v.s5.1d20e0994b2f from=translated src=- shape=8b203e8a vocab=ae7f0f89
-/
theorem finiteEndpointPartition_internal {n : ℕ} (a b : ℝ) (f : Fin n → ℝ) (k : Fin n) :
    finiteEndpointPartition a b f (k.val + 1) = f k := by
  simp [finiteEndpointPartition_succ, k.isLt]

/--
@isnad1 id=eq.0h4v.s5.6fabdd6d418e from=translated src=- shape=9a1fea94 vocab=9c0accd7
-/
theorem finiteEndpointPartition_last {n : ℕ} (a b : ℝ) (f : Fin n → ℝ) :
    finiteEndpointPartition a b f (n + 1) = b := by
  simp [finiteEndpointPartition_succ]

/--
@isnad1 id=monotone.3h4v.s5.1aa64f93979d from=translated src=- shape=e9fa0f7d vocab=2c7e666d
-/
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

/--
@isnad1 id=lt.4h5v.s6.8932a483f9a8 from=translated src=- shape=dc91c138 vocab=640a5077
-/
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

/--
@isnad1 id=le.4h5v.s6.0ab37ad3f777 from=translated src=- shape=c21f0fe2 vocab=3f73672d
-/
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

/--
@isnad1 id=iff.4h7v.s6.7e5a67b59ac8 from=translated src=- shape=4e82d2b5 vocab=263c01d0
-/
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
