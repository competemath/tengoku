import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact dyadic partition of positive natural indices

The cells `[2^i,2^(i+1))` partition `[1,2^D)`. Taking
`D = clog 2 (T+1)` includes every positive index at most `T`; an explicit
mask retains the exact final cutoff in every cell. The zero endpoint gives
an empty family and requires no exceptional convention.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

def dyadicNatDepth (T : ℕ) : ℕ := Nat.clog 2 (T + 1)

def dyadicNatCell (i : ℕ) : Finset ℕ := Ico (2 ^ i) (2 ^ (i + 1))

/--
@isnad1 id=eq.0h1v.s6.9fa75d227f12 from=translated src=- shape=89b0be66 vocab=bdab1729
-/
theorem dyadicNatCell_eq_Ico_add (i : ℕ) :
    dyadicNatCell i = Ico (2 ^ i) (2 ^ i + 2 ^ i) := by
  unfold dyadicNatCell
  congr 1
  rw [pow_succ]
  omega

/--
@isnad1 id=eq.0h0v.s3.8258addda462 from=translated src=- shape=3c26ae4f vocab=116744a9
-/
@[simp] theorem dyadicNatDepth_zero : dyadicNatDepth 0 = 0 := by
  simp [dyadicNatDepth]

/--
@isnad1 id=lt.0h1v.s4.0711fce1475f from=translated src=- shape=3dea6651 vocab=c0758faf
-/
theorem lt_two_pow_dyadicNatDepth (T : ℕ) : T < 2 ^ dyadicNatDepth T := by
  exact (Nat.lt_succ_self T).trans_le (Nat.le_pow_clog (by norm_num : 1 < 2) (T + 1))

/-- Distinct cells are disjoint, without restricting the depth.
@isnad1 id=disjoint.1h2v.s4.14467cdbbac6 from=translated src=- shape=c7c0c5d2 vocab=3c8f776e
-/
theorem dyadicNatCell_disjoint (i j : ℕ) (hij : i ≠ j) :
    Disjoint (dyadicNatCell i) (dyadicNatCell j) := by
  apply disjoint_left.mpr
  intro n hni hnj
  have hi := mem_Ico.mp hni
  have hj := mem_Ico.mp hnj
  rcases lt_or_gt_of_ne hij with h | h
  · have hp : (2 : ℕ) ^ (i + 1) ≤ 2 ^ j :=
      pow_le_pow_right' (by norm_num) (by omega)
    omega
  · have hp : (2 : ℕ) ^ (j + 1) ≤ 2 ^ i :=
      pow_le_pow_right' (by norm_num) (by omega)
    omega

/-- The complete finite union is exactly the enclosing positive interval.
@isnad1 id=eq.0h1v.s5.6bcb3c8bda3e from=translated src=- shape=3633a05f vocab=85afd98b
-/
theorem biUnion_dyadicNatCell (D : ℕ) :
    (range D).biUnion dyadicNatCell = Ico 1 (2 ^ D) := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [range_add_one, biUnion_insert, ih, union_comm]
      exact Ico_union_Ico_eq_Ico
        (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero D (by decide : (2 : ℕ) ≠ 0)))
        (pow_le_pow_right' (by norm_num) (Nat.le_succ D))

/--
@isnad1 id=eq.0h3v.s6.066eb1f196c9 from=translated src=- shape=579cbdcb vocab=1567553d
-/
theorem sum_dyadicNatCell {α : Type*} [AddCommMonoid α] (f : ℕ → α) (D : ℕ) :
    (∑ n ∈ Ico 1 (2 ^ D), f n) = ∑ i ∈ range D, ∑ n ∈ dyadicNatCell i, f n := by
  rw [← biUnion_dyadicNatCell]
  exact sum_biUnion (fun i _ j _ hij => dyadicNatCell_disjoint i j hij)

/-- Every positive index at most `T` belongs to exactly one selected cell.
@isnad1 id=existsun.1h2v.s5.e86d6a4b03c3 from=translated src=- shape=5ab37374 vocab=914377b5
-/
theorem existsUnique_dyadicNatCell (T n : ℕ) (hn : n ∈ Ioc 0 T) :
    ∃! i : ℕ, i ∈ range (dyadicNatDepth T) ∧ n ∈ dyadicNatCell i := by
  have hnroot : n ∈ Ico 1 (2 ^ dyadicNatDepth T) :=
    mem_Ico.mpr ⟨(mem_Ioc.mp hn).1, (mem_Ioc.mp hn).2.trans_lt (lt_two_pow_dyadicNatDepth T)⟩
  rw [← biUnion_dyadicNatCell] at hnroot
  obtain ⟨i, hi, hni⟩ := mem_biUnion.mp hnroot
  refine ⟨i, ⟨hi, hni⟩, ?_⟩
  intro j hj
  by_contra hji
  exact disjoint_left.mp (dyadicNatCell_disjoint j i hji) hj.2 hni

/-- Exact masked partition, expressed using the reusable cell definition.
@isnad1 id=eq.0h3v.s6.cccb353dce88 from=translated src=- shape=9821c016 vocab=91c20d56
-/
theorem sum_Ioc_eq_dyadicNatCell_masked {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (T : ℕ) :
    (∑ n ∈ Ioc 0 T, f n) =
      ∑ i ∈ range (dyadicNatDepth T), ∑ n ∈ dyadicNatCell i,
        if n ≤ T then f n else 0 := by
  rw [← sum_dyadicNatCell]
  have hsub : Ioc 0 T ⊆ Ico 1 (2 ^ dyadicNatDepth T) := by
    intro n hn
    exact mem_Ico.mpr ⟨(mem_Ioc.mp hn).1,
      (mem_Ioc.mp hn).2.trans_lt (lt_two_pow_dyadicNatDepth T)⟩
  calc
    _ = ∑ n ∈ Ioc 0 T, if n ≤ T then f n else 0 := by
      apply sum_congr rfl
      intro n hn
      simp only [ite_eq_left (mem_Ioc.mp hn).2]
    _ = _ := by
      apply sum_subset hsub
      intro n hn hnnot
      have hnT : ¬ n ≤ T := by
        intro h
        exact hnnot (mem_Ioc.mpr ⟨(mem_Ico.mp hn).1, h⟩)
      exact ite_eq_right hnT

/-- The explicit power-of-two cell form used by the bilinear box partition.
The cutoff remains inside each cell, so additional coefficient masks can
be included directly in `f`.
@isnad1 id=eq.0h3v.s7.0d4b18be2f9e from=translated src=- shape=fe289d3c vocab=4d6c4432
-/
theorem sum_Ioc_eq_dyadic_masked {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (T : ℕ) :
    (∑ n ∈ Ioc 0 T, f n) =
      ∑ i ∈ range (Nat.clog 2 (T + 1)), ∑ n ∈ Ico (2 ^ i) (2 ^ i + 2 ^ i),
        if n ≤ T then f n else 0 := by
  simpa only [dyadicNatDepth, dyadicNatCell_eq_Ico_add] using
    sum_Ioc_eq_dyadicNatCell_masked f T

end TwinPrime.Analytic
