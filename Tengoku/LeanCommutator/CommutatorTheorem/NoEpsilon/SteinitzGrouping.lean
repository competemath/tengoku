import Tengoku.LeanCommutator.CommutatorTheorem.NoEpsilon.Steinitz
import Tengoku.Seed.Logic.Equiv.Fin.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Trace-controlled groups from the two-dimensional Steinitz lemma

The permutation partitions kR entries into k groups of exactly R entries.
The first coordinate has group sums bounded by four, and a nonnegative second
coordinate of total mass at most 2k has group sums bounded by six.
-/

open scoped BigOperators

namespace NoEpsilon.SteinitzGrouping

/--
@isnad1 id=eq.1h4v.s7.7d97e20ae8a0 from=translated src=- shape=f92fdf96 vocab=a38c3e39
-/
theorem interval_sum_eq_sub_prefix {n : ℕ} (z : Fin n → ℂ) (a b : ℕ) (hab : a ≤ b) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ a ≤ i.val ∧ i.val < b), z i) =
      (∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ i.val < b), z i) -
        ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ i.val < a), z i := by
  classical
  apply eq_sub_iff_add_eq.mpr
  rw [← Finset.sum_union]
  · congr 1
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hi'
    omega

/--
@isnad1 id=eq.0h4v.s8.5eae0d9a04ea from=translated src=- shape=0850c6ed vocab=57f88c4b
-/
theorem group_sum_eq_interval {k R : ℕ} (z : Fin (k * R) → ℂ) (j : Fin k) :
    (∑ b : Fin R, z (finProdFinEquiv (j, b))) =
      ∑ i ∈ Finset.univ.filter
        (fun i : Fin (k * R) ↦ j.val * R ≤ i.val ∧ i.val < (j.val + 1) * R), z i := by
  classical
  apply Finset.sum_bij (fun b _ ↦ finProdFinEquiv (j, b))
  · intro b _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change j.val * R ≤ b.val + R * j.val ∧ b.val + R * j.val < (j.val + 1) * R
    have hb := b.isLt
    constructor <;> nlinarith
  · intro b _ c _ h
    exact congrArg Prod.snd (finProdFinEquiv.injective h)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hlt : i.val - j.val * R < R := by
      have hu : i.val < j.val * R + R := by nlinarith [hi.2]
      omega
    refine ⟨⟨i.val - j.val * R, hlt⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change i.val - j.val * R + R * j.val = i.val
    nlinarith [Nat.sub_add_cancel hi.1]
  · intro b _
    rfl

/-- Consecutive length-R groups inherit coordinate bounds four from prefix bounds two.
@isnad1 id=and.1h4v.s9.83db10d7386e from=translated src=- shape=142091cb vocab=e78c2bbb
-/
theorem group_coordinates_le_four {k R : ℕ} (z : Fin (k * R) → ℂ)
    (hprefix : ∀ m : ℕ,
      |(∑ i ∈ Finset.univ.filter (fun i : Fin (k * R) ↦ i.val < m), z i).re| ≤ 2 ∧
      |(∑ i ∈ Finset.univ.filter (fun i : Fin (k * R) ↦ i.val < m), z i).im| ≤ 2)
    (j : Fin k) :
    |(∑ b : Fin R, z (finProdFinEquiv (j, b))).re| ≤ 4 ∧
      |(∑ b : Fin R, z (finProdFinEquiv (j, b))).im| ≤ 4 := by
  rw [group_sum_eq_interval, interval_sum_eq_sub_prefix _ _ _ (by nlinarith)]
  obtain ⟨hlre, hlim⟩ := hprefix (j.val * R)
  obtain ⟨hhre, hhim⟩ := hprefix ((j.val + 1) * R)
  simp only [Complex.sub_re, Complex.sub_im]
  constructor
  · exact (abs_sub _ _).trans (by linarith)
  · exact (abs_sub _ _).trans (by linarith)

end NoEpsilon.SteinitzGrouping
