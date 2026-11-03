import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.GradedIntervalCount
import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.CommonFiberSum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Exact weighted count of interior shifts -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace MagnitudeConjecture.GradedInterval

/-- The common interior interval is contained in every bounded support window.
@isnad1 id=le.1h4v.s6.e3a368cb4b28 from=translated src=- shape=d964ef12 vocab=9fb4cb52
-/
theorem interior_subset_allowedShifts (m h l r : ℕ) (hr : r ≤ h) :
    Finset.Icc (0 : ℤ) ((m : ℤ) - 2 * h) ⊆ allowedShifts m l r := by
  intro t ht
  rw [Finset.mem_Icc] at ht
  rw [mem_allowedShifts]
  constructor <;> omega

/-- Each ordinary label contributes once for each of the m-2h+1 interior shifts.
@isnad1 id=eq.2h6v.s11.5ca562c72641 from=translated src=- shape=1136e954 vocab=32029e2c
-/
theorem interior_weighted_sum {ι : Type*} [Fintype ι]
    (m h : ℕ) (l r : ι → ℕ) (hr : ∀ i, r i ≤ h) (hm : 2 * h ≤ m)
    (w : ι → ℕ) :
    (∑ a : {a : (i : ι) × ↥(allowedShifts m (l i) (r i)) //
        0 ≤ a.2.val ∧ a.2.val ≤ (m : ℤ) - 2 * h}, w a.val.1) =
      (m - 2 * h + 1) * ∑ i, w i := by
  have hsum := sum_common_fiber (fun i ↦ allowedShifts m (l i) (r i))
    (Finset.Icc (0 : ℤ) ((m : ℤ) - 2 * h))
    (fun i ↦ interior_subset_allowedShifts m h (l i) (r i) (hr i)) w
  have hc : (Finset.Icc (0 : ℤ) ((m : ℤ) - 2 * h)).card = m - 2 * h + 1 := by
    rw [Int.card_Icc]
    omega
  let e : {a : (i : ι) × ↥(allowedShifts m (l i) (r i)) //
      0 ≤ a.2.val ∧ a.2.val ≤ (m : ℤ) - 2 * h} ≃
      {a : (i : ι) × ↥(allowedShifts m (l i) (r i)) //
        a.2.val ∈ Finset.Icc (0 : ℤ) ((m : ℤ) - 2 * h)} :=
    Equiv.subtypeEquivRight (fun _ ↦ Finset.mem_Icc.symm)
  have he := e.sum_comp (fun a ↦ w a.val.1)
  exact he.trans (by simpa only [hc] using hsum)

end MagnitudeConjecture.GradedInterval
