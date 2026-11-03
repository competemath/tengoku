import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.GradedIntervalCount
import Tengoku.Seed.Data.Finset.Max

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Exact support endpoints and allowed shifts -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.GradedInterval

/-- Natural endpoints of a finite nonnegative support, attained in that support.-/
structure SupportWindow (D : Finset ℤ) where
  lower : ℕ
  upper : ℕ
  lower_mem : (lower : ℤ) ∈ D
  upper_mem : (upper : ℤ) ∈ D
  bounds : ∀ d ∈ D, (lower : ℤ) ≤ d ∧ d ≤ upper

/-- A finite nonempty nonnegative support has exact natural endpoints.-/
def SupportWindow.ofNonnegative (D : Finset ℤ) (hne : D.Nonempty)
    (hpos : ∀ d ∈ D, 0 ≤ d) : SupportWindow D := by
  let l := D.min' hne
  let u := D.max' hne
  have hl : 0 ≤ l := hpos l (Finset.min'_mem D hne)
  have hu : 0 ≤ u := hpos u (Finset.max'_mem D hne)
  have hl' : (l.toNat : ℤ) = l := by omega
  have hu' : (u.toNat : ℤ) = u := by omega
  exact
    { lower := l.toNat
      upper := u.toNat
      lower_mem := by rw [hl']; exact Finset.min'_mem D hne
      upper_mem := by rw [hu']; exact Finset.max'_mem D hne
      bounds := fun d hd ↦ by
        rw [hl', hu']
        exact ⟨Finset.min'_le D d hd, Finset.le_max' D d hd⟩ }

/--
@isnad1 id=le.0h2v.s3.ab28c63e23a3 from=translated src=- shape=8b7cba42 vocab=11f6c603
-/
theorem SupportWindow.lower_le_upper {D : Finset ℤ} (W : SupportWindow D) : W.lower ≤ W.upper := by
  have h := (W.bounds W.upper W.upper_mem).1
  exact_mod_cast h

/-- Support containment after a shift is exactly the allowed-shift condition.
@isnad1 id=iff.0h4v.s6.0208e823bddf from=translated src=- shape=2039f7ba vocab=f60382ee
-/
theorem SupportWindow.shift_supported_iff {D : Finset ℤ} (W : SupportWindow D) (m : ℕ) (t : ℤ) :
    (∀ d ∈ D, 0 ≤ d + t ∧ d + t ≤ m) ↔ t ∈ allowedShifts m W.lower W.upper := by
  rw [mem_allowedShifts]
  constructor
  · intro h
    exact ⟨(h W.lower W.lower_mem).1, (h W.upper W.upper_mem).2⟩
  · intro h d hd
    have hb := W.bounds d hd
    constructor <;> omega

end MagnitudeConjecture.GradedInterval
