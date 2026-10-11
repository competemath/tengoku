module

public import Tengoku.AddCombi.AddCombi.Mathlib.Algebra.Notation.Indicator
public import Tengoku

public section

open scoped Indicator

namespace Set
variable {α M : Type*} [Zero M] [One M]

section Preorder
variable [Preorder M] [ZeroLEOneClass M] {s : Set α}

@[simp] lemma indicator_one_nonneg : 0 ≤ s.indicator (fun _ ↦ (1 : M)) :=
  indicator_nonneg (by simp)

@[local simp] lemma indicator_one_apply_nonneg {a : α} :
    0 ≤ s.indicator (fun _ ↦ (1 : M)) a := indicator_one_nonneg a

end Preorder
attribute [local simp] Set.indicator_one_nonneg

section PartialOrder
variable [PartialOrder M] [ZeroLEOneClass M] [NeZero (1 : M)] {s : Set α}

@[local simp]
lemma indicator_one_pos [Nontrivial M] : 0 < s.indicator (fun _ ↦ (1 : M)) ↔ s.Nonempty := by
  classical
  simp [indicator_apply, lt_iff_le_not_ge, Pi.le_def, apply_ite, ite_apply, Set.Nonempty,
    zero_lt_one.not_ge]

end PartialOrder
attribute [local simp] Set.indicator_one_apply_nonneg
end Set
-- Tengoku: 2 registration(s) of this module made local so they do not change other libraries (generated)
