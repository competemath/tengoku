import Tengoku.DeletionCodesLean.DeletionCode.FiniteConflictGraph
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Data.Fintype.EquivFin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms card_column_predicate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms card_editColumn` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms card_deletionColumns` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms card_insertionColumns` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms editEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms split_column` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms oneEditTarget_deletion_split` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms oneEditTarget_insertion_split` (it only prints; the queue checks the axioms of every declaration). -/

/-!
The finite index set consists of actual deletion and insertion columns of a
trace. Orientations, bits, source positions, and isolated one-edit targets
are read from those columns. Its cardinalities are derived from the trace
counters, including the balanced Fin (2*t) enumeration.
-/
namespace DeletionCode.TraceEditData

open AlignmentTrace FiniteConflictGraph HeaderRecovery
open scoped BigOperators

def EditColumn (trace : Trace) := {i : Fin trace.length // EditIndex trace i}

instance editColumnFintype (trace : Trace) : Fintype (EditColumn trace) := by
  unfold EditColumn EditIndex
  infer_instance

def column (trace : Trace) (c : EditColumn trace) : Column := trace.get c.val

def position (trace : Trace) (c : EditColumn trace) : ℕ := trace.sourcePosition c.val.val

/--
@isnad1 id=eq.0h2v.s3.3ed6c522b8a8 from=translated src=- shape=7c33b116 vocab=1d84ba3f
-/
theorem column_isEdit (trace : Trace) (c : EditColumn trace) :
    (column trace c).isEdit = true := c.property

/--
@isnad1 id=or.0h2v.s4.06ec3a66964b from=translated src=- shape=0305dfea vocab=553e8352
-/
theorem column_cases (trace : Trace) (c : EditColumn trace) :
    (∃ bit, column trace c = .deletion bit) ∨ (∃ bit, column trace c = .insertion bit) := by
  have h := column_isEdit trace c
  cases hc : column trace c with
  | matched bit => simp only [hc, Column.isEdit, Bool.false_eq_true] at h
  | deletion bit => exact Or.inl ⟨bit, rfl⟩
  | insertion bit => exact Or.inr ⟨bit, rfl⟩

/-- The matched-column branch is unreachable in the actual edit index type,
as proved by column_cases. Its unused value makes this a direct computation.-/
def orientation (trace : Trace) (c : EditColumn trace) : Orientation :=
  match column trace c with
  | .matched _ => .deletion
  | .deletion _ => .deletion
  | .insertion _ => .insertion

def bit (trace : Trace) (c : EditColumn trace) : Bool :=
  match column trace c with
  | .matched b => b
  | .deletion b => b
  | .insertion b => b

/--
@isnad1 id=eq.1h3v.s4.1e8c269e8eac from=translated src=- shape=e2e46f55 vocab=1269f7bc
-/
theorem orientation_of_deletion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .deletion b) : orientation trace c = .deletion := by
  simp [orientation, hc]

/--
@isnad1 id=eq.1h3v.s4.72efa1837557 from=translated src=- shape=e2e46f55 vocab=0609bef0
-/
theorem orientation_of_insertion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .insertion b) : orientation trace c = .insertion := by
  simp [orientation, hc]

/--
@isnad1 id=eq.1h3v.s4.788d19c49710 from=translated src=- shape=11b4ecda vocab=7aa17be9
-/
theorem bit_of_deletion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .deletion b) : bit trace c = b := by simp [bit, hc]

/--
@isnad1 id=eq.1h3v.s4.cab1e80c552e from=translated src=- shape=11b4ecda vocab=6ff2cbe4
-/
theorem bit_of_insertion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .insertion b) : bit trace c = b := by simp [bit, hc]

/-- Perform this one actual edit on the original source, independently of
the other edit columns in the trace.-/
def oneEditTarget (trace : Trace) (c : EditColumn trace) : List Bool :=
  match orientation trace c with
  | .deletion => trace.source.eraseIdx (position trace c)
  | .insertion => trace.source.take (position trace c) ++
      bit trace c :: trace.source.drop (position trace c)

/--
@isnad1 id=eq.1h3v.s4.762adb2c9386 from=translated src=- shape=3b2e24dd vocab=9e28e1bd
-/
theorem oneEditTarget_of_deletion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .deletion b) :
    oneEditTarget trace c = trace.source.eraseIdx (position trace c) := by
  simp only [oneEditTarget, orientation_of_deletion trace c b hc]

/--
@isnad1 id=eq.1h3v.s5.dc84fbe32ad3 from=translated src=- shape=95a27bd3 vocab=ed12bc8c
-/
theorem oneEditTarget_of_insertion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .insertion b) :
    oneEditTarget trace c = trace.source.take (position trace c) ++
      b :: trace.source.drop (position trace c) := by
  simp only [oneEditTarget, orientation_of_insertion trace c b hc, bit_of_insertion trace c b hc]

def isDeletion : Column → Bool
  | .deletion _ => true
  | _ => false

def isInsertion : Column → Bool
  | .insertion _ => true
  | _ => false

private theorem isDeletion_edit (col : Column) (h : isDeletion col = true) : col.isEdit = true := by
  cases col <;> simp_all only [isDeletion, Column.isEdit, Bool.false_eq_true]

private theorem isInsertion_edit (col : Column) (h : isInsertion col = true) : col.isEdit = true := by
  cases col <;> simp_all only [isInsertion, Column.isEdit, Bool.false_eq_true]

/--
@isnad1 id=iff.0h2v.s4.1a15d926b81e from=translated src=- shape=557dc69c vocab=5bc39298
-/
theorem orientation_eq_deletion_iff (trace : Trace) (c : EditColumn trace) :
    orientation trace c = .deletion ↔ isDeletion (column trace c) = true := by
  rcases column_cases trace c with ⟨b, hc⟩ | ⟨b, hc⟩
  · simp only [orientation_of_deletion trace c b hc, hc, isDeletion]
  · simp only [orientation_of_insertion trace c b hc, hc, isDeletion, reduceCtorEq,
      Bool.false_eq_true]

/--
@isnad1 id=iff.0h2v.s4.680745941836 from=translated src=- shape=557dc69c vocab=1200aed6
-/
theorem orientation_eq_insertion_iff (trace : Trace) (c : EditColumn trace) :
    orientation trace c = .insertion ↔ isInsertion (column trace c) = true := by
  rcases column_cases trace c with ⟨b, hc⟩ | ⟨b, hc⟩
  · simp only [orientation_of_deletion trace c b hc, hc, isInsertion, reduceCtorEq,
      Bool.false_eq_true]
  · simp only [orientation_of_insertion trace c b hc, hc, isInsertion]

/-- Counting predicate-selected finite indices is the actual list count.
@isnad1 id=eq.0h2v.s6.52763cdb86be from=translated src=- shape=5e48c528 vocab=d91a83dd
-/
theorem card_column_predicate (trace : Trace) (p : Column → Bool) :
    Fintype.card {i : Fin trace.length // p (trace.get i) = true} = trace.countP p := by
  classical
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  induction trace with
  | nil => simp
  | cons col rest ih =>
    simp only [List.length_cons, Fin.sum_univ_succ, List.get_cons_zero,
      List.get_cons_succ', List.countP_cons, ih]
    by_cases hp : p col = true <;> simp_all [Nat.add_comm]

/--
@isnad1 id=eq.0h1v.s3.10e3547d6095 from=translated src=- shape=00600d72 vocab=774a60c6
-/
theorem countP_isDeletion (trace : Trace) : trace.countP isDeletion = trace.deletions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;> simp [isDeletion, List.countP_cons, Trace.deletions, ih]

/--
@isnad1 id=eq.0h1v.s3.7ca81c2d0d58 from=translated src=- shape=00600d72 vocab=43701963
-/
theorem countP_isInsertion (trace : Trace) : trace.countP isInsertion = trace.insertions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;> simp [isInsertion, List.countP_cons, Trace.insertions, ih]

/--
@isnad1 id=eq.0h1v.s4.8766ada17707 from=translated src=- shape=8f00d362 vocab=111fe1a1
-/
theorem countP_isEdit (trace : Trace) :
    trace.countP Column.isEdit = trace.deletions + trace.insertions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;>
      simp only [List.countP_cons, Column.isEdit, Bool.false_eq_true,
        ite_true, ite_false, Trace.deletions, Trace.insertions, ih] <;> omega

/--
@isnad1 id=eq.0h1v.s4.98d15854b807 from=translated src=- shape=9e21155a vocab=0c18fa33
-/
theorem card_editColumn (trace : Trace) :
    Fintype.card (EditColumn trace) = trace.deletions + trace.insertions :=
  (card_column_predicate trace Column.isEdit).trans (countP_isEdit trace)

def deletionColumnEquiv (trace : Trace) :
    {c : EditColumn trace // orientation trace c = .deletion} ≃
      {i : Fin trace.length // isDeletion (trace.get i) = true} where
  toFun c := ⟨c.val.val, (orientation_eq_deletion_iff trace c.val).mp c.property⟩
  invFun i := ⟨⟨i.val, isDeletion_edit (trace.get i.val) i.property⟩,
    (orientation_eq_deletion_iff trace _).mpr i.property⟩
  left_inv c := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

def insertionColumnEquiv (trace : Trace) :
    {c : EditColumn trace // orientation trace c = .insertion} ≃
      {i : Fin trace.length // isInsertion (trace.get i) = true} where
  toFun c := ⟨c.val.val, (orientation_eq_insertion_iff trace c.val).mp c.property⟩
  invFun i := ⟨⟨i.val, isInsertion_edit (trace.get i.val) i.property⟩,
    (orientation_eq_insertion_iff trace _).mpr i.property⟩
  left_inv c := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv i := by apply Subtype.ext; rfl

/--
@isnad1 id=eq.0h1v.s5.def258b701cf from=translated src=- shape=1bbfc25a vocab=356cbf37
-/
theorem card_deletionColumns (trace : Trace) :
    Fintype.card {c : EditColumn trace // orientation trace c = .deletion} = trace.deletions :=
  (Fintype.card_congr (deletionColumnEquiv trace)).trans
    ((card_column_predicate trace isDeletion).trans (countP_isDeletion trace))

/--
@isnad1 id=eq.0h1v.s5.4353a233f65a from=translated src=- shape=1bbfc25a vocab=fa0a5c85
-/
theorem card_insertionColumns (trace : Trace) :
    Fintype.card {c : EditColumn trace // orientation trace c = .insertion} = trace.insertions :=
  (Fintype.card_congr (insertionColumnEquiv trace)).trans
    ((card_column_predicate trace isInsertion).trans (countP_isInsertion trace))

/-- The balanced finite enumeration is obtained from the proved exact count.-/
noncomputable def editEquiv (trace : Trace) (t : ℕ)
    (hdel : trace.deletions = t) (hins : trace.insertions = t) :
    Fin (2 * t) ≃ EditColumn trace :=
  (Fintype.equivFinOfCardEq (show Fintype.card (EditColumn trace) = 2 * t by
    rw [card_editColumn, hdel, hins]
    omega)).symm

def sourcePrefix (trace : Trace) (c : EditColumn trace) : List Bool :=
  Trace.source (trace.take c.val.val)

def sourceSuffix (trace : Trace) (c : EditColumn trace) : List Bool :=
  Trace.source (trace.drop (c.val.val + 1))

def targetPrefix (trace : Trace) (c : EditColumn trace) : List Bool :=
  Trace.target (trace.take c.val.val)

def targetSuffix (trace : Trace) (c : EditColumn trace) : List Bool :=
  Trace.target (trace.drop (c.val.val + 1))

/--
@isnad1 id=eq.0h2v.s3.09331c7b32bc from=translated src=- shape=7493a1c1 vocab=5e16e2b8
-/
theorem position_eq_sourcePrefix_length (trace : Trace) (c : EditColumn trace) :
    position trace c = (sourcePrefix trace c).length := rfl

/-- The selected trace column is recovered from the exact prefix/suffix split.
@isnad1 id=eq.0h2v.s6.c518e63e4c2c from=translated src=- shape=6bd7b165 vocab=da5ed674
-/
theorem split_column (trace : Trace) (c : EditColumn trace) :
    trace = trace.take c.val.val ++ column trace c :: trace.drop (c.val.val + 1) := by
  have hd : trace.drop c.val.val = column trace c :: trace.drop (c.val.val + 1) :=
    List.drop_eq_getElem_cons c.val.isLt
  calc
    trace = trace.take c.val.val ++ trace.drop c.val.val :=
      (List.take_append_drop c.val.val trace).symm
    _ = _ := by rw [hd]

/--
@isnad1 id=eq.0h2v.s5.e4777a984300 from=translated src=- shape=a901a488 vocab=4e24fd75
-/
theorem source_split (trace : Trace) (c : EditColumn trace) :
    trace.source = sourcePrefix trace c ++
      Trace.source [column trace c] ++ sourceSuffix trace c := by
  calc
    trace.source = Trace.source
        (trace.take c.val.val ++ column trace c :: trace.drop (c.val.val + 1)) :=
      congrArg Trace.source (split_column trace c)
    _ = _ := by
      rw [Trace.source_append]
      cases hc : column trace c <;> simp [sourcePrefix, sourceSuffix, Trace.source]

/--
@isnad1 id=eq.0h2v.s5.af2122c7df39 from=translated src=- shape=a901a488 vocab=3dbdbdd6
-/
theorem target_split (trace : Trace) (c : EditColumn trace) :
    trace.target = targetPrefix trace c ++
      Trace.target [column trace c] ++ targetSuffix trace c := by
  calc
    trace.target = Trace.target
        (trace.take c.val.val ++ column trace c :: trace.drop (c.val.val + 1)) :=
      congrArg Trace.target (split_column trace c)
    _ = _ := by
      rw [Trace.target_append]
      cases hc : column trace c <;> simp [targetPrefix, targetSuffix, Trace.target]

/--
@isnad1 id=eq.1h3v.s5.f8b01c0c49a6 from=translated src=- shape=6d481080 vocab=5b57badf
-/
theorem source_split_of_deletion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .deletion b) :
    trace.source = sourcePrefix trace c ++ b :: sourceSuffix trace c := by
  simpa only [hc, Trace.source, List.append_assoc, List.singleton_append] using source_split trace c

/--
@isnad1 id=eq.1h3v.s5.e173d0d71358 from=translated src=- shape=3305a18c vocab=32b8416c
-/
theorem source_split_of_insertion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .insertion b) :
    trace.source = sourcePrefix trace c ++ sourceSuffix trace c := by
  simpa only [hc, Trace.source, List.append_nil] using source_split trace c

/--
@isnad1 id=eq.1h3v.s5.8fc0eee21cec from=translated src=- shape=3305a18c vocab=eb072550
-/
theorem target_split_of_deletion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .deletion b) :
    trace.target = targetPrefix trace c ++ targetSuffix trace c := by
  simpa only [hc, Trace.target, List.append_nil] using target_split trace c

/--
@isnad1 id=eq.1h3v.s5.3debbb5b6abe from=translated src=- shape=6d481080 vocab=601876a1
-/
theorem target_split_of_insertion (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .insertion b) :
    trace.target = targetPrefix trace c ++ b :: targetSuffix trace c := by
  simpa only [hc, Trace.target, List.append_assoc, List.singleton_append] using target_split trace c

/--
@isnad1 id=eq.1h3v.s5.c1f156122f7e from=translated src=- shape=cc652d35 vocab=a9e5b977
-/
theorem oneEditTarget_deletion_split (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .deletion b) :
    oneEditTarget trace c = sourcePrefix trace c ++ sourceSuffix trace c := by
  rw [oneEditTarget_of_deletion trace c b hc, position_eq_sourcePrefix_length,
    source_split_of_deletion trace c b hc]
  rw [List.eraseIdx_append_of_length_le (Nat.le_refl _)]
  simp

/--
@isnad1 id=eq.1h3v.s5.7f391cd866d8 from=translated src=- shape=eabc8e7d vocab=4eb0404e
-/
theorem oneEditTarget_insertion_split (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .insertion b) :
    oneEditTarget trace c = sourcePrefix trace c ++ b :: sourceSuffix trace c := by
  rw [oneEditTarget_of_insertion trace c b hc, position_eq_sourcePrefix_length,
    source_split_of_insertion trace c b hc]
  simp

/--
@isnad1 id=lt.1h3v.s4.83e297fd5c0d from=translated src=- shape=da44a4ad vocab=38e89295
-/
theorem deletion_position_lt (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .deletion b) : position trace c < trace.source.length := by
  have h := congrArg List.length (source_split_of_deletion trace c b hc)
  simp only [List.length_append, List.length_cons] at h
  rw [position_eq_sourcePrefix_length]
  omega

/--
@isnad1 id=le.1h3v.s4.50d64f92c75e from=translated src=- shape=da44a4ad vocab=76a1d553
-/
theorem insertion_position_le (trace : Trace) (c : EditColumn trace) (b : Bool)
    (hc : column trace c = .insertion b) : position trace c ≤ trace.source.length := by
  have h := congrArg List.length (source_split_of_insertion trace c b hc)
  simp only [List.length_append] at h
  rw [position_eq_sourcePrefix_length]
  omega

end DeletionCode.TraceEditData
