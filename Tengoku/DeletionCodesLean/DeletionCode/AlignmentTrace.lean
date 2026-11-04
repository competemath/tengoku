import Tengoku.DeletionCodesLean.DeletionCode.EditAlignment

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Trace.alignment` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms alignment_iff_exists_trace` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Trace.matchedAnchor_at_column` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Trace.sourcePosition_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Trace.matchedAnchor_end_eq_sub` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms trace_of_equal_length_confusability` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Explicit alignment data. Unlike the proposition EditAlignment.Alignment, a
trace retains which matched and edit columns were used. Its projections and
counters compute the two words and exact edit counts. Matched-column anchors
are counts in the actual preceding prefix, as in the manuscript; no separation
convention is imposed here.
-/

namespace DeletionCode.AlignmentTrace

open EditAlignment

inductive Column where
  | matched (bit : Bool)
  | deletion (bit : Bool)
  | insertion (bit : Bool)
  deriving DecidableEq, Repr

def Column.isEdit : Column → Bool
  | .matched _ => false
  | .deletion _ => true
  | .insertion _ => true

abbrev Trace := List Column

namespace Trace

def source : Trace → Word
  | [] => []
  | .matched bit :: rest => bit :: source rest
  | .deletion bit :: rest => bit :: source rest
  | .insertion _ :: rest => source rest

def target : Trace → Word
  | [] => []
  | .matched bit :: rest => bit :: target rest
  | .deletion _ :: rest => target rest
  | .insertion bit :: rest => bit :: target rest

def deletions : Trace → ℕ
  | [] => 0
  | .matched _ :: rest => deletions rest
  | .deletion _ :: rest => deletions rest + 1
  | .insertion _ :: rest => deletions rest

def insertions : Trace → ℕ
  | [] => 0
  | .matched _ :: rest => insertions rest
  | .deletion _ :: rest => insertions rest
  | .insertion _ :: rest => insertions rest + 1

def matchedCount : Trace → ℕ
  | [] => 0
  | .matched _ :: rest => matchedCount rest + 1
  | .deletion _ :: rest => matchedCount rest
  | .insertion _ :: rest => matchedCount rest

/--
@isnad1 id=eq.0h2v.s4.91b1461c00fd from=translated src=- shape=0438c7a3 vocab=1ce8dea5
-/
theorem source_append (left right : Trace) :
    source (left ++ right) = source left ++ source right := by
  induction left with
  | nil => rfl
  | cons col rest ih => cases col <;> simp [source, ih]

/--
@isnad1 id=eq.0h2v.s4.d976df34c339 from=translated src=- shape=0438c7a3 vocab=bab9af57
-/
theorem target_append (left right : Trace) :
    target (left ++ right) = target left ++ target right := by
  induction left with
  | nil => rfl
  | cons col rest ih => cases col <;> simp [target, ih]

/--
@isnad1 id=eq.0h2v.s4.3d29f2bb9ce6 from=translated src=- shape=0438c7a3 vocab=3484f22f
-/
theorem deletions_append (left right : Trace) :
    deletions (left ++ right) = deletions left + deletions right := by
  induction left with
  | nil => simp [deletions]
  | cons col rest ih =>
    cases col <;> simp only [List.cons_append, deletions, ih] <;> omega

/--
@isnad1 id=eq.0h2v.s4.60ea8952ab8d from=translated src=- shape=0438c7a3 vocab=d95c8e63
-/
theorem insertions_append (left right : Trace) :
    insertions (left ++ right) = insertions left + insertions right := by
  induction left with
  | nil => simp [insertions]
  | cons col rest ih =>
    cases col <;> simp only [List.cons_append, insertions, ih] <;> omega

/--
@isnad1 id=eq.0h2v.s4.c91c414a0faa from=translated src=- shape=0438c7a3 vocab=ac9880c4
-/
theorem matchedCount_append (left right : Trace) :
    matchedCount (left ++ right) = matchedCount left + matchedCount right := by
  induction left with
  | nil => simp [matchedCount]
  | cons col rest ih =>
    cases col <;> simp only [List.cons_append, matchedCount, ih] <;> omega

/--
@isnad1 id=eq.0h1v.s4.20f8c665a682 from=translated src=- shape=1e99ff92 vocab=8a5219ea
-/
theorem source_length (trace : Trace) :
    trace.source.length = trace.matchedCount + trace.deletions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;> simp only [source, matchedCount, deletions, List.length_cons] <;> omega

/--
@isnad1 id=eq.0h1v.s4.84c4d6e0fb95 from=translated src=- shape=1e99ff92 vocab=998db6c5
-/
theorem target_length (trace : Trace) :
    trace.target.length = trace.matchedCount + trace.insertions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;> simp only [target, matchedCount, insertions, List.length_cons] <;> omega

/--
@isnad1 id=eq.0h1v.s4.115ef79cc734 from=translated src=- shape=af6e1451 vocab=632f27c0
-/
theorem length_eq_counts (trace : Trace) :
    trace.length = trace.matchedCount + trace.deletions + trace.insertions := by
  induction trace with
  | nil => rfl
  | cons col rest ih =>
    cases col <;>
      simp only [List.length_cons, matchedCount, deletions, insertions] <;> omega

/-- Every computational trace is a genuine alignment of its projections.
@isnad1 id=alignmen.0h1v.s3.7ba7f749ec93 from=translated src=- shape=7c615e45 vocab=eafeab3c
-/
theorem alignment (trace : Trace) :
    Alignment trace.source trace.target trace.deletions trace.insertions := by
  induction trace with
  | nil => exact Alignment.nil
  | cons col rest ih =>
    cases col with
    | matched bit => exact Alignment.matched bit ih
    | deletion bit => exact Alignment.deletion bit ih
    | insertion bit => exact Alignment.insertion bit ih

/-- Number of matched columns strictly before column j. At j = trace.length,
this is the right boundary anchor. Indices beyond the trace saturate there.-/
def matchedAnchor (trace : Trace) (j : ℕ) : ℕ := matchedCount (trace.take j)

/-- Number of source letters strictly before column j, counting deletions.-/
def sourcePosition (trace : Trace) (j : ℕ) : ℕ := (source (trace.take j)).length

/-- Number of target letters strictly before column j, counting insertions.-/
def targetPosition (trace : Trace) (j : ℕ) : ℕ := (target (trace.take j)).length

/--
@isnad1 id=eq.0h3v.s4.8520810eeb0a from=translated src=- shape=1ab5d54a vocab=e5a57364
-/
theorem matchedAnchor_at_column (pre suffix : Trace) (col : Column) :
    matchedAnchor (pre ++ col :: suffix) pre.length = pre.matchedCount := by
  simp [matchedAnchor]

/--
@isnad1 id=eq.0h3v.s4.0f354934288e from=translated src=- shape=094c4845 vocab=bec6ca2b
-/
theorem sourcePosition_at_column (pre suffix : Trace) (col : Column) :
    sourcePosition (pre ++ col :: suffix) pre.length = pre.source.length := by
  simp [sourcePosition]

/--
@isnad1 id=eq.0h3v.s4.757e2bf360fb from=translated src=- shape=094c4845 vocab=1f7a865e
-/
theorem targetPosition_at_column (pre suffix : Trace) (col : Column) :
    targetPosition (pre ++ col :: suffix) pre.length = pre.target.length := by
  simp [targetPosition]

/--
@isnad1 id=eq.0h1v.s4.620b0069bb4a from=translated src=- shape=9b4d794a vocab=832103fb
-/
@[simp] theorem matchedAnchor_zero (trace : Trace) : matchedAnchor trace 0 = 0 := rfl

/--
@isnad1 id=eq.0h1v.s3.fcd80fa4c91b from=translated src=- shape=59dbbc29 vocab=798705b6
-/
@[simp] theorem matchedAnchor_end (trace : Trace) :
    matchedAnchor trace trace.length = trace.matchedCount := by
  simp [matchedAnchor]

/--
@isnad1 id=le.0h2v.s3.80ddf1af2453 from=translated src=- shape=7c82f523 vocab=793e96dd
-/
theorem matchedAnchor_le (trace : Trace) (j : ℕ) :
    matchedAnchor trace j ≤ trace.matchedCount := by
  have h := matchedCount_append (trace.take j) (trace.drop j)
  rw [List.take_append_drop] at h
  unfold matchedAnchor
  omega

/-- The source position is the matched anchor plus preceding deletions.
@isnad1 id=eq.0h2v.s4.7e8a28cc0eb8 from=translated src=- shape=5e57ec02 vocab=b94f9206
-/
theorem sourcePosition_eq (trace : Trace) (j : ℕ) :
    sourcePosition trace j = matchedAnchor trace j + deletions (trace.take j) :=
  source_length (trace.take j)

/-- The target position is the matched anchor plus preceding insertions.
@isnad1 id=eq.0h2v.s4.1ce9e75de69a from=translated src=- shape=5e57ec02 vocab=500b45a4
-/
theorem targetPosition_eq (trace : Trace) (j : ℕ) :
    targetPosition trace j = matchedAnchor trace j + insertions (trace.take j) :=
  target_length (trace.take j)

/-- For a source of length n with d deletions, the right boundary anchor is n-d.
@isnad1 id=eq.2h3v.s5.d49fef4a02c3 from=translated src=- shape=dad82d0a vocab=3889939c
-/
theorem matchedAnchor_end_eq_sub (trace : Trace) (n d : ℕ)
    (hsource : trace.source.length = n) (hdel : trace.deletions = d) :
    matchedAnchor trace trace.length = n - d := by
  rw [matchedAnchor_end]
  have h := source_length trace
  omega

end Trace

/-- Propositional alignability has an explicit trace witness. Different
traces can remain distinct data even when their word projections agree.
@isnad1 id=ex.1h4v.s5.c39f76d1ee8a from=translated src=- shape=b215d865 vocab=c98cc937
-/
theorem exists_trace_of_alignment {y z : Word} {d i : ℕ}
    (h : Alignment y z d i) :
    ∃ trace : Trace, trace.source = y ∧ trace.target = z ∧
      trace.deletions = d ∧ trace.insertions = i := by
  induction h with
  | nil => exact ⟨[], rfl, rfl, rfl, rfl⟩
  | matched bit h ih =>
    obtain ⟨trace, hs, ht, hd, hi⟩ := ih
    refine ⟨Column.matched bit :: trace, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Trace.source, Trace.target, Trace.deletions, Trace.insertions, hs, ht, hd, hi]
  | deletion bit h ih =>
    obtain ⟨trace, hs, ht, hd, hi⟩ := ih
    refine ⟨Column.deletion bit :: trace, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Trace.source, Trace.target, Trace.deletions, Trace.insertions, hs, ht, hd, hi]
  | insertion bit h ih =>
    obtain ⟨trace, hs, ht, hd, hi⟩ := ih
    refine ⟨Column.insertion bit :: trace, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Trace.source, Trace.target, Trace.deletions, Trace.insertions, hs, ht, hd, hi]

/-- Exact equivalence with the already verified alignment proposition.
@isnad1 id=iff.0h4v.s5.c745d0d81f66 from=translated src=- shape=47b177c7 vocab=c98cc937
-/
theorem alignment_iff_exists_trace (y z : Word) (d i : ℕ) :
    Alignment y z d i ↔
      ∃ trace : Trace, trace.source = y ∧ trace.target = z ∧
        trace.deletions = d ∧ trace.insertions = i := by
  constructor
  · exact exists_trace_of_alignment
  · rintro ⟨trace, rfl, rfl, rfl, rfl⟩
    exact trace.alignment

/-- Confusability yields actual finite alignment data with the exact counters.
@isnad1 id=ex.4h5v.s6.2503fbd2331a from=translated src=- shape=7bc51b8f vocab=aedc8182
-/
theorem trace_of_equal_length_confusability (y z u : Word) (n t : ℕ)
    (hy : y.length = n) (hz : z.length = n)
    (hyu : WithinEdits t y u) (hzu : WithinEdits t z u) :
    ∃ (d : ℕ) (trace : Trace), d ≤ t ∧ trace.source = y ∧ trace.target = z ∧
      trace.deletions = d ∧ trace.insertions = d := by
  obtain ⟨d, hd, halign⟩ := equal_length_confusability y z u n t hy hz hyu hzu
  obtain ⟨trace, hs, ht, hdel, hins⟩ := exists_trace_of_alignment halign
  exact ⟨d, trace, hd, hs, ht, hdel, hins⟩

end DeletionCode.AlignmentTrace
