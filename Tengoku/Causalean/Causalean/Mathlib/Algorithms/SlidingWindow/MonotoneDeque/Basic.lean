module
public import Tengoku

/-!
# Finite streams and monotone contiguous window schedules

This module gives the paper-independent input model for a monotone-window scan: a finite prefix of
an ordered value function, bounded half-open windows, and a finite schedule whose two endpoints are
nondecreasing.  It also relates predicate, list, and finset views of a window, including empty
windows.
-/

@[expose] public section

namespace Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque

/-- A finite ordered stream of [values in a type](hyp:α) records its length and value at each
natural-number index. -/
structure Stream (α : Type*) where
  length : ℕ
  value : ℕ → α

/-- A contiguous half-open window in a stream of [given length](hyp:n) has a left endpoint no
larger than its right endpoint, which does not exceed the stream length. -/
structure Window (n : ℕ) where
  left : ℕ
  right : ℕ
  left_le_right : left ≤ right
  right_le_length : right ≤ n

/-- [A left endpoint](hyp:left), [a right endpoint](hyp:right), and [an index](hyp:i) determine
[whether the index is active in the half-open interval](goal). -/
def ActiveAt (left right i : ℕ) : Prop := left ≤ i ∧ i < right

/-- [A bounded window](hyp:w) and [an index](hyp:i) determine [whether the index is active in
that window](goal). -/
def Active {n : ℕ} (w : Window n) (i : ℕ) : Prop := ActiveAt w.left w.right i

/-- [A bounded window](hyp:w) determines [its increasing list of active indices](goal). -/
def Window.indices {n : ℕ} (w : Window n) : List ℕ :=
  List.range' w.left (w.right - w.left)

/-- [A bounded window](hyp:w) determines [its finite set of active indices](goal). -/
def Window.indexFinset {n : ℕ} (w : Window n) : Finset ℕ := Finset.Ico w.left w.right

/-- [A bounded window](hyp:w) has [the same active indices in its list enumeration and in its
active-window condition](goal).
@isnad1 id=iff.0h3v.s4.97cef4b095aa from=translated src=- shape=eb04fae5 vocab=1ad1380b
-/
theorem Window.mem_indices_iff {n i : ℕ} (w : Window n) : i ∈ w.indices ↔ Active w i := by
  rw [Window.indices, List.mem_range'_1, Nat.add_sub_of_le w.left_le_right]
  rfl

/-- [A bounded window](hyp:w) has [the same active indices in its finite-set enumeration and in
its active-window condition](goal).
@isnad1 id=iff.0h3v.s4.235d6b2eaba4 from=translated src=- shape=eb04fae5 vocab=628749f5
-/
theorem Window.mem_indexFinset_iff {n i : ℕ} (w : Window n) : i ∈ w.indexFinset ↔ Active w i := by
  simp [Window.indexFinset, Active, ActiveAt]

/-- [A bounded window](hyp:w) has [as many active indices as its width](goal).
@isnad1 id=eq.0h2v.s4.6fe0bb6a5732 from=translated src=- shape=08b6c798 vocab=4ec46c30
-/
theorem Window.card_indexFinset {n : ℕ} (w : Window n) :
    w.indexFinset.card = w.right - w.left := by
  simp [Window.indexFinset]

/-- [A bounded window](hyp:w) has
[an empty index list exactly when its two endpoints coincide](goal).
@isnad1 id=iff.0h2v.s4.4a166c721076 from=translated src=- shape=907a09bf vocab=e13bd60a
-/
theorem Window.indices_eq_nil_iff {n : ℕ} (w : Window n) :
    w.indices = [] ↔ w.left = w.right := by
  constructor
  · intro h
    have hlen : w.indices.length = 0 := by simp [h]
    rw [Window.indices, List.length_range'] at hlen
    exact Nat.le_antisymm w.left_le_right (Nat.sub_eq_zero_iff_le.mp hlen)
  · intro h
    simp [Window.indices, h]

/-- [A bounded window](hyp:w) has [an active index exactly when its left endpoint is strictly
below its right endpoint](goal).
@isnad1 id=iff.0h2v.s4.f6ac740d7535 from=translated src=- shape=1b979fca vocab=8ffa1696
-/
theorem Window.indexFinset_nonempty_iff {n : ℕ} (w : Window n) :
    w.indexFinset.Nonempty ↔ w.left < w.right := by
  simp [Window.indexFinset]

/-- A finite schedule for a stream of [given length](hyp:n) contains bounded windows with
nondecreasing left and right endpoints. -/
structure Schedule (n : ℕ) where
  windows : List (Window n)
  left_mono : windows.Pairwise (fun a b => a.left ≤ b.left)
  right_mono : windows.Pairwise (fun a b => a.right ≤ b.right)

/-- [A finite schedule](hyp:schedule) determines [its number of scheduled windows](goal). -/
def Schedule.steps {n : ℕ} (schedule : Schedule n) : ℕ := schedule.windows.length

/-- [A finite schedule](hyp:schedule), [two valid schedule positions](hyp:hi,hj), and [their
strict order](hyp:hij) ensure [that the earlier left endpoint is no larger](goal).
@isnad1 id=le.3h4v.s6.986fba5b0e74 from=translated src=- shape=d2817d8d vocab=19afb9d2
-/
theorem Schedule.left_le_of_get_lt {n : ℕ} (schedule : Schedule n)
    {i j : ℕ} (hi : i < schedule.steps) (hj : j < schedule.steps) (hij : i < j) :
    (schedule.windows.get ⟨i, hi⟩).left ≤ (schedule.windows.get ⟨j, hj⟩).left := by
  exact schedule.left_mono.rel_get_of_lt hij

/-- [A finite schedule](hyp:schedule), [two valid schedule positions](hyp:hi,hj), and [their
strict order](hyp:hij) ensure [that the earlier right endpoint is no larger](goal).
@isnad1 id=le.3h4v.s6.f0e30fa93e2a from=translated src=- shape=d2817d8d vocab=e636b533
-/
theorem Schedule.right_le_of_get_lt {n : ℕ} (schedule : Schedule n)
    {i j : ℕ} (hi : i < schedule.steps) (hj : j < schedule.steps) (hij : i < j) :
    (schedule.windows.get ⟨i, hi⟩).right ≤ (schedule.windows.get ⟨j, hj⟩).right := by
  exact schedule.right_mono.rel_get_of_lt hij

end Causalean.Mathlib.Algorithms.SlidingWindow.MonotoneDeque
