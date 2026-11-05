import Tengoku.NsP23.P23.OneTie.Border

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Phase 1: directional centres

This is the combinatorial DC predicate only. No implication from nearly
Gorensteinness or canonical trace is asserted here.
-/

namespace P23.OneTie

variable {a b c : ℕ} [NeZero a]

/-- A selected root containing every existing `e`-predecessor of every root.-/
def IsDirectionalCentre (S : Finset (Normal a b c)) (e : Direction)
    (centre : Normal a b c) : Prop :=
  centre ∈ S ∧
    ∀ s ∈ S, ∀ q, Normal.predecessor e s = some q → q ∈ Normal.divisorDownset centre

/-- Each variable direction has a (not necessarily common) selected centre.-/
def HasDirectionalCentres (S : Finset (Normal a b c)) : Prop :=
  ∀ e, ∃ centre, IsDirectionalCentre S e centre

private theorem isDirectionalCentre_y_criterion_iff (S : Finset (Normal a b c))
    (centre : Normal a b c) :
    IsDirectionalCentre S .y centre ↔
      centre ∈ S ∧ ∀ s ∈ S, ∀ hy : 0 < s.y,
        Normal.DividesCriterion (Normal.yPredecessor s hy) centre := by
  constructor
  · rintro ⟨hc, hpred⟩
    refine ⟨hc, ?_⟩
    intro s hs hy
    apply (Normal.mem_divisorDownset_iff _ _).1
    exact hpred s hs _ (Normal.predecessor_y_of_pos s hy)
  · rintro ⟨hc, hcoord⟩
    refine ⟨hc, ?_⟩
    intro s hs q hq
    by_cases hy : 0 < s.y
    · have heq := Normal.predecessor_y_of_pos s hy
      rw [heq] at hq
      have hq' : q = Normal.yPredecessor s hy := by simpa using hq.symm
      subst q
      exact (Normal.mem_divisorDownset_iff _ _).2 (hcoord s hs hy)
    · have hzero : s.y = 0 := by omega
      rw [Normal.predecessor_y_none s hzero] at hq
      contradiction

private theorem isDirectionalCentre_z_criterion_iff (S : Finset (Normal a b c))
    (centre : Normal a b c) :
    IsDirectionalCentre S .z centre ↔
      centre ∈ S ∧ ∀ s ∈ S, ∀ hz : 0 < s.z,
        Normal.DividesCriterion (Normal.zPredecessor s hz) centre := by
  constructor
  · rintro ⟨hc, hpred⟩
    refine ⟨hc, ?_⟩
    intro s hs hz
    apply (Normal.mem_divisorDownset_iff _ _).1
    exact hpred s hs _ (Normal.predecessor_z_of_pos s hz)
  · rintro ⟨hc, hcoord⟩
    refine ⟨hc, ?_⟩
    intro s hs q hq
    by_cases hz : 0 < s.z
    · have heq := Normal.predecessor_z_of_pos s hz
      rw [heq] at hq
      have hq' : q = Normal.zPredecessor s hz := by simpa using hq.symm
      subst q
      exact (Normal.mem_divisorDownset_iff _ _).2 (hcoord s hs hz)
    · have hzero : s.z = 0 := by omega
      rw [Normal.predecessor_z_none s hzero] at hq
      contradiction

private theorem isDirectionalCentre_x_criterion_iff (S : Finset (Normal a b c))
    (centre : Normal a b c) :
    IsDirectionalCentre S .x centre ↔
      centre ∈ S ∧ ∀ s ∈ S,
        (∀ hx : 0 < s.x,
          Normal.DividesCriterion (Normal.xPredecessor s hx) centre) ∧
        (∀ hsx : s.x = 0, ∀ hy : b ≤ s.y, ∀ hz : c ≤ s.z,
          Normal.DividesCriterion (Normal.wrappedXPredecessor s hsx hy hz)
            centre) := by
  constructor
  · rintro ⟨hc, hpred⟩
    refine ⟨hc, ?_⟩
    intro s hs
    constructor
    · intro hx
      apply (Normal.mem_divisorDownset_iff _ _).1
      exact hpred s hs _ (Normal.predecessor_x_of_pos s hx)
    · intro hsx hy hz
      apply (Normal.mem_divisorDownset_iff _ _).1
      exact hpred s hs _ (Normal.predecessor_x_wrapped s hsx hy hz)
  · rintro ⟨hc, hcoord⟩
    refine ⟨hc, ?_⟩
    intro s hs q hq
    by_cases hx : 0 < s.x
    · have heq := Normal.predecessor_x_of_pos s hx
      rw [heq] at hq
      have hq' : q = Normal.xPredecessor s hx := by simpa using hq.symm
      subst q
      exact (Normal.mem_divisorDownset_iff _ _).2 ((hcoord s hs).1 hx)
    · have hsx : s.x = 0 := by omega
      by_cases hw : b ≤ s.y ∧ c ≤ s.z
      · have heq := Normal.predecessor_x_wrapped s hsx hw.1 hw.2
        rw [heq] at hq
        have hq' : q = Normal.wrappedXPredecessor s hsx hw.1 hw.2 := by
          simpa using hq.symm
        subst q
        exact (Normal.mem_divisorDownset_iff _ _).2
          ((hcoord s hs).2 hsx hw.1 hw.2)
      · rw [Normal.predecessor_x_none s hsx hw] at hq
        contradiction

/-- The `y`-direction centre condition, fully expanded into coordinate inequalities.-/
theorem isDirectionalCentre_y_iff (S : Finset (Normal a b c))
    (centre : Normal a b c) :
    IsDirectionalCentre S .y centre ↔
      centre ∈ S ∧ ∀ s ∈ S, ∀ _hy : 0 < s.y,
        s.y - 1 ≤ centre.y ∧ s.z ≤ centre.z ∧
          (s.x ≤ centre.x ∨
            (s.y - 1 + b ≤ centre.y ∧ s.z + c ≤ centre.z)) := by
  simpa [Normal.DividesCriterion, Normal.yPredecessor] using
    (isDirectionalCentre_y_criterion_iff S centre)

/-- The `z`-direction centre condition, fully expanded into coordinate inequalities.-/
theorem isDirectionalCentre_z_iff (S : Finset (Normal a b c))
    (centre : Normal a b c) :
    IsDirectionalCentre S .z centre ↔
      centre ∈ S ∧ ∀ s ∈ S, ∀ _hz : 0 < s.z,
        s.y ≤ centre.y ∧ s.z - 1 ≤ centre.z ∧
          (s.x ≤ centre.x ∨
            (s.y + b ≤ centre.y ∧ s.z - 1 + c ≤ centre.z)) := by
  simpa [Normal.DividesCriterion, Normal.zPredecessor] using
    (isDirectionalCentre_z_criterion_iff S centre)

/-- The ordinary and wrapped `x`-direction centre conditions, fully expanded
into coordinate inequalities.-/
theorem isDirectionalCentre_x_iff (S : Finset (Normal a b c))
    (centre : Normal a b c) :
    IsDirectionalCentre S .x centre ↔
      centre ∈ S ∧ ∀ s ∈ S,
        (∀ _hx : 0 < s.x,
          s.y ≤ centre.y ∧ s.z ≤ centre.z ∧
            (s.x - 1 ≤ centre.x ∨
              (s.y + b ≤ centre.y ∧ s.z + c ≤ centre.z))) ∧
        (∀ _hsx : s.x = 0, ∀ _hy : b ≤ s.y, ∀ _hz : c ≤ s.z,
          s.y - b ≤ centre.y ∧ s.z - c ≤ centre.z ∧
            (a - 1 ≤ centre.x ∨
              (s.y - b + b ≤ centre.y ∧ s.z - c + c ≤ centre.z))) := by
  simpa [Normal.DividesCriterion, Normal.xPredecessor,
    Normal.wrappedXPredecessor] using
    (isDirectionalCentre_x_criterion_iff S centre)

end P23.OneTie
