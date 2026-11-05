import Tengoku.NsP23.P23.OneTie.SocleDownset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Phase 1: minimal combinatorial border

The border is defined directly by killedness and survival of every applicable
variable predecessor. No polynomial ideal or Artin quotient is introduced.
-/

namespace P23.OneTie

variable {a b c : ℕ} [NeZero a]

/-- Every applicable immediate variable predecessor of `m` lies in `O`.-/
def ApplicablePredecessorsSurvive (O : Set (Normal a b c)) (m : Normal a b c) : Prop :=
  (∀ q, Normal.predecessor .x m = some q → q ∈ O) ∧
  (∀ q, Normal.predecessor .y m = some q → q ∈ O) ∧
  (∀ q, Normal.predecessor .z m = some q → q ∈ O)

/-- A killed normal monomial whose applicable variable predecessors survive.-/
def IsMinimalBorder (O : Set (Normal a b c)) (m : Normal a b c) : Prop :=
  m ∉ O ∧ ApplicablePredecessorsSurvive O m

/-- Load-bearing minimal-border criterion in direction-uniform form.-/
theorem isMinimalBorder_iff (O : Set (Normal a b c)) (m : Normal a b c) :
    IsMinimalBorder O m ↔
      m ∉ O ∧ ∀ e q, Normal.predecessor e m = some q → q ∈ O := by
  constructor
  · rintro ⟨hm, hx, hy, hz⟩
    refine ⟨hm, ?_⟩
    intro e q hq
    cases e with
    | x => exact hx q hq
    | y => exact hy q hq
    | z => exact hz q hq
  · rintro ⟨hm, hpred⟩
    exact ⟨hm, hpred .x, hpred .y, hpred .z⟩

/-- A finite generator-multiple candidate set, filtered by the minimal-border
predicate. It is intentionally not named as the exact border: for an empty
socle set, the vacuous minimal border contains `1` while this candidate set is
empty.-/
noncomputable def borderCandidateFinset (S : Finset (Normal a b c)) :
    Finset (Normal a b c) := by
  classical
  let candidates :=
    (standardFinset S).biUnion fun p =>
      {p * Normal.xGenerator, p * Normal.yGenerator, p * Normal.zGenerator}
  exact candidates.filter fun m => IsMinimalBorder (standardSet S) m

theorem mem_borderCandidateFinset_iff (S : Finset (Normal a b c))
    (m : Normal a b c) :
    m ∈ borderCandidateFinset S ↔
      m ∈ (standardFinset S).biUnion (fun p =>
        {p * Normal.xGenerator, p * Normal.yGenerator, p * Normal.zGenerator}) ∧
      IsMinimalBorder (standardSet S) m := by
  classical
  simp [borderCandidateFinset]

/-- A nonempty socle finset generates a standard set containing the unit.-/
theorem one_mem_standardSet_of_nonempty {S : Finset (Normal a b c)}
    (hS : S.Nonempty) : (1 : Normal a b c) ∈ standardSet S := by
  rcases hS with ⟨s, hs⟩
  exact ⟨s, hs, one_dvd s⟩

/-- Every non-unit normal form has an applicable variable predecessor.-/
theorem exists_predecessor_of_ne_one (m : Normal a b c) (hm : m ≠ 1) :
    ∃ e q, Normal.predecessor e m = some q := by
  by_cases hx : 0 < m.x
  · exact ⟨.x, Normal.xPredecessor m hx, Normal.predecessor_x_of_pos m hx⟩
  have hx0 : m.x = 0 := by omega
  by_cases hy : 0 < m.y
  · exact ⟨.y, Normal.yPredecessor m hy, Normal.predecessor_y_of_pos m hy⟩
  have hy0 : m.y = 0 := by omega
  by_cases hz : 0 < m.z
  · exact ⟨.z, Normal.zPredecessor m hz, Normal.predecessor_z_of_pos m hz⟩
  have hz0 : m.z = 0 := by omega
  exfalso
  apply hm
  apply Normal.ext <;> simp [hx0, hy0, hz0]

/-- Over a nonempty socle finset, every minimal border point occurs among the
generator multiples used by `borderCandidateFinset`.-/
theorem minimalBorder_mem_borderCandidateFinset {S : Finset (Normal a b c)}
    (hS : S.Nonempty) {m : Normal a b c}
    (hm : IsMinimalBorder (standardSet S) m) :
    m ∈ borderCandidateFinset S := by
  have hm1 : m ≠ 1 := by
    intro h
    subst m
    exact hm.1 (one_mem_standardSet_of_nonempty hS)
  rcases exists_predecessor_of_ne_one m hm1 with ⟨e, q, hpred⟩
  have hqSet : q ∈ standardSet S := (isMinimalBorder_iff _ _).1 hm |>.2 e q hpred
  have hqFin : q ∈ standardFinset S :=
    (mem_standardFinset_iff_standardSet S q).2 hqSet
  apply (mem_borderCandidateFinset_iff S m).2
  refine ⟨Finset.mem_biUnion.mpr ⟨q, hqFin, ?_⟩, hm⟩
  have hmul := (Normal.predecessor_eq_some_iff_mul e m q).1 hpred
  cases e <;> simp_all [Direction.generator]

/-- The exact finite minimal border used by Run 03.  Exactness is asserted
only for nonempty socle finsets, keeping the empty-socle unit edge case
explicit.-/
noncomputable def borderFinset (S : Finset (Normal a b c)) :
    Finset (Normal a b c) :=
  borderCandidateFinset S

theorem mem_borderFinset_iff {S : Finset (Normal a b c)}
    (hS : S.Nonempty) (m : Normal a b c) :
    m ∈ borderFinset S ↔ IsMinimalBorder (standardSet S) m := by
  constructor
  · intro hm
    exact ((mem_borderCandidateFinset_iff S m).1 hm).2
  · intro hm
    exact minimalBorder_mem_borderCandidateFinset hS hm

end P23.OneTie
