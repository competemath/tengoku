import Tengoku.SingularityCompleteLean.Singularity.InfiniteWalkProcess
import Tengoku.SingularityCompleteLean.Singularity.FirstEntrance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# First-entrance probabilities on the infinite path space

The finite path sums defining F(x,a) are now probabilities of disjoint first
entrance events under the actual infinite walk law. Their union identifies
the infinite-time first-entrance distribution.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Prefix avoidance is avoidance by the actual process at all earlier times.
@isnad1 id=iff.0h6v.s6.6c39f2ab58b7 from=translated src=- shape=af464361 vocab=30bc91f2
-/
theorem avoidsBefore_prefix_iff (s : Finset Γ) (A : Set Γ) (n : ℕ) (x : Γ) (ω : ℕ → s) :
    avoidsBefore s A n x (walkPrefix s n ω) ↔
      ∀ k < n, walkPosition s x k ω ∉ A := by
  induction n generalizing x ω with
  | zero => simp [avoidsBefore]
  | succ n ih =>
    change (x ∉ A ∧ avoidsBefore s A n (x * ω 0) (walkPrefix s n (fun k => ω (k + 1)))) ↔ _
    rw [ih]
    constructor
    · rintro ⟨hx, ht⟩ k hk
      cases k with
      | zero => exact hx
      | succ k => exact ht k (Nat.lt_of_succ_lt_succ hk)
    · intro h
      exact ⟨h 0 (Nat.zero_lt_succ n), fun k hk => h (k + 1) (Nat.succ_lt_succ hk)⟩

/-- First entrance into A at the vertex a and the time n.-/
def walkFirstEntranceEvent (s : Finset Γ) (A : Set Γ) (x a : Γ) (n : ℕ) : Set (ℕ → s) :=
  {ω | avoidsBefore s A n x (walkPrefix s n ω) ∧ walkPosition s x n ω = a ∧ a ∈ A}

/-- Eventual first entrance at a, at an arbitrary finite time.-/
def walkFirstEntranceEver (s : Finset Γ) (A : Set Γ) (x a : Γ) : Set (ℕ → s) :=
  ⋃ n : ℕ, walkFirstEntranceEvent s A x a n

/-- A first-entrance event specifies the current position and excludes all earlier visits.
@isnad1 id=iff.0h7v.s7.1a691860a9c2 from=translated src=- shape=de8361c5 vocab=2aa94439
-/
theorem mem_walkFirstEntranceEvent (s : Finset Γ) (A : Set Γ) (x a : Γ) (n : ℕ) (ω : ℕ → s) :
    ω ∈ walkFirstEntranceEvent s A x a n ↔
      (∀ k < n, walkPosition s x k ω ∉ A) ∧ walkPosition s x n ω = a ∧ a ∈ A := by
  change (_ ∧ _ ∧ _) ↔ _
  rw [avoidsBefore_prefix_iff]

/-- A path cannot first enter at two different times.
@isnad1 id=pairwise.0h5v.s8.a0cb089a5c59 from=translated src=- shape=a1223594 vocab=a41fe901
-/
theorem walkFirstEntranceEvent_disjoint (s : Finset Γ) (A : Set Γ) (x a : Γ) :
    Pairwise (fun n m => Disjoint (walkFirstEntranceEvent s A x a n) (walkFirstEntranceEvent s A x a m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  intro ω hn hm
  rw [mem_walkFirstEntranceEvent] at hn hm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact hm.1 n hlt (hn.2.1 ▸ hn.2.2)
  · exact hn.1 m hgt (hm.2.1 ▸ hm.2.2)

/-- Distinct entrance vertices give disjoint infinite-time first-entrance events.
@isnad1 id=pairwise.0h4v.s8.1a2849f7cf5d from=translated src=- shape=f10af189 vocab=95c70681
-/
theorem walkFirstEntranceEver_disjoint (s : Finset Γ) (A : Set Γ) (x : Γ) :
    Pairwise (fun a b => Disjoint (walkFirstEntranceEver s A x a) (walkFirstEntranceEver s A x b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro ω ha hb
  obtain ⟨n, hn⟩ := mem_iUnion.mp ha
  obtain ⟨m, hm⟩ := mem_iUnion.mp hb
  rw [mem_walkFirstEntranceEvent] at hn hm
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact hm.1 n hlt (hn.2.1 ▸ hn.2.2)
  · subst m
    exact hab (hn.2.1.symm.trans hm.2.1)
  · exact hn.1 m hgt (hm.2.1 ▸ hm.2.2)

/-- Visiting A at some finite time is the union over all possible entrance vertices.
@isnad1 id=eq.0h4v.s6.fab8726b4bca from=translated src=- shape=647e4532 vocab=cade275a
-/
theorem walk_hit_eq_union_firstEntrance (s : Finset Γ) (A : Set Γ) (x : Γ) :
    {ω : ℕ → s | ∃ n, walkPosition s x n ω ∈ A} = ⋃ a : Γ, walkFirstEntranceEver s A x a := by
  ext ω
  constructor
  · intro h
    let n := Nat.find h
    apply mem_iUnion.mpr
    refine ⟨walkPosition s x n ω, mem_iUnion.mpr ⟨n, ?_⟩⟩
    rw [mem_walkFirstEntranceEvent]
    exact ⟨fun k hk => Nat.find_min h hk, rfl, Nat.find_spec h⟩
  · intro h
    obtain ⟨a, ha⟩ := mem_iUnion.mp h
    obtain ⟨n, hn⟩ := mem_iUnion.mp ha
    rw [mem_walkFirstEntranceEvent] at hn
    exact ⟨n, hn.2.1 ▸ hn.2.2⟩

variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ]

/-- Finite-prefix first entrance is measurable, for every subset A of the group.
@isnad1 id=measurab.0h6v.s6.5c9e5cd42f97 from=translated src=- shape=580b3f05 vocab=e7d69dc2
-/
theorem measurableSet_walkFirstEntranceEvent (s : Finset Γ) (A : Set Γ) (x a : Γ) (n : ℕ) :
    MeasurableSet (walkFirstEntranceEvent s A x a n) := by
  have h : MeasurableSet {w : WalkWord s n | avoidsBefore s A n x w ∧
      walkEndpoint s n x w = a ∧ a ∈ A} := trivial
  exact h.preimage (measurable_walkPrefix s n)

/--
@isnad1 id=measurab.0h5v.s6.fd37982b0c3f from=translated src=- shape=671bbb4f vocab=214d459b
-/
theorem measurableSet_walkFirstEntranceEver (s : Finset Γ) (A : Set Γ) (x a : Γ) :
    MeasurableSet (walkFirstEntranceEver s A x a) :=
  MeasurableSet.iUnion (fun n => measurableSet_walkFirstEntranceEvent s A x a n)

/-- The finite first-entrance path weight is its actual probability.
@isnad1 id=eq.2h7v.s8.2fdb621779a6 from=translated src=- shape=8d21d8ac vocab=6386af48
-/
theorem walkFirstEntranceEvent_probability (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1) (A : Set Γ) (x a : Γ) (n : ℕ) :
    infiniteWalkLaw s μ hμ hmass (walkFirstEntranceEvent s A x a n) =
      ENNReal.ofReal (firstEntranceWeight s μ A n x a) := by
  let S : Set (WalkWord s n) := {w | avoidsBefore s A n x w ∧ walkEndpoint s n x w = a ∧ a ∈ A}
  have hS : MeasurableSet S := trivial
  change infiniteWalkLaw s μ hμ hmass (walkPrefix s n ⁻¹' S) = _
  rw [← Measure.map_apply (measurable_walkPrefix s n) hS, infiniteWalkLaw_prefix,
    PMF.toMeasure_apply _ hS, tsum_fintype, firstEntranceWeight, ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro w _
    simp only [Set.indicator_apply, S, Set.mem_ofPred_eq, finiteWalkLaw_apply]
    split_ifs <;> simp
  · intro w _
    split_ifs
    · exact walkWeight_nonneg s μ hμ n w
    · exact le_rfl

variable [MeasurableMul Γ]

end Singularity
