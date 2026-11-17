import Tengoku.SingularityCompleteLean.Singularity.WalkPrefixTail
import Tengoku.SingularityCompleteLean.Singularity.InfiniteFirstEntrance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Last-exit events and their exact probability

The probability of the last visit at a specified vertex and time factors into
a transition probability and a no-return probability. Summing over time gives
the Green kernel times the actual no-return probability.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Classical
namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- No visit to A at any strictly positive time, starting at a.-/
def walkNoReturnEvent (s : Finset Γ) (A : Set Γ) (a : Γ) : Set (ℕ → s) :=
  {ω | ∀ k : ℕ, 0 < k → walkPosition s a k ω ∉ A}

/-- The last visit to A is at vertex a at time n.-/
def walkLastExitEvent (s : Finset Γ) (A : Set Γ) (x a : Γ) (n : ℕ) : Set (ℕ → s) :=
  {ω | walkPosition s x n ω = a ∧ a ∈ A ∧ ∀ k : ℕ, n < k → walkPosition s x k ω ∉ A}

/-- The last visit to A is at a, at some finite time.-/
def walkLastExitEver (s : Finset Γ) (A : Set Γ) (x a : Γ) : Set (ℕ → s) :=
  ⋃ n : ℕ, walkLastExitEvent s A x a n

/-- Splitting a path at time n expresses last exit as a present-position event
and a future no-return event.
@isnad1 id=eq.1h6v.s7.8cab39863207 from=translated src=- shape=1dd2f3c5 vocab=ec4e446a
-/
theorem walkLastExitEvent_eq_inter (s : Finset Γ) (A : Set Γ) (x a : Γ)
    (ha : a ∈ A) (n : ℕ) :
    walkLastExitEvent s A x a n = {ω | walkPosition s x n ω = a} ∩
      (fun ω k => ω (k + n)) ⁻¹' walkNoReturnEvent s A a := by
  ext ω
  have he (h : walkPosition s x n ω = a) (k : ℕ) :
      walkPosition s x (n + k) ω = walkPosition s a k (fun j => ω (j + n)) := by
    rw [walkPosition_add, h]
    simpa only [mul_one] using (walkPosition_left s a 1 k (fun j => ω (j + n))).symm
  constructor
  · rintro ⟨hp, _, ht⟩
    refine ⟨hp, fun k hk => ?_⟩
    rw [← he hp k]
    exact ht (n + k) (by omega)
  · rintro ⟨hp, ht⟩
    refine ⟨hp, ha, fun k hk => ?_⟩
    have hh := ht (k - n) (by omega)
    rw [← he hp (k - n), Nat.add_sub_of_le (by omega)] at hh
    exact hh

/-- Distinct last-exit times are mutually exclusive.
@isnad1 id=pairwise.0h5v.s8.0840d23e1607 from=translated src=- shape=a1223594 vocab=e60131ba
-/
theorem walkLastExitEvent_disjoint (s : Finset Γ) (A : Set Γ) (x a : Γ) :
    Pairwise (fun n m => Disjoint (walkLastExitEvent s A x a n) (walkLastExitEvent s A x a m)) := by
  intro n m hnm
  apply Set.disjoint_left.mpr
  rintro ω ⟨hn, ha, hnt⟩ ⟨hm, _, hmt⟩
  rcases lt_or_gt_of_ne hnm with h | h
  · exact hnt m h (hm ▸ ha)
  · exact hmt n h (hn ▸ ha)

/-- Distinct last-exit vertices are mutually exclusive.
@isnad1 id=pairwise.0h4v.s8.2f589c899022 from=translated src=- shape=f10af189 vocab=dbcbc5fb
-/
theorem walkLastExitEver_disjoint (s : Finset Γ) (A : Set Γ) (x : Γ) :
    Pairwise (fun a b => Disjoint (walkLastExitEver s A x a) (walkLastExitEver s A x b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro ω ha hb
  obtain ⟨n, hn, hna, hnt⟩ := mem_iUnion.mp ha
  obtain ⟨m, hm, hmb, hmt⟩ := mem_iUnion.mp hb
  rcases lt_trichotomy n m with h | h | h
  · exact hnt m h (hm ▸ hmb)
  · subst m
    exact hab (hn.symm.trans hm)
  · exact hmt n h (hn ▸ hna)

variable [MeasurableSpace Γ] [MeasurableSingletonClass Γ]

/-- The infinite future no-return event is measurable.
@isnad1 id=measurab.1h4v.s6.dd14a87e1758 from=translated src=- shape=3d8530b4 vocab=4a9e9ef4
-/
theorem measurableSet_walkNoReturnEvent (s : Finset Γ) (A : Set Γ) (hA : MeasurableSet A) (a : Γ) :
    MeasurableSet (walkNoReturnEvent s A a) := by
  have he : walkNoReturnEvent s A a = ⋂ k : ℕ, {ω | 0 < k → walkPosition s a k ω ∉ A} := by
    ext ω
    simp [walkNoReturnEvent]
  rw [he]
  apply MeasurableSet.iInter
  intro k
  by_cases hk : 0 < k
  · simp only [hk, true_implies]
    exact hA.compl.preimage (measurable_walkPosition s a k)
  · simp only [hk, false_implies, ofPred_true, MeasurableSet.univ]

/-- The last-exit event is measurable at each time.
@isnad1 id=measurab.1h6v.s6.61426a590d3f from=translated src=- shape=2dd335a3 vocab=c315ea17
-/
theorem measurableSet_walkLastExitEvent (s : Finset Γ) (A : Set Γ) (hA : MeasurableSet A)
    (x a : Γ) (n : ℕ) : MeasurableSet (walkLastExitEvent s A x a n) := by
  by_cases ha : a ∈ A
  · rw [walkLastExitEvent_eq_inter s A x a ha n]
    exact (measurableSet_walkPosition s x a n).inter
      ((measurableSet_walkNoReturnEvent s A hA a).preimage (by fun_prop))
  · have he : walkLastExitEvent s A x a n = ∅ := by ext ω; simp [walkLastExitEvent, ha]
    rw [he]; exact MeasurableSet.empty

/-- Last exit at a at some finite time is measurable.
@isnad1 id=measurab.1h5v.s6.978bb50eaa44 from=translated src=- shape=79663be8 vocab=1be9bf43
-/
theorem measurableSet_walkLastExitEver (s : Finset Γ) (A : Set Γ) (hA : MeasurableSet A) (x a : Γ) :
    MeasurableSet (walkLastExitEver s A x a) :=
  MeasurableSet.iUnion (measurableSet_walkLastExitEvent s A hA x a)

/-- Exact factorization of a last-exit event into a transition probability and
an actual no-return probability under the same infinite walk law.
@isnad1 id=eq.4h7v.s8.7e22a9ab2346 from=translated src=- shape=579e51e7 vocab=6812160e
-/
theorem walkLastExitEvent_probability (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 ≤ μ g) (hmass : ∑ g ∈ s, μ g = 1)
    (A : Set Γ) (hA : MeasurableSet A) (x a : Γ) (ha : a ∈ A) (n : ℕ) :
    infiniteWalkLaw s μ hμ hmass (walkLastExitEvent s A x a n) =
      ENNReal.ofReal (transitionWeight s μ n x a) *
        infiniteWalkLaw s μ hμ hmass (walkNoReturnEvent s A a) := by
  rw [walkLastExitEvent_eq_inter s A x a ha n]
  have hh := (infiniteWalkLaw_position_tail_independent s μ hμ hmass x n).meas_inter
    ((measurableSet_singleton a).preimage (comap_measurable (walkPosition s x n)))
    ((measurableSet_walkNoReturnEvent s A hA a).preimage (comap_measurable (fun (ω : ℕ → s) (k : ℕ) => ω (k + n))))
  change infiniteWalkLaw s μ hμ hmass ({ω | walkPosition s x n ω = a} ∩
    (fun ω k => ω (k + n)) ⁻¹' walkNoReturnEvent s A a) = _ at hh
  rw [hh]
  change infiniteWalkLaw s μ hμ hmass {ω | walkPosition s x n ω = a} *
    infiniteWalkLaw s μ hμ hmass ((fun ω k => ω (k + n)) ⁻¹' walkNoReturnEvent s A a) = _
  rw [walkPosition_probability]
  rw [← Measure.map_apply (by fun_prop) (measurableSet_walkNoReturnEvent s A hA a),
    infiniteWalkLaw_shift]

variable [MeasurableMul Γ]

end Singularity
