import Tengoku.Seed.Analysis.Normed.Group.Bounded
import Tengoku.Seed.Analysis.Normed.Module.Basic
import Tengoku.Seed.Topology.Connected.LocallyConnected
import Tengoku.Seed.Topology.Order.IntermediateValue
import Tengoku.Seed.Topology.MetricSpace.Thickening
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Filling the bounded complementary components of a compact set

The fill of a compact plane contour is its trace together with its bounded
complementary components. For a Jordan curve this is the usual closed
interior. Compactness of this set does not require Jordan separation:
complement components are open, while an outward ray from any point beyond
a ball containing the trace proves that point lies in an unbounded component.
-/

noncomputable section
open Bornology Metric Topology
namespace Set

section Topology
variable {X : Type*} [TopologicalSpace X] [Bornology X]

/-- Fill a set by adjoining its bounded complementary components. For a
Jordan curve in the plane, this is its trace together with its interior.-/
def boundedComplementFill (s : Set X) : Set X :=
  s ∪ {x | x ∉ s ∧ IsBounded (connectedComponentIn sᶜ x)}

/-- The original set is contained in its bounded-complement fill.
@isnad1 id=le.0h2v.s4.2a0953705d8f from=translated src=- shape=530d50d6 vocab=26fc3027
-/
theorem subset_boundedComplementFill (s : Set X) : s ⊆ boundedComplementFill s :=
  subset_union_left

/-- A point outside the fill lies in an unbounded complementary component.
@isnad1 id=iff.0h3v.s5.2b82eb026db1 from=translated src=- shape=4b489186 vocab=dccf698b
-/
theorem not_mem_boundedComplementFill_iff {s : Set X} {x : X} :
    x ∉ boundedComplementFill s ↔ x ∉ s ∧ ¬ IsBounded (connectedComponentIn sᶜ x) := by
  by_cases hx : x ∈ s <;> simp [boundedComplementFill, hx]

/-- A complementary component through a point outside the fill stays outside
the fill, since all of its points determine the same component.
@isnad1 id=le.1h3v.s5.53b15df35776 from=translated src=- shape=429c3b56 vocab=36aeab65
-/
theorem connectedComponentIn_subset_compl_boundedComplementFill {s : Set X} {x : X}
    (hx : x ∉ boundedComplementFill s) :
    connectedComponentIn sᶜ x ⊆ (boundedComplementFill s)ᶜ := by
  obtain ⟨_, hx⟩ := not_mem_boundedComplementFill_iff.mp hx
  intro y hy
  refine not_mem_boundedComplementFill_iff.mpr ⟨connectedComponentIn_subset sᶜ x hy, ?_⟩
  rw [← connectedComponentIn_eq hy]
  exact hx

/-- Filling bounded components preserves closedness in a locally connected
space. Each complementary component left over is open.
@isnad1 id=isclosed.1h2v.s4.12cb908036dc from=translated src=- shape=a3830b65 vocab=44c13011
-/
theorem isClosed_boundedComplementFill [LocallyConnectedSpace X] {s : Set X}
    (hs : IsClosed s) : IsClosed (boundedComplementFill s) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  have hx' := (not_mem_boundedComplementFill_iff.mp hx).1
  exact Filter.mem_of_superset
    (hs.isOpen_compl.connectedComponentIn.mem_nhds (mem_connectedComponentIn hx'))
    (connectedComponentIn_subset_compl_boundedComplementFill hx)

end Topology

section NormedSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point beyond a ball containing a set belongs to an unbounded component
of its complement: the entire outward ray lies in that same component.
@isnad1 id=not.3h4v.s6.4cdd25200d5c from=translated src=- shape=048324a3 vocab=8180c998
-/
theorem not_isBounded_connectedComponentIn_compl_of_norm_lt
    {s : Set E} {R : ℝ} (hR : 0 ≤ R) (hs : s ⊆ closedBall 0 R)
    {x : E} (hx : R < ‖x‖) : ¬ IsBounded (connectedComponentIn sᶜ x) := by
  have hxpos : 0 < ‖x‖ := hR.trans_lt hx
  let ray : Set E := (fun t : ℝ => t • x) '' Ici 1
  have hray : IsPreconnected ray :=
    isPreconnected_Ici.image _ (by fun_prop)
  have hxray : x ∈ ray := ⟨1, by simp, one_smul ℝ x⟩
  have hrays : ray ⊆ sᶜ := by
    rintro z ⟨t, ht, rfl⟩ hz
    change 1 ≤ t at ht
    have hb := hs hz
    rw [mem_closedBall_zero_iff] at hb
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans ht)] at hb
    nlinarith
  have hraycomp : ray ⊆ connectedComponentIn sᶜ x :=
    hray.subset_connectedComponentIn hxray hrays
  intro hcomp
  obtain ⟨M, hM⟩ := (hcomp.subset hraycomp).exists_norm_le
  let t : ℝ := (max M ‖x‖ + 1) / ‖x‖
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ hxpos).mpr
    linarith [le_max_right M ‖x‖]
  have hn : ‖t • x‖ = max M ‖x‖ + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans ht)]
    exact div_mul_cancel₀ _ hxpos.ne'
  have hb := hM (t • x) ⟨t, ht, rfl⟩
  rw [hn] at hb
  linarith [le_max_left M ‖x‖]

/-- Filling bounded complementary components does not enlarge a containing
closed ball. This applies in every real normed space.
@isnad1 id=le.2h3v.s6.0aa79b81110e from=translated src=- shape=9d97ace2 vocab=8f3b6f3f
-/
theorem boundedComplementFill_subset_closedBall {s : Set E} {R : ℝ}
    (hR : 0 ≤ R) (hs : s ⊆ closedBall 0 R) :
    boundedComplementFill s ⊆ closedBall 0 R := by
  intro x hx
  by_contra hnot
  have hn : R < ‖x‖ := by simpa only [mem_closedBall_zero_iff, not_le] using hnot
  rcases hx with hx | ⟨_, hcomp⟩
  · exact hnot (hs hx)
  · exact not_isBounded_connectedComponentIn_compl_of_norm_lt hR hs hn hcomp

/-- Filling the bounded complementary components of a bounded set is bounded.
@isnad1 id=isbounde.1h2v.s5.43fbe6cbe189 from=translated src=- shape=b1207aaf vocab=f4d7f227
-/
theorem isBounded_boundedComplementFill {s : Set E} (hs : IsBounded s) :
    IsBounded (boundedComplementFill s) := by
  obtain ⟨R, hR, hb⟩ := hs.exists_pos_norm_le
  exact isBounded_closedBall.subset
    (boundedComplementFill_subset_closedBall hR.le
      (fun x hx => mem_closedBall_zero_iff.mpr (hb x hx)))

/-- The fill of a compact set in a locally connected proper real normed space
is compact. In particular, every compact planar contour has compact fill.
@isnad1 id=iscompac.1h2v.s6.adf435078ae5 from=translated src=- shape=55c5bfd4 vocab=7ab3ae56
-/
theorem isCompact_boundedComplementFill [LocallyConnectedSpace E] [ProperSpace E]
    {s : Set E} (hs : IsCompact s) : IsCompact (boundedComplementFill s) :=
  isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_boundedComplementFill hs.isClosed, isBounded_boundedComplementFill hs.isBounded⟩

/-- A holomorphy neighborhood of the compact filled trace contains an actual
positive closed metric buffer around it.
@isnad1 id=ex.3h3v.s7.91e8ba76abc1 from=translated src=- shape=393d9d25 vocab=e1c756a5
-/
theorem exists_cthickening_boundedComplementFill_subset_open
    [LocallyConnectedSpace E] [ProperSpace E] {s U : Set E}
    (hs : IsCompact s) (hU : IsOpen U) (hsub : boundedComplementFill s ⊆ U) :
    ∃ δ, 0 < δ ∧ cthickening δ (boundedComplementFill s) ⊆ U :=
  (isCompact_boundedComplementFill hs).exists_cthickening_subset_open hU hsub

end NormedSpace
end Set
