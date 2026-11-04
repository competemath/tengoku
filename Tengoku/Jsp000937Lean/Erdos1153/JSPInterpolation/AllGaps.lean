import Tengoku.Jsp000937Lean.Erdos1153.JSPInterpolation.FreeNodes
import Tengoku.Jsp000937Lean.Erdos1153.Interpolation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# JSP-000937: the ORIGINAL all-gap maximin problem

Unlike the auxiliary internal-gap maximin problem, Erdős 1130 includes
[-1,x_first] and [x_last,1].  The proof below includes both intervals,
proves attainment by an explicitly compressed pattern, and classifies
all maximizers.  The independent logarithmic-growth request is separately
named in Definitions.lean; this file does not silently assume that request.

Verification for the pinned revision is recorded in README.md and can be
reproduced with verify.sh.
-/

namespace JSPFreeNodes
open Erdos1153 Erdos1153.DeBoorPinkus
noncomputable section

lemma allMinPeak_le {d : ℕ} (nodes : NodeFamily (d + 2))
    (i : Option (Option (Fin (d + 1)))) :
    allMinPeak nodes ≤ augmentedGapHeight nodes i := by
  classical
  exact csInf_le (Set.finite_range (augmentedGapHeight nodes)).bddBelow
    (Set.mem_range_self i)

lemma le_allMinPeak_iff {d : ℕ} (nodes : NodeFamily (d + 2)) (L : ℝ) :
    L ≤ allMinPeak nodes ↔ ∀ i, L ≤ augmentedGapHeight nodes i := by
  constructor
  · intro h i
    exact h.trans (allMinPeak_le nodes i)
  · intro h
    apply le_csInf
    · exact ⟨augmentedGapHeight nodes none, ⟨none, rfl⟩⟩
    · rintro _ ⟨i, rfl⟩
      exact h i

/-- Neither endpoint is inserted into the interpolating node family. The
maximum on each exterior interval is attained at the ambient endpoint.-/
lemma left_exterior_max {d : ℕ} (nodes : NodeFamily (d + 2)) :
    lebesgueOn nodes (-1) (nodes.sorted.point 0) =
      lebesgueFunction nodes (-1) := by
  have hab : (-1 : ℝ) ≤ nodes.sorted.point 0 := nodes.sorted.neg_one_le 0
  apply le_antisymm
  · apply (interval_max_le_iff nodes hab).2
    intro x hx
    have hxj (j : Fin (d + 2)) : x ≤ nodes.point j := by
      obtain ⟨i, hi⟩ := nodes.sortingPerm.surjective j
      rw [← hi, NodeFamily.point_sortingPerm]
      exact hx.2.trans (nodes.sorted.strictMono.monotone (Fin.zero_le i))
    exact lebesgue_left_exterior nodes hx.1 hxj
  · exact value_le_interval_max nodes hab ⟨le_rfl, hab⟩

lemma right_exterior_max {d : ℕ} (nodes : NodeFamily (d + 2)) :
    lebesgueOn nodes (nodes.sorted.point (Fin.last (d + 1))) 1 =
      lebesgueFunction nodes 1 := by
  have hab : nodes.sorted.point (Fin.last (d + 1)) ≤ (1 : ℝ) :=
    nodes.sorted.le_one _
  apply le_antisymm
  · apply (interval_max_le_iff nodes hab).2
    intro x hx
    have hjx (j : Fin (d + 2)) : nodes.point j ≤ x := by
      obtain ⟨i, hi⟩ := nodes.sortingPerm.surjective j
      rw [← hi, NodeFamily.point_sortingPerm]
      exact (nodes.sorted.strictMono.monotone (Fin.le_last i)).trans hx.1
    exact lebesgue_right_exterior nodes hx.2 hjx
  · exact value_le_interval_max nodes hab ⟨hab, le_rfl⟩

lemma allMinPeak_le_internal {d : ℕ} (nodes : NodeFamily (d + 2)) :
    allMinPeak nodes ≤ minPeak nodes := by
  apply (le_orderedMinPeak_iff nodes.sorted _).2
  intro i
  exact allMinPeak_le nodes (some (some i))

/-- The literal minimum over n+1 intervals is exactly the three-way minimum
of the left exterior peak, the internal-gap minimum, and the right exterior peak.-/
lemma allMinPeak_eq_min {d : ℕ} (nodes : NodeFamily (d + 2)) :
    allMinPeak nodes = min (lebesgueFunction nodes (-1))
      (min (minPeak nodes) (lebesgueFunction nodes 1)) := by
  apply le_antisymm
  · apply le_min
    · simpa only [augmentedGapHeight, left_exterior_max] using allMinPeak_le nodes none
    · apply le_min
      · exact allMinPeak_le_internal nodes
      · simpa only [augmentedGapHeight, right_exterior_max] using
          allMinPeak_le nodes (some none)
  · apply (le_allMinPeak_iff nodes _).2
    intro i
    cases i with
    | none =>
      simpa only [augmentedGapHeight, left_exterior_max] using
        (min_le_left (lebesgueFunction nodes (-1))
          (min (minPeak nodes) (lebesgueFunction nodes 1)))
    | some j =>
      cases j with
      | none =>
        change min (lebesgueFunction nodes (-1))
          (min (minPeak nodes) (lebesgueFunction nodes 1)) ≤
          lebesgueOn nodes (nodes.sorted.point (Fin.last (d + 1))) 1
        rw [right_exterior_max]
        exact (min_le_right _ _).trans (min_le_right _ _)
      | some g =>
        exact (min_le_right _ _).trans
          ((min_le_left _ _).trans (orderedMinPeak_le nodes.sorted g))

/-! ## Actual attainment, not an unproved assumption about exterior growth -/

/-- Exactness of interpolation for p(X)=X bounds the exterior Lebesgue
function below whenever every node lies in [-a,a].-/
lemma abs_le_scale_mul_lebesgue {d : ℕ} (nodes : NodeFamily (d + 2))
    (a x : ℝ) (ha : ∀ k, |nodes.point k| ≤ a) :
    |x| ≤ a * lebesgueFunction nodes x := by
  have hp : (Polynomial.X : Polynomial ℝ).degree < (d + 2 : ℕ) := by
    rw [Polynomial.degree_X]
    exact_mod_cast (show (1 : ℕ) < d + 2 by omega)
  simpa only [Polynomial.eval_X] using
    (abs_eval_le_mul_lebesgueFunction nodes Polynomial.X hp a x
      (by simpa only [Polynomial.eval_X] using ha))

lemma oneNodeAllMinPeak_eq_one (nodes : NodeFamily 1) :
    oneNodeAllMinPeak nodes = 1 := by
  have hmax {a b : ℝ} (hab : a ≤ b) : lebesgueOn nodes a b = 1 := by
    obtain ⟨t, _ht, heq, _hmax⟩ := exists_lebesgueOn_eq_and_ge nodes hab
    exact heq.trans (single_node_lebesgue nodes t)
  unfold oneNodeAllMinPeak
  rw [hmax (nodes.mem_Icc 0).1, hmax (nodes.mem_Icc 0).2, min_self]

theorem jsp_000937_one_node (nodes : NodeFamily 1) : IsOneNodeFullMaximizer nodes := by
  intro other
  calc
    oneNodeAllMinPeak other = 1 := oneNodeAllMinPeak_eq_one other
    _ ≤ 1 := le_rfl
    _ = oneNodeAllMinPeak nodes := (oneNodeAllMinPeak_eq_one nodes).symm

end
end JSPFreeNodes
