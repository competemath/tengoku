import Tengoku.TdaLib.TDA.Persistence.BoundaryCost

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An attained finite first-order matching cost

Finite occurrence labels preserve repeated pair values. The admissible family is
the existing partial-injection type with empty essential parts, and its cost is
the existing real sum of maximum-norm pair costs and diagonal charges. The real
infimum is attained because that family is finite and contains the all-unmatched
matching. Relabelling preserves both the candidate sums and the minimum.

The algebra below also applies to arbitrary real pairs. For persistence diagrams,
each pair satisfies birth < death. `FiniteMatchingCostLaws` supplies the distance
laws. Equality with an optimization over measure couplings is not asserted here.
-/

namespace TDA.Persistence

namespace OccurrenceMatching

variable {I J I' J' : Type*} [Fintype I] [Fintype J] [Fintype I'] [Fintype J']

/-- Relabelling preserves the paired sum and both unmatched diagonal sums.
@isnad1 id=eq.0h9v.s6.fb88bab1ebda from=translated src=- shape=633d3f0f vocab=4ec2ad16
-/
theorem totalFiniteCost_relabel (u : I' ≃ I) (v : J' ≃ J)
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1})
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    (M.relabel u v (Equiv.refl _) (Equiv.refl _)).totalFiniteCost (x ∘ u) (y ∘ v) =
      M.totalFiniteCost x y :=
  totalBoundaryCost_relabel u v M
    (fun i j => (finitePairCost (x i) (y j)).toReal)
    (fun i => (diagonalCost (x i)).toReal) (fun j => (diagonalCost (y j)).toReal)

end OccurrenceMatching

variable {I J : Type*} [Fintype I] [Fintype J]

/-- First-order finite PD matching cost in the birth–death maximum norm.
Essential occurrences are absent. The infimum is an attained finite minimum.-/
noncomputable def finiteFirstOrderMatchingCost (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : ℝ :=
  ⨅ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}, M.totalFiniteCost x y

/-- The existing nonempty finite matching family supplies a minimizer,
including when either occurrence type is empty.
@isnad1 id=ex.0h4v.s5.e2d95e00b849 from=translated src=- shape=02222a3f vocab=d2ec8f3d
-/
theorem exists_minimizing_occurrenceMatching (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    ∃ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1},
      M.totalFiniteCost x y = finiteFirstOrderMatchingCost x y := by
  let : Nonempty (OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :=
    occurrenceMatching_nonempty_iff.mpr (by simp)
  exact exists_eq_ciInf_of_finite

/-- Every candidate partial matching gives an upper bound on the minimum.
@isnad1 id=le.0h5v.s5.978341eb9536 from=translated src=- shape=499c6df1 vocab=aaeea7ef
-/
theorem finiteFirstOrderMatchingCost_le_totalFiniteCost
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ)
    (M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}) :
    finiteFirstOrderMatchingCost x y ≤ M.totalFiniteCost x y := by
  apply ciInf_le
  refine ⟨0, ?_⟩
  rintro _ ⟨N, rfl⟩
  exact N.totalFiniteCost_nonneg x y

/-- A lower bound holds for the minimum exactly when it holds for every matching.
@isnad1 id=iff.0h5v.s5.4fb9b7369ed0 from=translated src=- shape=80f4fba0 vocab=aaeea7ef
-/
theorem le_finiteFirstOrderMatchingCost_iff (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) (c : ℝ) :
    c ≤ finiteFirstOrderMatchingCost x y ↔
      ∀ M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1}, c ≤ M.totalFiniteCost x y := by
  constructor
  · intro h M
    exact h.trans (finiteFirstOrderMatchingCost_le_totalFiniteCost x y M)
  · intro h
    obtain ⟨M, hM⟩ := exists_minimizing_occurrenceMatching x y
    exact hM ▸ h M

/--
@isnad1 id=le.0h4v.s5.dc28a08fec7d from=translated src=- shape=785132df vocab=1a00afd7
-/
theorem finiteFirstOrderMatchingCost_nonneg (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    0 ≤ finiteFirstOrderMatchingCost x y :=
  (le_finiteFirstOrderMatchingCost_iff x y 0).mpr (fun M => M.totalFiniteCost_nonneg x y)

/-- Deleting every source and target occurrence is always feasible.
@isnad1 id=le.0h4v.s6.e38f419f5d52 from=translated src=- shape=c0d02f92 vocab=a642716d
-/
theorem finiteFirstOrderMatchingCost_le_diagonalSum (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finiteFirstOrderMatchingCost x y ≤
      (∑ i, (diagonalCost (x i)).toReal) + ∑ j, (diagonalCost (y j)).toReal := by
  classical
  let M : OccurrenceMatching I J PEmpty.{1} PEmpty.{1} :=
    ⟨fun _ => none, by simp, Equiv.refl _⟩
  calc
    _ ≤ M.totalFiniteCost x y := finiteFirstOrderMatchingCost_le_totalFiniteCost x y M
    _ = _ := by simp [M, OccurrenceMatching.totalFiniteCost]

/--
@isnad1 id=eq.0h4v.s5.6d6c795efe1f from=translated src=- shape=2b7a3f08 vocab=02b307a3
-/
theorem finiteFirstOrderMatchingCost_of_isEmpty_right [IsEmpty J]
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finiteFirstOrderMatchingCost x y = ∑ i, (diagonalCost (x i)).toReal := by
  classical
  obtain ⟨M, hM⟩ := exists_minimizing_occurrenceMatching x y
  have hn (i : I) : M.finite i = none := by
    cases h : M.finite i with
    | none => rfl
    | some j => exact isEmptyElim j
  rw [← hM]
  simp [OccurrenceMatching.totalFiniteCost, hn]

/--
@isnad1 id=eq.0h4v.s5.a1464d38e82c from=translated src=- shape=5113c342 vocab=02b307a3
-/
theorem finiteFirstOrderMatchingCost_of_isEmpty_left [IsEmpty I]
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finiteFirstOrderMatchingCost x y = ∑ j, (diagonalCost (y j)).toReal := by
  classical
  obtain ⟨M, hM⟩ := exists_minimizing_occurrenceMatching x y
  rw [← hM]
  simp [OccurrenceMatching.totalFiniteCost]

/--
@isnad1 id=eq.0h4v.s5.0d1f977b23ce from=translated src=- shape=21309ef5 vocab=0d441989
-/
@[simp] theorem finiteFirstOrderMatchingCost_empty [IsEmpty I] [IsEmpty J]
    (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) : finiteFirstOrderMatchingCost x y = 0 := by
  rw [finiteFirstOrderMatchingCost_of_isEmpty_right]
  exact Fintype.sum_empty _

/-- Arbitrary finite occurrence equivalences preserve the minimum, including multiplicity.
@isnad1 id=eq.0h8v.s6.5268cf356720 from=translated src=- shape=9e2d99af vocab=180b066b
-/
theorem finiteFirstOrderMatchingCost_reindex {I' J' : Type*} [Fintype I'] [Fintype J']
    (u : I' ≃ I) (v : J' ≃ J) (x : I → ℝ × ℝ) (y : J → ℝ × ℝ) :
    finiteFirstOrderMatchingCost (x ∘ u) (y ∘ v) = finiteFirstOrderMatchingCost x y := by
  apply le_antisymm
  · obtain ⟨M, hM⟩ := exists_minimizing_occurrenceMatching x y
    calc
      _ ≤ (M.relabel u v (Equiv.refl _) (Equiv.refl _)).totalFiniteCost (x ∘ u) (y ∘ v) :=
        finiteFirstOrderMatchingCost_le_totalFiniteCost _ _ _
      _ = _ := by rw [M.totalFiniteCost_relabel, hM]
  · obtain ⟨N, hN⟩ := exists_minimizing_occurrenceMatching (x ∘ u) (y ∘ v)
    obtain ⟨M, hM⟩ :=
      (OccurrenceMatching.relabelEquiv u v (Equiv.refl PEmpty.{1})
        (Equiv.refl PEmpty.{1})).surjective N
    have hcost := M.totalFiniteCost_relabel u v x y
    change M.relabel u v (Equiv.refl _) (Equiv.refl _) = N at hM
    rw [hM] at hcost
    calc
      _ ≤ M.totalFiniteCost x y := finiteFirstOrderMatchingCost_le_totalFiniteCost x y M
      _ = _ := hcost.symm.trans hN

end TDA.Persistence
