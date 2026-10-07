/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Weighted

/-!
# Collision budgets for biased Boolean features

An average collision bound replaces the maximum-fibre hypothesis in weighted
counting. Dividing each pulled-back message weight by its fibre size normalizes
the mass; two logarithmic mean inequalities then charge biased coordinates.
No independence assumption is made on the features.

The differential-uniformity collision estimate used by applications is classical:
Kölsch, Kriepke, and Kyureghyan, "Image sets of perfectly nonlinear maps" (2022),
Lemma 2 and Corollary 1, https://doi.org/10.1007/s10623-022-01094-4.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped BigOperators Classical

/-- The number of ordered pairs of inputs with equal keys, including the diagonal. -/
noncomputable def collisionCount {X T : Type*} [Fintype X] (key : X → T) : ℕ :=
  ∑ x, (Finset.univ.filter fun y => key y = key x).card

/-- Refining equality of keys cannot increase their number of collisions. -/
theorem collisionCount_le_of_refines {X T U : Type*} [Fintype X]
    (key : X → T) (coarse : X → U)
    (refines : ∀ x y, key x = key y → coarse x = coarse y) :
    collisionCount key ≤ collisionCount coarse := by
  apply Finset.sum_le_sum
  intro x _
  apply Finset.card_le_card
  intro y hy
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, refines y x (Finset.mem_filter.mp hy).2⟩

/-- Reindex ordered collisions by their input displacement. -/
theorem collisionCount_eq_sum_differences {X T : Type*} [Fintype X] [AddGroup X]
    (key : X → T) :
    collisionCount key =
      ∑ d, (Finset.univ.filter fun x => key (x + d) = key x).card := by
  unfold collisionCount
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    (∑ x, ∑ y, if key y = key x then 1 else 0) =
        ∑ x, ∑ d, if key (x + d) = key x then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Equiv.sum_comp (Equiv.addLeft x) (fun y => if key y = key x then 1 else 0)).symm
    _ = _ := Finset.sum_comm

/-- A bound on every nonzero difference gives the classical ordered-collision budget. -/
theorem collisionCount_le_of_differences {X T : Type*} [Fintype X] [AddGroup X]
    (key : X → T) {δ : ℕ}
    (differences : ∀ d : X, d ≠ 0 →
      (Finset.univ.filter fun x => key (x + d) = key x).card ≤ δ) :
    collisionCount key ≤ Fintype.card X + δ * (Fintype.card X - 1) := by
  rw [collisionCount_eq_sum_differences]
  calc
    (∑ d, (Finset.univ.filter fun x => key (x + d) = key x).card) ≤
        ∑ d : X, if d = 0 then Fintype.card X else δ := by
      apply Finset.sum_le_sum
      intro d _
      by_cases hd : d = 0
      · simp [hd]
      · simpa only [hd, ↓reduceIte] using differences d hd
    _ = Fintype.card X + δ * (Fintype.card X - 1) := by
      rw [Finset.sum_ite]
      simp [Finset.filter_ne', mul_comm]
      have eq : (Finset.univ.filter fun x : X => x = 0) = {0} := by
        ext x
        simp
      rw [eq, Finset.card_singleton]

/-- Dividing pulled-back weights by their fibre sizes leaves mass at most one. -/
theorem sum_weight_div_fibre_le {X T : Type*} [Fintype X] [Fintype T]
    (key : X → T) (weight : T → ℝ) (nonneg : ∀ t, 0 ≤ weight t)
    (mass : ∑ t, weight t = 1) :
    (∑ x, weight (key x) / (Finset.univ.filter fun y => key y = key x).card) ≤ 1 := by
  classical
  rw [← mass, ← Finset.sum_fiberwise Finset.univ key]
  apply Finset.sum_le_sum
  intro t _
  have same : (∑ x ∈ Finset.univ.filter (fun x => key x = t),
      weight (key x) / (Finset.univ.filter fun y => key y = key x).card) =
      ∑ _x ∈ Finset.univ.filter (fun x => key x = t),
        weight t / (Finset.univ.filter fun y => key y = t).card := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [same]
  simp only [Finset.sum_const, nsmul_eq_mul]
  by_cases zero : (Finset.univ.filter fun y => key y = t).card = 0
  · simp only [zero, Nat.cast_zero, zero_mul]
    exact nonneg t
  · have nz : ((Finset.univ.filter fun y => key y = t).card : ℝ) ≠ 0 := by
      exact_mod_cast zero
    rw [mul_div_cancel₀ _ nz]

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
