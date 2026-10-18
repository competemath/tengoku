import Tengoku.Seed.Topology.Algebra.Module.FiniteDimension
import Tengoku.Seed.Analysis.Normed.Affine.Isometry
import Tengoku.Seed.Analysis.Convex.PartitionOfUnity
import Tengoku.Seed.Analysis.Convex.Caratheodory

import Tengoku.FixedPointTheoremsLean4.FixedPointTheorems.brouwer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-
Kakutani Fixed-Point theorem:
Let s be a nonempty, compact, convex of a finite-dimensional space.
Let f be a set-valued map on s with closed graph,
and each f(x) be nonempty, compact, convex, and a subset of s.
Then there is a point x with x ∈ f(x).

Main result is `kakutani_fixed_point` below.
Proof relies on the Brouwer fixed-point theorem.

https://en.wikipedia.org/wiki/Kakutani_fixed-point_theorem
-/

open Classical
open Filter

/- defining the closed graph property of a set-valued map -/
def closedGraph {X Y} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Set Y) : Prop :=
    IsClosed { z : X × Y | z.2 ∈ f z.1}

/- defining that x is a convex combinations of points y_i with weights a_i -/
def convex_comb {V : Type*} {k: ℕ} [AddCommGroup V] [Module ℝ V]
  (x : V) (a : Fin k → ℝ) (y: Fin k → V) : Prop :=
  (∀ i, 0 ≤ a i) ∧ ∑ i, a i = 1 ∧ x = ∑ i, a i • y i

lemma mem_of_convex_comb {V : Type*} {k: ℕ} [AddCommGroup V] [Module ℝ V]
  (x : V) {a : Fin k → ℝ} {y: Fin k → V} (h0 : convex_comb x a y)
  s (h1 : Convex ℝ s) (h2 : ∀ i, y i ∈ s): x ∈ s := by {
  unfold convex_comb at h0
  rw [h0.2.2]
  apply Convex.sum_mem h1 (fun i _ ↦ h0.1 i) h0.2.1 fun i a ↦ h2 i
}

lemma sub_ICC_of_convex_comb {V : Type*} {k: ℕ} [AddCommGroup V] [Module ℝ V]
    (x : V) {a : Fin k → ℝ} {y: Fin k → V} (h0 : convex_comb x a y)
    : a ∈ Set.Icc 0 1 := by {
  simp only [Set.mem_Icc]
  apply And.intro h0.1
  have h2 := h0.1
  have h1 := h0.2.1
  intro i
  simp only [Pi.one_apply]
  rw [←h1]
  apply Finset.single_le_sum (fun i a ↦ h2 i)
  simp only [Finset.mem_univ]
}

/- useful to get a fixed size of vectors -/
lemma caratheodory_1 {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (s : Set V) k (h1 : k = Module.finrank ℝ V) {x} (h2 : x ∈ convexHull ℝ s)
    : ∃ (z : Fin (k+1)→ V), ∃ a, Set.range z ⊆ s ∧ convex_comb x a z := by {
  obtain ⟨I ,hI,z1,α, h3⟩  := eq_pos_convex_span_of_mem_convexHull h2
  have h4 : hI.card ≤ k + 1 := by {
    apply le_trans $ AffineIndependent.card_le_finrank_succ h3.2.1
    rw [h1,add_le_add_iff_right]
    exact Submodule.finrank_le (vectorSpan ℝ (Set.range z1))
  }
  let g1 := hI.equivFin
  let g2 : Fin (hI.card) → Fin (k+1) := fun i ↦ Fin.ofNat _ i.1
  let g3 := g2 ∘ g1
  have hg3 : Function.Injective g3 := by {
    unfold g3
    refine (Equiv.injective_comp g1 g2).mpr ?_
    intro i1 i2 h5
    unfold g2 at h5
    simp only [Fin.ofNat_eq_cast] at h5
    rw [←Fin.val_eq_val] at h5 ⊢
    rwa [Fin.val_cast_of_lt, Fin.val_cast_of_lt] at h5 <;> omega
  }
  have hsne : s.Nonempty := convexHull_nonempty_iff.mp (Set.nonempty_of_mem h2)
  obtain ⟨sdef, hsdef⟩ := hsne
  let β := Function.extend g3 α (fun _ ↦ 0)
  let z2 := Function.extend g3 z1 (fun _ ↦ sdef)
  have h5 : Set.range z2 ⊆ s := by {
    intro y hy
    obtain ⟨i1, hi1⟩ := hy
    rw [← hi1]
    unfold z2
    by_cases h5 : ∃ i2, g3 i2 = i1
    {
      apply h3.1
      obtain ⟨i2, hi2⟩ := h5
      use i2
      rw [←hi2,Function.Injective.extend_apply hg3]
    }
    rwa [Function.extend_apply' _ _ _ h5]
  }
  use z2, β
  have h6 : ∑ i, β i = 1 := by {
    rw [←h3.2.2.2.1]
    symm
    apply Fintype.sum_of_injective g3 hg3
    exact fun i a ↦ Function.extend_apply' α (fun x ↦ 0) i a
    exact fun i ↦ Eq.symm (Function.Injective.extend_apply hg3 α (fun x ↦ 0) i)
  }
  have h7 : x = ∑ i, β i • z2 i := by {
    rw [←h3.2.2.2.2]
    apply Fintype.sum_of_injective g3 hg3
    intro i h7
    simp only [smul_eq_zero]
    exact Or.inl $ Function.extend_apply' α (fun x ↦ 0) i h7
    intro i
    unfold β z2
    rw [Function.Injective.extend_apply hg3,Function.Injective.extend_apply hg3]
  }
  have h9 i : 0 ≤ β i := by {
    unfold β
    have h12 : 0 ≤ α := fun i ↦ le_of_lt (h3.2.2.1 i)
    apply Function.extend_nonneg h12
    rfl
  }
  apply And.intro h5
  apply And.intro h9 (And.intro h6 h7)
}
