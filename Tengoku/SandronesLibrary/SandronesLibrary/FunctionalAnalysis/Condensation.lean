/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.BanachSteinhaus
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Banach–Steinhaus (1927): condensation of singularities, Theorem I

A countable family of rows of continuous real-linear operators on a Banach space has a common
point of unbounded output whenever each row has its own such point. The common points form a
dense Gδ set. Infinite limsup is expressed by exceeding every threshold in every tail, so no
extended-real supremum conventions are hidden in the statement.

The proof follows the paper's category and linear-scaling mechanism, using dense open sets.
The final operator-norm version uses the library's existing uniform boundedness interface.
-/

namespace SandronesLibrary.FunctionalAnalysis

open Set
open SandronesLibrary.Topology.NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedLinearSpace ℝ E]

section SingleRow

variable {F : Type*} [NormedAddCommGroup F] [NormedLinearSpace ℝ F]

omit [NormedLinearSpace ℝ F] in
/-- Removing a finite prefix preserves unbounded output norms. This gives the textbook
quantifiers for `limsup ‖a q‖ = ∞` from ordinary unboundedness.

> **Entry**: functional-analysis.condensation
@isnad1 id=ex.1h4v.s5.d4f2a1d0b766 from=translated src=- shape=2915f5c4 vocab=69744159
-/
theorem unbounded_on_tail_of_unbounded {a : ℕ → F}
    (h : ∀ C : ℝ, ∃ q, C < ‖a q‖) (C : ℝ) (N : ℕ) :
    ∃ q, N ≤ q ∧ C < ‖a q‖ := by
  obtain ⟨q, hq⟩ := h (max C (∑ i ∈ Finset.range N, ‖a i‖))
  refine ⟨q, ?_, (le_max_left _ _).trans_lt hq⟩
  by_contra hn
  have hmem : q ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_of_not_ge hn)
  have hsum : ‖a q‖ ≤ ∑ i ∈ Finset.range N, ‖a i‖ :=
    Finset.single_le_sum (fun i _ => norm_nonneg (a i)) hmem
  exact (not_lt_of_ge (hsum.trans (le_max_right _ _))) hq

/-- The points where at least one operator exceeds a fixed threshold form an open set.
@isnad1 id=isopen.0h4v.s7.a81b04fd10bc from=translated src=- shape=12f22037 vocab=4e642980
-/
theorem isOpen_norm_exceeds_set (g : ℕ → E →L[ℝ] F) (C : ℝ) :
    IsOpen {x : E | ∃ q, C < ‖g q x‖} := by
  have heq : {x : E | ∃ q, C < ‖g q x‖} = ⋃ q, {x : E | C < ‖g q x‖} := by
    ext x
    simp
  rw [heq]
  exact isOpen_iUnion (fun q => isOpen_lt continuous_const (g q).continuous.norm)

/-- A row unbounded at one point exceeds each threshold somewhere in every nonempty open ball.
Completeness is unnecessary for this local step.
@isnad1 id=dense.1h4v.s8.b20ad2d843d1 from=translated src=- shape=f04379ca vocab=efc33321
-/
theorem dense_norm_exceeds_set_of_unbounded {g : ℕ → E →L[ℝ] F}
    (h : ∃ z : E, ∀ C : ℝ, ∃ q, C < ‖g q z‖) (C : ℝ) :
    Dense {x : E | ∃ q, C < ‖g q x‖} := by
  rw [Metric.dense_iff]
  intro x r hr
  by_contra hball
  have hbound : ∀ y ∈ Metric.ball x r, ∀ q, ‖g q y‖ ≤ C := by
    intro y hy q
    by_contra hq
    exact hball ⟨y, hy, q, lt_of_not_ge hq⟩
  obtain ⟨z, hz⟩ := h
  let t : ℝ := r / (‖z‖ + 1)
  have ht : 0 < t := div_pos hr (by positivity)
  have ht_eq : t * (‖z‖ + 1) = r := div_mul_cancel₀ _ (by positivity)
  have ht_norm : ‖t • z‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith
  have hnear : x + t • z ∈ Metric.ball x r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simpa using ht_norm
  have hcenter : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  obtain ⟨q, hq⟩ := hz (2 * C / t)
  have hlarge : 2 * C < t * ‖g q z‖ := by
    have hlarge' := (div_lt_iff₀ ht).mp hq
    simpa [mul_comm] using hlarge'
  have hdiff : ‖g q (t • z)‖ ≤ 2 * C := by
    calc
      ‖g q (t • z)‖ = ‖g q (x + t • z) - g q x‖ := by simp
      _ ≤ ‖g q (x + t • z)‖ + ‖g q x‖ := norm_sub_le _ _
      _ ≤ 2 * C := by linarith [hbound (x + t • z) hnear q, hbound x hcenter q]
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at hdiff
  exact (not_lt_of_ge hdiff) hlarge

end SingleRow

variable [BanachSpace E]
variable {F : ℕ → Type*} [∀ p, NormedAddCommGroup (F p)]
variable [∀ p, NormedLinearSpace ℝ (F p)]

/-- **Condensation of singularities**: the points at which every row is unbounded form a dense
Gδ set. This is the category conclusion in the proof of Theorem I of Banach–Steinhaus (1927).
@isnad1 id=and.1h3v.s9.f281d7610f64 from=translated src=- shape=f4e50f99 vocab=5ac3b249
-/
theorem condensation_dense_Gδ {g : ∀ p : ℕ, ℕ → E →L[ℝ] F p}
    (h : ∀ p, ∃ z : E, ∀ C : ℝ, ∃ q, C < ‖g p q z‖) :
    Dense {x : E | ∀ p, ∀ C : ℝ, ∃ q, C < ‖g p q x‖} ∧
      IsGδ {x : E | ∀ p, ∀ C : ℝ, ∃ q, C < ‖g p q x‖} := by
  let U : ℕ → ℕ → Set E := fun p m => {x | ∃ q, (m : ℝ) < ‖g p q x‖}
  have hEq : {x : E | ∀ p, ∀ C : ℝ, ∃ q, C < ‖g p q x‖} = ⋂ p, ⋂ m, U p m := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro hx p m
      exact hx p m
    · intro hx p C
      obtain ⟨m, hm⟩ := exists_nat_gt C
      obtain ⟨q, hq⟩ := hx p m
      exact ⟨q, hm.trans hq⟩
  have hOpen : ∀ p m, IsOpen (U p m) :=
    fun p m => isOpen_norm_exceeds_set (g p) m
  have hDense : ∀ p m, Dense (U p m) :=
    fun p m => dense_norm_exceeds_set_of_unbounded (h p) m
  have hGδ : ∀ p, IsGδ (⋂ m, U p m) :=
    fun p => IsGδ.iInter_of_isOpen (hOpen p)
  rw [hEq]
  exact ⟨dense_iInter_of_Gδ hGδ
    (fun p => banach_dense_iInter_of_isOpen (hOpen p) (hDense p)), IsGδ.iInter hGδ⟩

/-- **Theorem I, explicit infinite-limsup form**: a common point exceeds every threshold in
every tail of every row. The witness point is chosen before all three universal quantifiers.
@isnad1 id=ex.1h3v.s9.989d074280c3 from=translated src=- shape=e672f75c vocab=8cf2ebee
-/
theorem condensation_exists {g : ∀ p : ℕ, ℕ → E →L[ℝ] F p}
    (h : ∀ p, ∃ z : E, ∀ C : ℝ, ∃ q, C < ‖g p q z‖) :
    ∃ x : E, ∀ p, ∀ C : ℝ, ∀ N : ℕ, ∃ q, N ≤ q ∧ C < ‖g p q x‖ := by
  obtain ⟨x, hx⟩ := (condensation_dense_Gδ h).1.nonempty
  exact ⟨x, fun p C N => unbounded_on_tail_of_unbounded (hx p) C N⟩

/-- Unbounded operator norms in each row imply a common point of infinite output limsup.
The existing uniform boundedness principle supplies individual unbounded-output witnesses.
@isnad1 id=ex.1h3v.s8.fc4aa6da3b15 from=translated src=- shape=df02d6a3 vocab=8cf2ebee
-/
theorem condensation_of_unbounded_operatorNorm {g : ∀ p : ℕ, ℕ → E →L[ℝ] F p}
    (h : ∀ p, ∀ C : ℝ, ∃ q, C < ‖g p q‖) :
    ∃ x : E, ∀ p, ∀ C : ℝ, ∀ N : ℕ, ∃ q, N ≤ q ∧ C < ‖g p q x‖ := by
  apply condensation_exists
  intro p
  by_contra hpoint
  push Not at hpoint
  obtain ⟨C, _, hC⟩ := uniform_operatorNorm_bound_of_pointwise_bounded hpoint
  obtain ⟨q, hq⟩ := h p C
  exact (not_lt_of_ge (hC q)) hq

end SandronesLibrary.FunctionalAnalysis
