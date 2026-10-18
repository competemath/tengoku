/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.M2.PointMaps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# M2: no equivariant maps to unordered pairs

`noPair`: let `Γ` be countable and doubly ergodic, acting on `ℙ¹(k)` through `a` with no
finite-index subgroup fixing a point. Then there are no measurable `u v : B → ℙ¹(k)` with
`u ≠ v` a.e. such that the unordered pair `{u, v}` is equivariant.

* If the pairs of two generic points meet, the weights `w(y) = ν{x : y ∈ {u x, v x}}` single out
  a finite set of points meeting every pair. Then B. H. Neumann's lemma produces a finite-index
  stabiliser.
* If they are generically disjoint, the invariant `wcr + wcr⁻¹` of two pairs is constant. Two
  generic reference pairs then confine `u` to a finite set, which contradicts disjointness.
-/

open MeasureTheory Filter Set
open scoped MatrixGroups ENNReal Pointwise

namespace OrbicurveCores.M2

variable {k : Type*} [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k]

/-- The unordered pair `{u x, v x}`. -/
def pairAt (u v : OnePoint ℝ → OnePoint k) (x : OnePoint ℝ) : Set (OnePoint k) := {u x, v x}

/-- The stabiliser of a point, as a subgroup of `Γ`. -/
def stab {Γ : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k} (hact : ActsOn Γ a)
    (y : OnePoint k) : Subgroup Γ where
  carrier := {g | a g • y = y}
  mul_mem' {g h} hg hh := by
    change a (g * h : SL(2, ℝ)) • y = y
    rw [hact _ g.2 _ h.2]
    rw [show a h • y = y from hh]; exact hg
  one_mem' := hact.one y
  inv_mem' {g} hg := by
    change a (g⁻¹ : SL(2, ℝ)) • y = y
    conv_lhs => rw [← show a g • y = y from hg]
    exact hact.inv g.2 y

section

variable {Γ : Subgroup SL(2, ℝ)} [Countable Γ] {a : SL(2, ℝ) → GL (Fin 2) k}
  {u v : OnePoint ℝ → OnePoint k}

lemma cauchy_ne_zero : cauchy ≠ 0 := fun h ↦
  bdry_ne_zero (Measure.measure_univ_eq_zero.1 (bdry_absolutelyContinuous_cauchy (by simp [h])))

omit [DecidableEq k] [ProperSpace k] in
lemma measurableSet_mem_pairAt (hu : Measurable u) (hv : Measurable v) (y : OnePoint k) :
    MeasurableSet {x | y ∈ pairAt u v x} := by
  have : {x | y ∈ pairAt u v x} = u ⁻¹' {y} ∪ v ⁻¹' {y} := by
    ext x; simp [pairAt, eq_comm]
  rw [this]
  exact (hu (measurableSet_singleton y)).union (hv (measurableSet_singleton y))

omit [DecidableEq k] [ProperSpace k] in
/-- At most two points meet any given pair: the weights sum to at most `2 ν(B)`. -/
lemma sum_weight_le (hu : Measurable u) (hv : Measurable v) (T : Finset (OnePoint k)) :
    ∑ y ∈ T, cauchy {x | y ∈ pairAt u v x} ≤ 2 * cauchy univ := by
  classical
  have e : ∀ y ∈ T, cauchy {x | y ∈ pairAt u v x} =
      ∫⁻ x, {x | y ∈ pairAt u v x}.indicator 1 x ∂cauchy := fun y _ ↦
    (lintegral_indicator_one (measurableSet_mem_pairAt hu hv y)).symm
  rw [Finset.sum_congr rfl e, ← lintegral_finsetSum' _ fun y _ ↦
    (measurable_one.indicator (measurableSet_mem_pairAt hu hv y)).aemeasurable]
  calc ∫⁻ x, ∑ y ∈ T, {x | y ∈ pairAt u v x}.indicator 1 x ∂cauchy
      ≤ ∫⁻ _, (2 : ℝ≥0∞) ∂cauchy := by
        refine lintegral_mono fun x ↦ ?_
        have : ∑ y ∈ T, {x | y ∈ pairAt u v x}.indicator (1 : OnePoint ℝ → ℝ≥0∞) x =
            ((T.filter fun y ↦ y ∈ pairAt u v x).card : ℝ≥0∞) := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          by_cases h : y ∈ pairAt u v x <;> simp [h]
        rw [this]
        have hc : (T.filter fun y ↦ y ∈ pairAt u v x).card ≤ 2 := by
          calc (T.filter fun y ↦ y ∈ pairAt u v x).card ≤ ({u x, v x} : Finset _).card := by
                refine Finset.card_le_card fun y hy ↦ ?_
                have := (Finset.mem_filter.1 hy).2
                simp only [pairAt, mem_insert_iff, mem_singleton_iff] at this
                simp [this]
            _ ≤ 2 := Finset.card_le_two
        exact (Nat.cast_le.2 hc).trans_eq (by norm_num)
    _ = 2 * cauchy univ := by rw [lintegral_const]

omit [ProperSpace k] [DecidableEq k] in
lemma eq_or_eq_inv_of_add_inv {w c : k} (hw : w ≠ 0) (hc : c ≠ 0) (h : w + w⁻¹ = c + c⁻¹) :
    w = c ∨ w = c⁻¹ := by
  have : (w - c) * (w - c⁻¹) = 0 := by
    have e : (w - c) * (w - c⁻¹) = w * (w + w⁻¹ - (c + c⁻¹)) := by field_simp; ring
    rw [e, h, sub_self, mul_zero]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact Or.inl (sub_eq_zero.1 h1)
  · exact Or.inr (sub_eq_zero.1 h1)

/-- The symmetric invariant of two pairs. -/
def jcr (y₁ y₂ y₃ y₄ : OnePoint k) : k := wcr y₁ y₂ y₃ y₄ + (wcr y₁ y₂ y₃ y₄)⁻¹

omit [ProperSpace k] [DecidableEq k] in
lemma jcr_swap₁₂ {y₁ y₂ y₃ y₄ : OnePoint k} (h : Distinct4 y₁ y₂ y₃ y₄) :
    jcr y₂ y₁ y₃ y₄ = jcr y₁ y₂ y₃ y₄ := by
  simp only [jcr, wcr_swap₁₂ h, inv_inv]; ring

omit [ProperSpace k] [DecidableEq k] in
lemma jcr_swap₃₄ {y₁ y₂ y₃ y₄ : OnePoint k} (h : Distinct4 y₁ y₂ y₃ y₄) :
    jcr y₁ y₂ y₄ y₃ = jcr y₁ y₂ y₃ y₄ := by
  simp only [jcr, wcr_swap₃₄ h, inv_inv]; ring

omit [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k] in
lemma Distinct4.swap₁₂ {y₁ y₂ y₃ y₄ : OnePoint k} (h : Distinct4 y₁ y₂ y₃ y₄) :
    Distinct4 y₂ y₁ y₃ y₄ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h; exact ⟨h1.symm, h4, h5, h2, h3, h6⟩

omit [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k] in
lemma distinct4_of_disjoint {u₁ v₁ u₂ v₂ : OnePoint k} (h₁ : u₁ ≠ v₁) (h₂ : u₂ ≠ v₂)
    (hd : Disjoint ({u₁, v₁} : Set (OnePoint k)) {u₂, v₂}) : Distinct4 u₁ v₁ u₂ v₂ := by
  simp only [Set.disjoint_insert_left, Set.disjoint_insert_right, Set.disjoint_singleton_left,
    Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hd
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := hd
  exact ⟨h₁, Ne.symm a, c, Ne.symm b, d, h₂⟩

variable [MeasurableSpace k] [BorelSpace k]

end

end OrbicurveCores.M2
