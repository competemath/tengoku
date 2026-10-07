/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.InfoMeasures
import Tengoku

/-!
# Product-law helpers for the finite Shannon semantic bridge

This file contains the first reusable infrastructure for semantic bridge
theorems. The core finite information-measure API is PMF-first; this file adds
the independent product law and its basic relationship with product measures.

The helper is named `Shannon.indepProd`, not `PMF.prod`, so that it remains a
project-local bridge construction and will not conflict with a future canonical
mathlib product-PMF API.
-/

namespace LeanInfoTheory
namespace Shannon

open MeasureTheory
open scoped ENNReal

noncomputable section

universe u v

/--
Independent product of two probability mass functions.

Mathematically, this is the law of `(X, Y)` when `X` has law `p`, `Y` has law
`q`, and the two variables are independent.
-/
def indepProd {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (q : PMF beta) : PMF (alpha × beta) :=
  p.bind fun a => q.map fun b => (a, b)

open Classical in
private theorem map_prod_mk_apply {alpha : Type u} {beta : Type v}
    (q : PMF beta) (a a' : alpha) (b : beta) :
    (q.map fun b' => (a', b')) (a, b) = if a = a' then q b else 0 := by
  rw [PMF.map_apply]
  by_cases h : a = a'
  · subst h
    rw [ite_eq_left rfl]
    exact (tsum_eq_single b (by
      intro b' hb'
      simp [Ne.symm hb'])).trans (by simp)
  · rw [ite_eq_right h]
    exact ENNReal.tsum_eq_zero.2 (by
      intro b'
      simp [h])

/--
The atom mass of an independent product is the product of the two atom masses.
-/
@[simp]
theorem indepProd_apply {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (q : PMF beta) (a : alpha) (b : beta) :
    indepProd p q (a, b) = p a * q b := by
  rw [indepProd, PMF.bind_apply]
  simp_rw [map_prod_mk_apply]
  exact (tsum_eq_single a (by
    intro a' ha'
    rw [ite_eq_right (Ne.symm ha')]
    simp)).trans (by simp)

/--
An atom of the independent product has zero mass exactly when one of the two
coordinate atoms has zero mass.
-/
@[simp]
theorem indepProd_apply_eq_zero_iff {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (q : PMF beta) (a : alpha) (b : beta) :
    indepProd p q (a, b) = 0 ↔ p a = 0 ∨ q b = 0 := by
  rw [indepProd_apply, mul_eq_zero]

/--
An atom belongs to the independent product support exactly when both coordinate
atoms belong to the corresponding supports.
-/
@[simp]
theorem indepProd_apply_ne_zero_iff {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (q : PMF beta) (a : alpha) (b : beta) :
    indepProd p q (a, b) ≠ 0 ↔ p a ≠ 0 ∧ q b ≠ 0 := by
  rw [ne_eq, indepProd_apply_eq_zero_iff, not_or]

/-- The support of an independent product is the product of the two supports. -/
@[simp]
theorem support_indepProd {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (q : PMF beta) :
    (indepProd p q).support = Set.prod p.support q.support := by
  ext x
  rcases x with ⟨a, b⟩
  simp [PMF.mem_support_iff, Set.prod]

/-- The first marginal of an independent product is the first factor law. -/
@[simp]
theorem fstMarginal_indepProd {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (q : PMF beta) :
    fstMarginal (indepProd p q) = p := by
  unfold fstMarginal indepProd
  rw [PMF.map_bind]
  have hinner :
      (fun a : alpha => (q.map fun b : beta => (a, b)).map Prod.fst) =
        fun a : alpha => PMF.pure a := by
    funext a
    rw [PMF.map_comp]
    change q.map (Function.const beta a) = PMF.pure a
    exact PMF.map_const q a
  rw [hinner]
  exact PMF.bind_pure p

/-- The second marginal of an independent product is the second factor law. -/
@[simp]
theorem sndMarginal_indepProd {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (q : PMF beta) :
    sndMarginal (indepProd p q) = q := by
  unfold sndMarginal indepProd
  rw [PMF.map_bind]
  have hinner :
      (fun a : alpha => (q.map fun b : beta => (a, b)).map Prod.snd) =
        fun _a : alpha => q := by
    funext a
    rw [PMF.map_comp]
    change q.map id = q
    exact PMF.map_id q
  rw [hinner]
  exact PMF.bind_const p q

/--
Swapping the coordinates of an independent product swaps the two factor laws.
-/
theorem indepProd_map_swap {alpha : Type u} {beta : Type v}
    (p : PMF alpha) (q : PMF beta) :
    (indepProd p q).map Prod.swap = indepProd q p := by
  unfold indepProd
  rw [PMF.map_bind]
  have hinner :
      (fun a : alpha => (q.map fun b : beta => (a, b)).map Prod.swap) =
        fun a : alpha => q.map fun b : beta => (b, a) := by
    funext a
    rw [PMF.map_comp]
    rfl
  rw [hinner]
  change p.bind (fun a => q.bind fun b => PMF.pure (b, a)) =
    q.bind (fun b => p.bind fun a => PMF.pure (b, a))
  exact PMF.bind_comm p q fun a b => PMF.pure (b, a)

/--
The independent product law assigns product rectangles the product of the
factor probabilities.
-/
theorem indepProd_toMeasure_prod {alpha : Type u} {beta : Type v}
    [MeasurableSpace alpha] [MeasurableSpace beta]
    (p : PMF alpha) (q : PMF beta)
    {s : Set alpha} {t : Set beta} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (indepProd p q).toMeasure (Set.prod s t) = p.toMeasure s * q.toMeasure t := by
  classical
  rw [indepProd,
    PMF.toMeasure_bind_apply (p := p) (f := fun a => q.map fun b : beta => (a, b))
      (s := Set.prod s t) (hs := hs.prod ht)]
  have hmap : ∀ a : alpha,
      ((q.map fun b : beta => (a, b)).toMeasure (Set.prod s t)) =
        if a ∈ s then q.toMeasure t else 0 := by
    intro a
    rw [PMF.toMeasure_map_apply (fun b : beta => (a, b)) q (Set.prod s t)
      measurable_prodMk_left (hs.prod ht)]
    by_cases ha : a ∈ s
    · rw [ite_eq_left ha]
      congr 1
      ext b
      constructor
      · intro hb
        exact hb.2
      · intro hb
        exact ⟨ha, hb⟩
    · rw [ite_eq_right ha]
      rw [show (fun b : beta => (a, b)) ⁻¹' Set.prod s t = (∅ : Set beta) by
        ext b
        constructor
        · intro hb
          exact ha hb.1
        · intro hb
          cases hb]
      simp
  simp_rw [hmap]
  calc
    (∑' a : alpha, p a * if a ∈ s then q.toMeasure t else 0)
        = ∑' a : alpha, (s.indicator (fun a => p a) a) * q.toMeasure t := by
          apply tsum_congr
          intro a
          by_cases ha : a ∈ s <;> simp [Set.indicator, ha]
    _ = (∑' a : alpha, s.indicator (fun a => p a) a) * q.toMeasure t := by
          rw [ENNReal.tsum_mul_right]
    _ = p.toMeasure s * q.toMeasure t := by
          rw [PMF.toMeasure_apply p hs]

/--
The measure associated to the independent product PMF is the product of the
two associated measures.
-/
theorem indepProd_toMeasure {alpha : Type u} {beta : Type v}
    [MeasurableSpace alpha] [MeasurableSpace beta]
    (p : PMF alpha) (q : PMF beta) :
    (indepProd p q).toMeasure =
      Measure.prod p.toMeasure q.toMeasure := by
  refine Measure.ext_prod ?_
  intro s t hs ht
  change (indepProd p q).toMeasure (Set.prod s t) =
    (Measure.prod p.toMeasure q.toMeasure) (Set.prod s t)
  rw [indepProd_toMeasure_prod (p := p) (q := q) hs ht]
  exact (Measure.prod_prod (μ := p.toMeasure) (ν := q.toMeasure) s t).symm

/--
A finite joint PMF is absolutely continuous with respect to the independent
product of its two marginals.

Mathematically, if the product of the marginal masses of `(a, b)` is zero, then
one marginal atom is zero, hence the joint atom `p (a, b)` is zero. This is the
support fact needed before comparing finite mutual information with KL
divergence from the joint law to the product of its marginals.
-/
theorem joint_toMeasure_absolutelyContinuous_indepProd_marginals
    {alpha : Type u} {beta : Type v} [Finite alpha] [Finite beta]
    [MeasurableSpace (alpha × beta)] (p : PMF (alpha × beta)) :
    p.toMeasure ≪ (indepProd (fstMarginal p) (sndMarginal p)).toMeasure := by
  classical
  refine Measure.AbsolutelyContinuous.mk ?_
  intro s hs hzero
  rw [PMF.toMeasure_apply p hs]
  apply ENNReal.tsum_eq_zero.2
  intro x
  by_cases hx : x ∈ s
  · have hzero_sum :
        ∑' y : alpha × beta,
          s.indicator (fun y => indepProd (fstMarginal p) (sndMarginal p) y) y = 0 := by
      simpa [PMF.toMeasure_apply (indepProd (fstMarginal p) (sndMarginal p) : PMF (alpha × beta))
        hs] using hzero
    have hxzero :=
      ENNReal.tsum_eq_zero.mp hzero_sum x
    have hprod_zero : indepProd (fstMarginal p) (sndMarginal p) x = 0 := by
      simpa [Set.indicator, hx] using hxzero
    rcases x with ⟨a, b⟩
    rw [Set.indicator_of_mem hx]
    rw [indepProd_apply_eq_zero_iff] at hprod_zero
    rcases hprod_zero with hfst | hsnd
    · exact apply_eq_zero_of_fstMarginal_eq_zero p hfst b
    · exact apply_eq_zero_of_sndMarginal_eq_zero p a hsnd
  · simp [Set.indicator, hx]

/--
Product-measure version of
`joint_toMeasure_absolutelyContinuous_indepProd_marginals`.

This is the form expected by KL-divergence statements that use
`Measure.prod` directly.
-/
theorem joint_toMeasure_absolutelyContinuous_prod_marginals
    {alpha : Type u} {beta : Type v} [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSpace beta] (p : PMF (alpha × beta)) :
    p.toMeasure ≪ Measure.prod (fstMarginal p).toMeasure (sndMarginal p).toMeasure := by
  simpa [indepProd_toMeasure] using
    (joint_toMeasure_absolutelyContinuous_indepProd_marginals (p := p))

end

end Shannon
end LeanInfoTheory
