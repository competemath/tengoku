/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Tengoku

/-!
# Coordinate projections of finite product measures

This file records measure-preserving coordinate projections and refreshes for finite product
measures.

**Projecting along an embedding.** If `e : ι ↪ κ`, restriction of a product-distributed
assignment on `κ` to the coordinates in the image of `e` has the corresponding product law on
`ι`. This is the finite-family form of the fact that a subfamily of independent coordinates is
still independent.

**Reading off a pair of coordinates.** The evaluation map `x ↦ (x a, x b)` at two distinct indices
pushes `Measure.pi μ` forward to `μ a ⊗ μ b`: distinct coordinates of a product measure are
independent, and each single coordinate has law `μ a` (Mathlib's `measurePreserving_eval`). This
is the two-variable companion of `measurePreserving_eval`, and is what transports an
almost-everywhere statement about a pair back to the product space.

**Splitting off one coordinate.** Mathlib's `Equiv.piSplitAt` pushes `Measure.pi μ` forward to
`μ i₀ ⊗ Measure.pi fun j : {i // i ≠ i₀} ↦ μ j`. Mathlib splits a product measure along a
predicate and leaves both halves as products over subtypes; a construction that singles out one
index wants the one-element half collapsed to the factor itself.

**Refreshing a pair of coordinates.** Overwriting two *distinct*
probability coordinates by an independent pair samples the same law: the map

`(z, s, t) ↦ Function.update (Function.update z a s) b t`

pushes `(Measure.pi μ) ⊗ (μ a ⊗ μ b)` forward to `Measure.pi μ`. The two overwritten coordinates
carry the fresh samples and the remaining coordinates keep the ones they had, which is the product
law again.

For `a = b` the pair degenerates to a single refresh because the second update overwrites the
first. The distinctness hypothesis records the two-slot factorisation needed by consumers of this
construction.

## Main statements

* `TauCeti.measurePreserving_pi_comp_embedding` — restricting a product assignment along an
  embedding is measure preserving;
* `TauCeti.measurePreserving_eval_pair` — reading off two distinct coordinates is measure
  preserving;
* `TauCeti.measurePreserving_piSplitAt` — separating the coordinate `i₀` from the rest is
  measure preserving;
* `TauCeti.measurePreserving_update_update` — the two-coordinate refresh is measure
  preserving.

## Implementation

`measurePreserving_eval_pair` reads the pair law off Mathlib's independence of the coordinates of a
product measure, `ProbabilityTheory.iIndepFun_pi`, through
`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`.

The proof of `measurePreserving_update_update` splits the product into the coordinates `{a, b}`
and their complement using Mathlib's measure-preserving product equivalences. The fresh pair
replaces the selected coordinates, while the complementary coordinates are projected from the
original assignment; recombining the two parts is pointwise the double update.
-/

public section

open Function MeasureTheory ProbabilityTheory Set

open scoped ENNReal

namespace TauCeti

open ProbabilityTheory

/-- Restricting a finite product-distributed assignment along an embedding of index types is
measure preserving. The target product uses exactly the marginals selected by the embedding. -/
theorem measurePreserving_pi_comp_embedding {ι κ : Type*} [Fintype ι] [Fintype κ]
    {α : κ → Type*} [∀ j, MeasurableSpace (α j)] (μ : ∀ j, Measure (α j))
    [∀ j, IsProbabilityMeasure (μ j)] (e : ι ↪ κ) :
    MeasurePreserving (fun x : ∀ j, α j => fun i => x (e i))
      (Measure.pi μ) (Measure.pi fun i => μ (e i)) := by
  refine ⟨measurable_pi_iff.mpr fun i => measurable_pi_apply (e i), ?_⟩
  have hindep : iIndepFun (fun i (x : ∀ j, α j) => x (e i)) (Measure.pi μ) :=
    (iIndepFun_pi (μ := μ) fun _ => aemeasurable_id).precomp e.injective
  rw [hindep.map_fun_eq_pi_map fun i => (measurable_pi_apply (e i)).aemeasurable]
  congr 1
  funext i
  exact (measurePreserving_eval μ (e i)).map_eq

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
  [∀ i, MeasurableSpace (α i)]

omit [DecidableEq ι] in
/-- **Two distinct coordinates of a product measure carry the product of their laws.** Reading off
the coordinates `a ≠ b` of a product-distributed assignment pushes `Measure.pi μ` forward to
`μ a ⊗ μ b`.

The one-coordinate statement is Mathlib's `MeasureTheory.measurePreserving_eval`; distinctness is
what makes the pair independent, and hence its law a product. -/
theorem measurePreserving_eval_pair (μ : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (μ i)] {a b : ι} (hab : a ≠ b) :
    MeasurePreserving (fun x : ∀ i, α i => (x a, x b)) (Measure.pi μ) ((μ a).prod (μ b)) := by
  refine ⟨(measurable_pi_apply a).prodMk (measurable_pi_apply b), ?_⟩
  have hindep : (fun x : ∀ i, α i => x a) ⟂ᵢ[Measure.pi μ] fun x : ∀ i, α i => x b :=
    (iIndepFun_pi (X := fun i => (id : α i → α i)) fun _ => aemeasurable_id).indepFun hab
  rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_pi_apply a).aemeasurable
    (measurable_pi_apply b).aemeasurable] at hindep
  rw [hindep, (measurePreserving_eval μ a).map_eq, (measurePreserving_eval μ b).map_eq]

/-- **Splitting off one coordinate of a finite product measure.** Mathlib's `Equiv.piSplitAt`,
which reads a product-distributed assignment as its value at `i₀` paired with its values at the
remaining indices, pushes `Measure.pi μ` forward to
`μ i₀ ⊗ Measure.pi fun j : {i // i ≠ i₀} => μ j`.

This is Mathlib's `MeasureTheory.measurePreserving_piEquivPiSubtypeProd` for the predicate
`(· = i₀)`, with the one-element factor collapsed to `μ i₀`. -/
theorem measurePreserving_piSplitAt (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (i₀ : ι) :
    MeasurePreserving (Equiv.piSplitAt i₀ α)
      (Measure.pi μ) ((μ i₀).prod (Measure.pi fun j : {i // i ≠ i₀} => μ j)) := by
  let _ : Unique {i : ι // i = i₀} := ⟨⟨⟨i₀, rfl⟩⟩, fun x => Subtype.ext x.2⟩
  let _ : Fintype {i : ι // i = i₀} := Subtype.fintype _
  -- Composing the split at `(· = i₀)` with the collapse of its one-element factor evaluates,
  -- coordinate by coordinate, to the pair above.  The application lemmas below reduce both
  -- measurable equivalences to their underlying maps; what is left is that the unique element of
  -- `{i // i = i₀}` is `i₀` and that `i ≠ i₀` is by definition `¬ i = i₀`.
  have hfun : Prod.map (MeasurableEquiv.piUnique fun i : {i : ι // i = i₀} => α i)
        (id : (∀ j : {i : ι // i ≠ i₀}, α j) → ∀ j : {i : ι // i ≠ i₀}, α j) ∘
      MeasurableEquiv.piEquivPiSubtypeProd α (· = i₀)
      = ⇑(Equiv.piSplitAt i₀ α) := by
    funext w
    simp only [Function.comp_apply, MeasurableEquiv.piEquivPiSubtypeProd, MeasurableEquiv.coe_mk,
      Equiv.piEquivPiSubtypeProd_apply, Prod.map_apply, id_eq, MeasurableEquiv.piUnique,
      Equiv.piUnique_apply, Equiv.piSplitAt_apply]
    rfl
  rw [← hfun]
  exact ((measurePreserving_piUnique fun i : {i : ι // i = i₀} => μ i).prod
    (MeasurePreserving.id (Measure.pi fun j : {i : ι // i ≠ i₀} => μ j))).comp
    (measurePreserving_piEquivPiSubtypeProd μ (· = i₀))

end TauCeti
