/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.Entropy

/-!
# Finite Shannon information measures

This file defines the first entropy-derived information measures for finite
joint PMFs. For `p : PMF (alpha × beta)`, `condEntropy p` means `H(alpha | beta)`,
matching the Rocq `infotheo` convention that conditional entropy is the entropy
of the first coordinate conditioned on the second.
-/

namespace LeanInfoTheory
namespace Shannon

open scoped BigOperators

universe u v w x

noncomputable section

/-! ## Marginals -/

/-- The first marginal of a finite joint PMF. -/
abbrev fstMarginal {alpha : Type u} {beta : Type v} (p : PMF (alpha × beta)) : PMF alpha :=
  p.map Prod.fst

/-- The second marginal of a finite joint PMF. -/
abbrev sndMarginal {alpha : Type u} {beta : Type v} (p : PMF (alpha × beta)) : PMF beta :=
  p.map Prod.snd

/--
Taking the first marginal after pushing a PMF forward to a pair is the same as
pushing forward by the first coordinate of that pair-valued map.
-/
@[simp]
theorem fstMarginal_map {omega : Type u} {alpha : Type v} {beta : Type w}
    (p : PMF omega) (f : omega -> alpha × beta) :
    fstMarginal (p.map f) = p.map (fun omega => (f omega).1) := by
  simpa [fstMarginal, Function.comp_def] using
    PMF.map_comp (p := p) (f := f) Prod.fst

/--
Taking the second marginal after pushing a PMF forward to a pair is the same as
pushing forward by the second coordinate of that pair-valued map.
-/
@[simp]
theorem sndMarginal_map {omega : Type u} {alpha : Type v} {beta : Type w}
    (p : PMF omega) (f : omega -> alpha × beta) :
    sndMarginal (p.map f) = p.map (fun omega => (f omega).2) := by
  simpa [sndMarginal, Function.comp_def] using
    PMF.map_comp (p := p) (f := f) Prod.snd

/-- For a joint law built from random variables `(X, Y)`, the first marginal is the law of `X`. -/
@[simp]
theorem fstMarginal_map_pair {omega : Type u} {alpha : Type v} {beta : Type w}
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    fstMarginal (p.map fun omega => (X omega, Y omega)) = p.map X := by
  simp

/-- For a joint law built from random variables `(X, Y)`, the second marginal is the law of `Y`. -/
@[simp]
theorem sndMarginal_map_pair {omega : Type u} {alpha : Type v} {beta : Type w}
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    sndMarginal (p.map fun omega => (X omega, Y omega)) = p.map Y := by
  simp

/-- Swapping the two coordinates turns the first marginal into the original second marginal. -/
@[simp]
theorem fstMarginal_map_swap {alpha : Type u} {beta : Type v}
    (p : PMF (alpha × beta)) :
    fstMarginal (p.map Prod.swap) = sndMarginal p := by
  simp [sndMarginal]

/-- Swapping the two coordinates turns the second marginal into the original first marginal. -/
@[simp]
theorem sndMarginal_map_swap {alpha : Type u} {beta : Type v}
    (p : PMF (alpha × beta)) :
    sndMarginal (p.map Prod.swap) = fstMarginal p := by
  simp [fstMarginal]

/-- The mass of the first marginal is the sum of the joint masses over the second coordinate. -/
theorem fstMarginal_apply {alpha : Type u} {beta : Type v} [Fintype beta]
    (p : PMF (alpha × beta)) (a : alpha) :
    fstMarginal p a = ∑ b, p (a, b) := by
  classical
  -- The fiber of `a` under `Prod.fst` is the finite set `{(a, b) | b : beta}`.
  let fiber : Finset (alpha × beta) := Finset.univ.image fun b : beta => (a, b)
  have hfiber :
      Prod.fst ⁻¹' ({a} : Set alpha) = (fiber : Set (alpha × beta)) := by
    ext x
    rcases x with ⟨a', b⟩
    simp [fiber, eq_comm]
  calc
    fstMarginal p a = (fstMarginal p).toOuterMeasure ({a} : Set alpha) := by
      exact (PMF.toOuterMeasure_apply_singleton (p := fstMarginal p) a).symm
    _ = p.toOuterMeasure (Prod.fst ⁻¹' ({a} : Set alpha)) := by
      rw [fstMarginal, PMF.toOuterMeasure_map_apply]
    _ = p.toOuterMeasure (fiber : Set (alpha × beta)) := by
      rw [hfiber]
    _ = ∑ x ∈ fiber, p x := by
      exact PMF.toOuterMeasure_apply_finset (p := p) fiber
    _ = ∑ b, p (a, b) := by
      change (∑ x ∈ Finset.univ.image (fun b : beta => (a, b)), p x) = ∑ b, p (a, b)
      rw [Finset.sum_image]
      intro b _ b' _ h
      exact congrArg Prod.snd h

/-- The mass of the second marginal is the sum of the joint masses over the first coordinate. -/
theorem sndMarginal_apply {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) (b : beta) :
    sndMarginal p b = ∑ a, p (a, b) := by
  classical
  -- The fiber of `b` under `Prod.snd` is the finite set `{(a, b) | a : alpha}`.
  let fiber : Finset (alpha × beta) := Finset.univ.image fun a : alpha => (a, b)
  have hfiber :
      Prod.snd ⁻¹' ({b} : Set beta) = (fiber : Set (alpha × beta)) := by
    ext x
    rcases x with ⟨a, b'⟩
    simp [fiber, eq_comm]
  calc
    sndMarginal p b = (sndMarginal p).toOuterMeasure ({b} : Set beta) := by
      exact (PMF.toOuterMeasure_apply_singleton (p := sndMarginal p) b).symm
    _ = p.toOuterMeasure (Prod.snd ⁻¹' ({b} : Set beta)) := by
      rw [sndMarginal, PMF.toOuterMeasure_map_apply]
    _ = p.toOuterMeasure (fiber : Set (alpha × beta)) := by
      rw [hfiber]
    _ = ∑ x ∈ fiber, p x := by
      exact PMF.toOuterMeasure_apply_finset (p := p) fiber
    _ = ∑ a, p (a, b) := by
      change (∑ x ∈ Finset.univ.image (fun a : alpha => (a, b)), p x) = ∑ a, p (a, b)
      rw [Finset.sum_image]
      intro a _ a' _ h
      exact congrArg Prod.fst h

/-- The marginal on the first and second coordinates of a finite triple PMF. -/
abbrev fstSndMarginal {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) : PMF (alpha × beta) :=
  p.map fun x => (x.1, x.2.1)

/--
Projection formula for the first-second marginal of a pushed-forward triple
law.
-/
@[simp]
theorem fstSndMarginal_map
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    (p : PMF omega) (f : omega -> alpha × beta × gamma) :
    fstSndMarginal (p.map f) =
      p.map fun omega => ((f omega).1, (f omega).2.1) := by
  simpa [fstSndMarginal, Function.comp_def] using
    PMF.map_comp (p := p) (f := f) (fun x : alpha × beta × gamma => (x.1, x.2.1))

/--
For a joint law built from `(X, Y, Z)`, the first-second marginal is the joint
law of `(X, Y)`.
-/
@[simp]
theorem fstSndMarginal_map_triple
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    fstSndMarginal (p.map fun omega => (X omega, Y omega, Z omega)) =
      p.map fun omega => (X omega, Y omega) := by
  simp

/-- The marginal on the first and third coordinates of a finite triple PMF. -/
abbrev fstThirdMarginal {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) : PMF (alpha × gamma) :=
  p.map fun x => (x.1, x.2.2)

/-- The marginal on the second and third coordinates of a finite triple PMF. -/
abbrev sndThirdMarginal {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) : PMF (beta × gamma) :=
  p.map fun x => (x.2.1, x.2.2)

/-- The marginal on the third coordinate of a finite triple PMF. -/
abbrev thirdMarginal {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) : PMF gamma :=
  p.map fun x => x.2.2

/--
Projection formula for the first-third marginal of a pushed-forward triple
law. This is the triple analogue of `fstMarginal_map`.
-/
@[simp]
theorem fstThirdMarginal_map
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    (p : PMF omega) (f : omega -> alpha × beta × gamma) :
    fstThirdMarginal (p.map f) =
      p.map fun omega => ((f omega).1, (f omega).2.2) := by
  simpa [fstThirdMarginal, Function.comp_def] using
    PMF.map_comp (p := p) (f := f) (fun x : alpha × beta × gamma => (x.1, x.2.2))

/--
Projection formula for the second-third marginal of a pushed-forward triple
law. The product `alpha × beta × gamma` is right-associated in Lean.
-/
@[simp]
theorem sndThirdMarginal_map
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    (p : PMF omega) (f : omega -> alpha × beta × gamma) :
    sndThirdMarginal (p.map f) =
      p.map fun omega => ((f omega).2.1, (f omega).2.2) := by
  simp

/-- Projection formula for the third-coordinate marginal of a pushed-forward triple law. -/
@[simp]
theorem thirdMarginal_map
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    (p : PMF omega) (f : omega -> alpha × beta × gamma) :
    thirdMarginal (p.map f) = p.map fun omega => (f omega).2.2 := by
  simpa [thirdMarginal, Function.comp_def] using
    PMF.map_comp (p := p) (f := f) (fun x : alpha × beta × gamma => x.2.2)

/--
For a joint law built from `(X, Y, Z)`, the first-third marginal is the joint
law of `(X, Z)`.
-/
@[simp]
theorem fstThirdMarginal_map_triple
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    fstThirdMarginal (p.map fun omega => (X omega, Y omega, Z omega)) =
      p.map fun omega => (X omega, Z omega) := by
  simp

/--
For a joint law built from `(X, Y, Z)`, the second-third marginal is the joint
law of `(Y, Z)`.
-/
@[simp]
theorem sndThirdMarginal_map_triple
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    sndThirdMarginal (p.map fun omega => (X omega, Y omega, Z omega)) =
      p.map fun omega => (Y omega, Z omega) := by
  simp

/-- For a joint law built from `(X, Y, Z)`, the third marginal is the law of `Z`. -/
@[simp]
theorem thirdMarginal_map_triple
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    thirdMarginal (p.map fun omega => (X omega, Y omega, Z omega)) = p.map Z := by
  simp

/--
After swapping the first two coordinates of `(A, B, C)`, the first-third
marginal is the original second-third marginal.
-/
@[simp]
theorem fstThirdMarginal_map_swap12
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) :
    fstThirdMarginal (p.map fun x => (x.2.1, x.1, x.2.2)) = sndThirdMarginal p := by
  simp [sndThirdMarginal]

/--
After swapping the first two coordinates of `(A, B, C)`, the second-third
marginal is the original first-third marginal.
-/
@[simp]
theorem sndThirdMarginal_map_swap12
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) :
    sndThirdMarginal (p.map fun x => (x.2.1, x.1, x.2.2)) = fstThirdMarginal p := by
  simp [fstThirdMarginal]

/-- Swapping the first two coordinates leaves the third marginal unchanged. -/
@[simp]
theorem thirdMarginal_map_swap12
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    (p : PMF (alpha × beta × gamma)) :
    thirdMarginal (p.map fun x => (x.2.1, x.1, x.2.2)) = thirdMarginal p := by
  simp [thirdMarginal]

/--
The mass of the first-third marginal is the sum of the triple joint masses over
the second coordinate.
-/
theorem fstThirdMarginal_apply
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Fintype beta]
    (p : PMF (alpha × beta × gamma)) (a : alpha) (c : gamma) :
    fstThirdMarginal p (a, c) = ∑ b, p (a, b, c) := by
  classical
  -- The fiber of `(a, c)` under `(first, third)` is indexed by the middle coordinate.
  let fiber : Finset (alpha × beta × gamma) := Finset.univ.image fun b : beta => (a, b, c)
  have hfiber :
      (fun x : alpha × beta × gamma => (x.1, x.2.2)) ⁻¹'
          ({(a, c)} : Set (alpha × gamma)) =
        (fiber : Set (alpha × beta × gamma)) := by
    ext x
    rcases x with ⟨a', b, c'⟩
    simp [fiber, Prod.ext_iff, eq_comm]
  calc
    fstThirdMarginal p (a, c) =
        (fstThirdMarginal p).toOuterMeasure ({(a, c)} : Set (alpha × gamma)) := by
      exact (PMF.toOuterMeasure_apply_singleton (p := fstThirdMarginal p) (a, c)).symm
    _ = p.toOuterMeasure
        ((fun x : alpha × beta × gamma => (x.1, x.2.2)) ⁻¹'
          ({(a, c)} : Set (alpha × gamma))) := by
      rw [fstThirdMarginal, PMF.toOuterMeasure_map_apply]
    _ = p.toOuterMeasure (fiber : Set (alpha × beta × gamma)) := by
      rw [hfiber]
    _ = ∑ x ∈ fiber, p x := by
      exact PMF.toOuterMeasure_apply_finset (p := p) fiber
    _ = ∑ b, p (a, b, c) := by
      change
        (∑ x ∈ Finset.univ.image (fun b : beta => (a, b, c)), p x) =
          ∑ b, p (a, b, c)
      rw [Finset.sum_image]
      intro b _ b' _ h
      exact congrArg (fun x : alpha × beta × gamma => x.2.1) h

/--
The mass of the second-third marginal is the sum of the triple joint masses over
the first coordinate.
-/
theorem sndThirdMarginal_apply
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Fintype alpha]
    (p : PMF (alpha × beta × gamma)) (b : beta) (c : gamma) :
    sndThirdMarginal p (b, c) = ∑ a, p (a, b, c) := by
  classical
  -- The fiber of `(b, c)` under `(second, third)` is indexed by the first coordinate.
  let fiber : Finset (alpha × beta × gamma) := Finset.univ.image fun a : alpha => (a, b, c)
  have hfiber :
      (fun x : alpha × beta × gamma => (x.2.1, x.2.2)) ⁻¹'
          ({(b, c)} : Set (beta × gamma)) =
        (fiber : Set (alpha × beta × gamma)) := by
    ext x
    rcases x with ⟨a, b', c'⟩
    simp [fiber, Prod.ext_iff, eq_comm]
  calc
    sndThirdMarginal p (b, c) =
        (sndThirdMarginal p).toOuterMeasure ({(b, c)} : Set (beta × gamma)) := by
      exact (PMF.toOuterMeasure_apply_singleton (p := sndThirdMarginal p) (b, c)).symm
    _ = p.toOuterMeasure
        ((fun x : alpha × beta × gamma => (x.2.1, x.2.2)) ⁻¹'
          ({(b, c)} : Set (beta × gamma))) := by
      rw [sndThirdMarginal, PMF.toOuterMeasure_map_apply]
    _ = p.toOuterMeasure (fiber : Set (alpha × beta × gamma)) := by
      rw [hfiber]
    _ = ∑ x ∈ fiber, p x := by
      exact PMF.toOuterMeasure_apply_finset (p := p) fiber
    _ = ∑ a, p (a, b, c) := by
      change
        (∑ x ∈ Finset.univ.image (fun a : alpha => (a, b, c)), p x) =
          ∑ a, p (a, b, c)
      rw [Finset.sum_image]
      intro a _ a' _ h
      exact congrArg Prod.fst h

/--
The mass of the third marginal is the sum of the triple joint masses over the
first two coordinates.
-/
theorem thirdMarginal_apply
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta × gamma)) (c : gamma) :
    thirdMarginal p c = ∑ a, ∑ b, p (a, b, c) := by
  classical
  -- The fiber of `c` under the third projection is indexed by pairs `(a, b)`.
  let fiber : Finset (alpha × beta × gamma) :=
    (Finset.univ : Finset (alpha × beta)).image fun x => (x.1, x.2, c)
  have hfiber :
      (fun x : alpha × beta × gamma => x.2.2) ⁻¹' ({c} : Set gamma) =
        (fiber : Set (alpha × beta × gamma)) := by
    ext x
    rcases x with ⟨a, b, c'⟩
    simp [fiber, eq_comm]
  calc
    thirdMarginal p c = (thirdMarginal p).toOuterMeasure ({c} : Set gamma) := by
      exact (PMF.toOuterMeasure_apply_singleton (p := thirdMarginal p) c).symm
    _ = p.toOuterMeasure
        ((fun x : alpha × beta × gamma => x.2.2) ⁻¹' ({c} : Set gamma)) := by
      rw [thirdMarginal, PMF.toOuterMeasure_map_apply]
    _ = p.toOuterMeasure (fiber : Set (alpha × beta × gamma)) := by
      rw [hfiber]
    _ = ∑ x ∈ fiber, p x := by
      exact PMF.toOuterMeasure_apply_finset (p := p) fiber
    _ = ∑ a, ∑ b, p (a, b, c) := by
      change
        (∑ x ∈ (Finset.univ : Finset (alpha × beta)).image
            (fun x : alpha × beta => (x.1, x.2, c)), p x) =
          ∑ a, ∑ b, p (a, b, c)
      rw [Finset.sum_image]
      · simpa using
          (Finset.sum_product
            (s := (Finset.univ : Finset alpha))
            (t := (Finset.univ : Finset beta))
            (f := fun x : alpha × beta => p (x.1, x.2, c)))
      · intro x _ y _ h
        rcases x with ⟨a, b⟩
        rcases y with ⟨a', b'⟩
        simp only [Prod.mk.injEq] at h ⊢
        exact ⟨h.1, h.2.1⟩

-- In `ℝ≥0∞`, every term of a finite sum is bounded by the whole sum.
private theorem finset_apply_le_sum {ι : Type u} [Fintype ι]
    (f : ι -> ENNReal) (i : ι) : f i ≤ ∑ j, f j := by
  classical
  exact Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ i)

/--
A joint atom mass is bounded by the mass of its first marginal atom. This is
the basic support/domination fact behind conditioning on the first coordinate.
-/
theorem apply_le_fstMarginal {alpha : Type u} {beta : Type v} [Finite beta]
    (p : PMF (alpha × beta)) (a : alpha) (b : beta) :
    p (a, b) ≤ fstMarginal p a := by
  classical
  let := Fintype.ofFinite beta
  rw [fstMarginal_apply (p := p) (a := a)]
  exact finset_apply_le_sum (fun b' => p (a, b')) b

/--
A joint atom mass is bounded by the mass of its second marginal atom.
-/
theorem apply_le_sndMarginal {alpha : Type u} {beta : Type v} [Finite alpha]
    (p : PMF (alpha × beta)) (a : alpha) (b : beta) :
    p (a, b) ≤ sndMarginal p b := by
  classical
  let := Fintype.ofFinite alpha
  rw [sndMarginal_apply (p := p) (b := b)]
  exact finset_apply_le_sum (fun a' => p (a', b)) a

/--
In a triple law, a full atom is bounded by the corresponding `(first, third)`
marginal atom.
-/
theorem apply_le_fstThirdMarginal
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Finite beta]
    (p : PMF (alpha × beta × gamma)) (a : alpha) (b : beta) (c : gamma) :
    p (a, b, c) ≤ fstThirdMarginal p (a, c) := by
  classical
  let := Fintype.ofFinite beta
  rw [fstThirdMarginal_apply (p := p) (a := a) (c := c)]
  exact finset_apply_le_sum (fun b' => p (a, b', c)) b

/--
In a triple law, a full atom is bounded by the corresponding `(second, third)`
marginal atom.
-/
theorem apply_le_sndThirdMarginal
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Finite alpha]
    (p : PMF (alpha × beta × gamma)) (a : alpha) (b : beta) (c : gamma) :
    p (a, b, c) ≤ sndThirdMarginal p (b, c) := by
  classical
  let := Fintype.ofFinite alpha
  rw [sndThirdMarginal_apply (p := p) (b := b) (c := c)]
  exact finset_apply_le_sum (fun a' => p (a', b, c)) a

/--
In a triple law, a full atom is bounded by the mass of its third-coordinate
marginal atom. This is the support fact needed for conditioning on `gamma`.
-/
theorem apply_le_thirdMarginal
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Finite alpha] [Finite beta]
    (p : PMF (alpha × beta × gamma)) (a : alpha) (b : beta) (c : gamma) :
    p (a, b, c) ≤ thirdMarginal p c := by
  classical
  let := Fintype.ofFinite alpha
  let := Fintype.ofFinite beta
  have hinner : p (a, b, c) ≤ ∑ b', p (a, b', c) :=
    finset_apply_le_sum (fun b' => p (a, b', c)) b
  have houter : (∑ b', p (a, b', c)) ≤ ∑ a', ∑ b', p (a', b', c) :=
    finset_apply_le_sum (fun a' => ∑ b', p (a', b', c)) a
  calc
    p (a, b, c) ≤ ∑ b', p (a, b', c) := hinner
    _ ≤ thirdMarginal p c := by
      rw [thirdMarginal_apply (p := p) (c := c)]
      exact houter

/--
If a first marginal atom has zero mass, then every joint atom over that first
coordinate has zero mass.
-/
theorem apply_eq_zero_of_fstMarginal_eq_zero {alpha : Type u} {beta : Type v}
    [Finite beta] (p : PMF (alpha × beta)) {a : alpha}
    (h : fstMarginal p a = 0) (b : beta) :
    p (a, b) = 0 := by
  exact le_antisymm (by simpa [h] using apply_le_fstMarginal p a b) zero_le

/--
If a second marginal atom has zero mass, then every joint atom over that second
coordinate has zero mass.
-/
theorem apply_eq_zero_of_sndMarginal_eq_zero {alpha : Type u} {beta : Type v}
    [Finite alpha] (p : PMF (alpha × beta)) (a : alpha) {b : beta}
    (h : sndMarginal p b = 0) :
    p (a, b) = 0 := by
  exact le_antisymm (by simpa [h] using apply_le_sndMarginal p a b) zero_le

/--
Nonzero joint mass forces the corresponding first marginal mass to be nonzero.
-/
theorem fstMarginal_ne_zero_of_apply_ne_zero {alpha : Type u} {beta : Type v}
    [Finite beta] (p : PMF (alpha × beta)) {a : alpha} {b : beta}
    (h : p (a, b) ≠ 0) :
    fstMarginal p a ≠ 0 := by
  intro hmarg
  exact h (apply_eq_zero_of_fstMarginal_eq_zero p hmarg b)

/--
Nonzero joint mass forces the corresponding second marginal mass to be nonzero.
-/
theorem sndMarginal_ne_zero_of_apply_ne_zero {alpha : Type u} {beta : Type v}
    [Finite alpha] (p : PMF (alpha × beta)) {a : alpha} {b : beta}
    (h : p (a, b) ≠ 0) :
    sndMarginal p b ≠ 0 := by
  intro hmarg
  exact h (apply_eq_zero_of_sndMarginal_eq_zero p a hmarg)

/--
If a `(first, third)` marginal atom has zero mass, then every triple atom over
that pair has zero mass.
-/
theorem apply_eq_zero_of_fstThirdMarginal_eq_zero
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Finite beta]
    (p : PMF (alpha × beta × gamma)) {a : alpha} (b : beta) {c : gamma}
    (h : fstThirdMarginal p (a, c) = 0) :
    p (a, b, c) = 0 := by
  exact le_antisymm (by simpa [h] using apply_le_fstThirdMarginal p a b c) zero_le

/--
If a `(second, third)` marginal atom has zero mass, then every triple atom over
that pair has zero mass.
-/
theorem apply_eq_zero_of_sndThirdMarginal_eq_zero
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Finite alpha]
    (p : PMF (alpha × beta × gamma)) (a : alpha) {b : beta} {c : gamma}
    (h : sndThirdMarginal p (b, c) = 0) :
    p (a, b, c) = 0 := by
  exact le_antisymm (by simpa [h] using apply_le_sndThirdMarginal p a b c) zero_le

/--
If a third marginal atom has zero mass, then every triple atom over that third
coordinate has zero mass.
-/
theorem apply_eq_zero_of_thirdMarginal_eq_zero
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Finite alpha] [Finite beta]
    (p : PMF (alpha × beta × gamma)) (a : alpha) (b : beta) {c : gamma}
    (h : thirdMarginal p c = 0) :
    p (a, b, c) = 0 := by
  exact le_antisymm (by simpa [h] using apply_le_thirdMarginal p a b c) zero_le

/--
Nonzero triple mass forces the corresponding `(first, third)` marginal mass to
be nonzero.
-/
theorem fstThirdMarginal_ne_zero_of_apply_ne_zero
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Finite beta]
    (p : PMF (alpha × beta × gamma)) {a : alpha} {b : beta} {c : gamma}
    (h : p (a, b, c) ≠ 0) :
    fstThirdMarginal p (a, c) ≠ 0 := by
  intro hmarg
  exact h (apply_eq_zero_of_fstThirdMarginal_eq_zero p b hmarg)

/--
Nonzero triple mass forces the corresponding `(second, third)` marginal mass to
be nonzero.
-/
theorem sndThirdMarginal_ne_zero_of_apply_ne_zero
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Finite alpha]
    (p : PMF (alpha × beta × gamma)) {a : alpha} {b : beta} {c : gamma}
    (h : p (a, b, c) ≠ 0) :
    sndThirdMarginal p (b, c) ≠ 0 := by
  intro hmarg
  exact h (apply_eq_zero_of_sndThirdMarginal_eq_zero p a hmarg)

/--
Nonzero triple mass forces the corresponding third-coordinate marginal mass to
be nonzero.
-/
theorem thirdMarginal_ne_zero_of_apply_ne_zero
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Finite alpha] [Finite beta]
    (p : PMF (alpha × beta × gamma)) {a : alpha} {b : beta} {c : gamma}
    (h : p (a, b, c) ≠ 0) :
    thirdMarginal p c ≠ 0 := by
  intro hmarg
  exact h (apply_eq_zero_of_thirdMarginal_eq_zero p a b hmarg)

/-! ## Information Measures -/

/-- Conditional entropy `H(alpha | beta)` of a finite joint PMF on `alpha × beta`. -/
def condEntropy {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) : Real :=
  entropy p - entropy (sndMarginal p)

/-- Mutual information `I(alpha; beta)` of a finite joint PMF on `alpha × beta`. -/
def mutualInfo {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) : Real :=
  entropy (fstMarginal p) + entropy (sndMarginal p) - entropy p

/--
Conditional mutual information `I(alpha; beta | gamma)` of a finite joint PMF on
`alpha × beta × gamma`, where the product is Lean's right-associated product.
-/
def condMutualInfo {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) : Real :=
  entropy (fstThirdMarginal p) + entropy (sndThirdMarginal p) -
    entropy (thirdMarginal p) - entropy p

/-- Conditional entropy `H(X | Y)` for finite-valued random variables. -/
def condEntropyOf {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) : Real :=
  condEntropy (p.map fun omega => (X omega, Y omega))

/-- Mutual information `I(X; Y)` for finite-valued random variables. -/
def mutualInfoOf {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) : Real :=
  mutualInfo (p.map fun omega => (X omega, Y omega))

/-- Conditional mutual information `I(X; Y | Z)` for finite-valued random variables. -/
def condMutualInfoOf {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) : Real :=
  condMutualInfo (p.map fun omega => (X omega, Y omega, Z omega))

/-! ## Symmetry Theorems -/

/-- Mutual information is symmetric under swapping the two coordinates of a joint law. -/
@[simp]
theorem mutualInfo_map_swap {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    mutualInfo (p.map Prod.swap) = mutualInfo p := by
  unfold mutualInfo
  rw [fstMarginal_map_swap, sndMarginal_map_swap, entropy_map_swap]
  ring

/-- Mutual information of finite-valued random variables is symmetric: `I(Y;X) = I(X;Y)`. -/
theorem mutualInfoOf_swap
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    mutualInfoOf p Y X = mutualInfoOf p X Y := by
  simpa [mutualInfoOf, Function.comp_def, PMF.map_comp] using
    mutualInfo_map_swap
      (p := p.map fun omega => (X omega, Y omega))

/--
Conditional mutual information is symmetric in its first two coordinates:
`I(B;A | C) = I(A;B | C)`.
-/
@[simp]
theorem condMutualInfo_map_swap12
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condMutualInfo (p.map fun x => (x.2.1, x.1, x.2.2)) = condMutualInfo p := by
  have hswap :
      Function.Injective (fun x : alpha × beta × gamma => (x.2.1, x.1, x.2.2)) := by
    intro x y h
    exact
      Prod.ext
        (congrArg (fun z : beta × alpha × gamma => z.2.1) h)
        (Prod.ext
          (congrArg (fun z : beta × alpha × gamma => z.1) h)
          (congrArg (fun z : beta × alpha × gamma => z.2.2) h))
  have hentropy :
      entropy (p.map fun x => (x.2.1, x.1, x.2.2)) = entropy p :=
    entropy_map_injective (p := p) hswap
  unfold condMutualInfo
  rw [fstThirdMarginal_map_swap12, sndThirdMarginal_map_swap12,
    thirdMarginal_map_swap12, hentropy]
  ring

/--
Conditional mutual information of finite-valued random variables is symmetric
in the first two variables: `I(Y;X | Z) = I(X;Y | Z)`.
-/
theorem condMutualInfoOf_swap
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condMutualInfoOf p Y X Z = condMutualInfoOf p X Y Z := by
  simpa [condMutualInfoOf, Function.comp_def, PMF.map_comp] using
    condMutualInfo_map_swap12
      (p := p.map fun omega => (X omega, Y omega, Z omega))

/-! ## Coordinate Projection Identities -/

/-- Entropy of the first coordinate projection is entropy of the first marginal. -/
@[simp]
theorem entropyOf_fst {alpha : Type u} {beta : Type v} [Fintype alpha]
    (p : PMF (alpha × beta)) :
    entropyOf p Prod.fst = entropy (fstMarginal p) :=
  rfl

/-- Entropy of the second coordinate projection is entropy of the second marginal. -/
@[simp]
theorem entropyOf_snd {alpha : Type u} {beta : Type v} [Fintype beta]
    (p : PMF (alpha × beta)) :
    entropyOf p Prod.snd = entropy (sndMarginal p) :=
  rfl

/--
The joint entropy of the two coordinate projections of an existing pair law is
the entropy of that pair law itself.
-/
@[simp]
theorem jointEntropyOf_fst_snd {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    jointEntropyOf p Prod.fst Prod.snd = jointEntropy p := by
  unfold jointEntropyOf entropyOf jointEntropy
  rw [show (fun omega : alpha × beta => (Prod.fst omega, Prod.snd omega)) = id by
    funext omega
    cases omega
    rfl]
  simp [PMF.map_id]

/--
Conditional entropy of the coordinate projections of a pair law recovers the
PMF-level conditional entropy of that pair law.
-/
@[simp]
theorem condEntropyOf_fst_snd {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    condEntropyOf p Prod.fst Prod.snd = condEntropy p := by
  unfold condEntropyOf
  rw [show (fun omega : alpha × beta => (Prod.fst omega, Prod.snd omega)) = id by
    funext omega
    cases omega
    rfl]
  simp [PMF.map_id]

/--
Mutual information of the coordinate projections of a pair law recovers the
PMF-level mutual information of that pair law.
-/
@[simp]
theorem mutualInfoOf_fst_snd {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta] (p : PMF (alpha × beta)) :
    mutualInfoOf p Prod.fst Prod.snd = mutualInfo p := by
  unfold mutualInfoOf
  rw [show (fun omega : alpha × beta => (Prod.fst omega, Prod.snd omega)) = id by
    funext omega
    cases omega
    rfl]
  simp [PMF.map_id]

/-- Entropy of the third coordinate projection is entropy of the third marginal. -/
@[simp]
theorem entropyOf_third
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    entropyOf p (fun x => x.2.2) = entropy (thirdMarginal p) :=
  rfl

/--
Joint entropy of the first and third coordinate projections is the entropy of
the first-third marginal.
-/
@[simp]
theorem jointEntropyOf_fst_third
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Fintype alpha] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    jointEntropyOf p (fun x => x.1) (fun x => x.2.2) =
      jointEntropy (fstThirdMarginal p) :=
  rfl

/--
Joint entropy of the second and third coordinate projections is the entropy of
the second-third marginal.
-/
@[simp]
theorem jointEntropyOf_snd_third
    {alpha : Type u} {beta : Type v} {gamma : Type w} [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    jointEntropyOf p (fun x => x.2.1) (fun x => x.2.2) =
      jointEntropy (sndThirdMarginal p) :=
  rfl

/--
Conditional mutual information of the coordinate projections of a triple law
recovers the PMF-level `I(first; second | third)` quantity.
-/
@[simp]
theorem condMutualInfoOf_fst_snd_third
    {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condMutualInfoOf p (fun x => x.1) (fun x => x.2.1) (fun x => x.2.2) =
      condMutualInfo p := by
  unfold condMutualInfoOf
  rw [show (fun omega : alpha × beta × gamma => (omega.1, omega.2.1, omega.2.2)) =
      id by
    funext omega
    rcases omega with ⟨a, b, c⟩
    rfl]
  simp [PMF.map_id]

/-! ## Definitional Identities -/

/-- Unfolding lemma for the entropy-identity definition of conditional entropy. -/
theorem condEntropy_eq {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    condEntropy p = entropy p - entropy (sndMarginal p) :=
  rfl

/-- Unfolding lemma for the entropy-identity definition of mutual information. -/
theorem mutualInfo_eq {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    mutualInfo p = entropy (fstMarginal p) + entropy (sndMarginal p) - entropy p :=
  rfl

/--
Unfolding lemma for the entropy-identity definition of conditional mutual
information.
-/
theorem condMutualInfo_eq {alpha : Type u} {beta : Type v} {gamma : Type w}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF (alpha × beta × gamma)) :
    condMutualInfo p =
      entropy (fstThirdMarginal p) + entropy (sndThirdMarginal p) -
        entropy (thirdMarginal p) - entropy p :=
  rfl

/-! ## Conditional Entropy Chain Rules -/

/--
Conditional entropy chain rule for a joint PMF:
`H(A,B) = H(B) + H(A | B)`.
-/
theorem entropy_eq_entropy_sndMarginal_add_condEntropy
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    entropy p = entropy (sndMarginal p) + condEntropy p := by
  rw [condEntropy_eq]
  ring

/--
Swapped conditional entropy chain rule for a joint PMF:
`H(A,B) = H(A) + H(B | A)`.
-/
theorem entropy_eq_entropy_fstMarginal_add_condEntropy_swap
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    entropy p = entropy (fstMarginal p) + condEntropy (p.map Prod.swap) := by
  calc
    entropy p = entropy (p.map Prod.swap) := (entropy_map_swap p).symm
    _ = entropy (sndMarginal (p.map Prod.swap)) + condEntropy (p.map Prod.swap) := by
      exact entropy_eq_entropy_sndMarginal_add_condEntropy (p.map Prod.swap)
    _ = entropy (fstMarginal p) + condEntropy (p.map Prod.swap) := by
      rw [sndMarginal_map_swap]

/--
Conditional entropy chain rule for finite-valued random variables:
`H(X,Y) = H(Y) + H(X | Y)`.
-/
theorem jointEntropyOf_eq_entropyOf_add_condEntropyOf
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    jointEntropyOf p X Y = entropyOf p Y + condEntropyOf p X Y := by
  simpa [jointEntropyOf, entropyOf, condEntropyOf] using
    entropy_eq_entropy_sndMarginal_add_condEntropy
      (p := p.map fun omega => (X omega, Y omega))

/--
Swapped conditional entropy chain rule for finite-valued random variables:
`H(X,Y) = H(X) + H(Y | X)`.
-/
theorem jointEntropyOf_eq_entropyOf_add_condEntropyOf_swap
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    jointEntropyOf p X Y = entropyOf p X + condEntropyOf p Y X := by
  rw [← jointEntropyOf_swap (p := p) (X := X) (Y := Y)]
  exact jointEntropyOf_eq_entropyOf_add_condEntropyOf (p := p) (X := Y) (Y := X)

/-! ## Textbook-Facing Chain-Rule Aliases -/

/-- Right-oriented PMF entropy chain rule: `H(A,B) = H(B) + H(A|B)`. -/
theorem entropy_chain_rule_right
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    entropy p = entropy (sndMarginal p) + condEntropy p :=
  entropy_eq_entropy_sndMarginal_add_condEntropy p

/-- Left-oriented PMF entropy chain rule: `H(A,B) = H(A) + H(B|A)`. -/
theorem entropy_chain_rule_left
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    entropy p = entropy (fstMarginal p) + condEntropy (p.map Prod.swap) :=
  entropy_eq_entropy_fstMarginal_add_condEntropy_swap p

/-- Right-oriented random-variable entropy chain rule. -/
theorem jointEntropyOf_chain_rule_right
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    jointEntropyOf p X Y = entropyOf p Y + condEntropyOf p X Y :=
  jointEntropyOf_eq_entropyOf_add_condEntropyOf p X Y

/-- Left-oriented random-variable entropy chain rule. -/
theorem jointEntropyOf_chain_rule_left
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    jointEntropyOf p X Y = entropyOf p X + condEntropyOf p Y X :=
  jointEntropyOf_eq_entropyOf_add_condEntropyOf_swap p X Y

/-! ## Random-Variable Identities -/

/--
Random-variable conditional entropy rewrites to joint entropy minus entropy of
the conditioning variable.
-/
theorem condEntropyOf_eq {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    condEntropyOf p X Y = jointEntropyOf p X Y - entropyOf p Y := by
  simp [condEntropyOf, condEntropy_eq, jointEntropyOf, entropyOf]

/-! ## Triple Conditional Entropy Chain Rules -/

/--
Conditional joint entropy is invariant under swapping the two variables being
conditioned: `H(Y,X|Z) = H(X,Y|Z)`.
-/
theorem condEntropyOf_pair_swap
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condEntropyOf p (fun omega => (Y omega, X omega)) Z =
      condEntropyOf p (fun omega => (X omega, Y omega)) Z := by
  let swapPair : (alpha × beta) × gamma -> (beta × alpha) × gamma :=
    fun z => ((z.1.2, z.1.1), z.2)
  have hswap : Function.Injective swapPair := by
    intro z z' h
    exact
      Prod.ext
        (Prod.ext
          (congrArg (fun t : (beta × alpha) × gamma => t.1.2) h)
          (congrArg (fun t : (beta × alpha) × gamma => t.1.1) h))
        (congrArg (fun t : (beta × alpha) × gamma => t.2) h)
  have hmap :
      (p.map fun omega => ((Y omega, X omega), Z omega)) =
        (p.map fun omega => ((X omega, Y omega), Z omega)).map swapPair := by
    simpa [swapPair, Function.comp_def] using
      (PMF.map_comp
        (p := p)
        (f := fun omega => ((X omega, Y omega), Z omega))
        (g := swapPair)).symm
  have hjoint :
      jointEntropyOf p (fun omega => (Y omega, X omega)) Z =
        jointEntropyOf p (fun omega => (X omega, Y omega)) Z := by
    unfold jointEntropyOf entropyOf
    rw [hmap]
    exact
      entropy_map_injective
        (p := p.map fun omega => ((X omega, Y omega), Z omega)) hswap
  rw [condEntropyOf_eq, condEntropyOf_eq, hjoint]

/--
Triple conditional-entropy chain rule:
`H(X,Y|Z) = H(Y|Z) + H(X|Y,Z)`.
-/
theorem condEntropyOf_pair_chain_rule
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condEntropyOf p (fun omega => (X omega, Y omega)) Z =
      condEntropyOf p Y Z +
        condEntropyOf p X (fun omega => (Y omega, Z omega)) := by
  rw [condEntropyOf_eq, condEntropyOf_eq, condEntropyOf_eq]
  unfold jointEntropyOf
  rw [entropyOf_prodAssoc]
  ring

/--
Swapped triple conditional-entropy chain rule:
`H(X,Y|Z) = H(X|Z) + H(Y|X,Z)`.
-/
theorem condEntropyOf_pair_chain_rule_swap
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condEntropyOf p (fun omega => (X omega, Y omega)) Z =
      condEntropyOf p X Z +
        condEntropyOf p Y (fun omega => (X omega, Z omega)) := by
  calc
    condEntropyOf p (fun omega => (X omega, Y omega)) Z =
        condEntropyOf p (fun omega => (Y omega, X omega)) Z :=
      (condEntropyOf_pair_swap p X Y Z).symm
    _ = condEntropyOf p X Z +
          condEntropyOf p Y (fun omega => (X omega, Z omega)) :=
      condEntropyOf_pair_chain_rule p Y X Z

/--
Random-variable mutual information rewrites to the standard entropy identity
`H(X) + H(Y) - H(X,Y)`.
-/
theorem mutualInfoOf_eq {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    mutualInfoOf p X Y =
      entropyOf p X + entropyOf p Y - jointEntropyOf p X Y := by
  simp [mutualInfoOf, mutualInfo_eq, jointEntropyOf, entropyOf]

/--
Random-variable conditional mutual information rewrites to the entropy identity
`H(X,Z) + H(Y,Z) - H(Z) - H(X,Y,Z)`.
-/
theorem condMutualInfoOf_eq
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condMutualInfoOf p X Y Z =
      jointEntropyOf p X Z + jointEntropyOf p Y Z -
        entropyOf p Z - entropyOf p (fun omega => (X omega, Y omega, Z omega)) := by
  simp [condMutualInfoOf, condMutualInfo_eq, jointEntropyOf, entropyOf]

/-! ## Conditional Mutual Information Identities -/

/--
Conditional mutual information as a difference of conditional entropies:
`I(X;Y|Z) = H(X|Z) - H(X|Y,Z)`.
-/
theorem condMutualInfoOf_eq_condEntropyOf_sub_condEntropyOf
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condMutualInfoOf p X Y Z =
      condEntropyOf p X Z -
        condEntropyOf p X (fun omega => (Y omega, Z omega)) := by
  rw [condMutualInfoOf_eq, condEntropyOf_eq, condEntropyOf_eq]
  unfold jointEntropyOf
  ring

/--
Symmetric conditional-entropy difference form:
`I(X;Y|Z) = H(Y|Z) - H(Y|X,Z)`.
-/
theorem condMutualInfoOf_eq_condEntropyOf_sub_condEntropyOf_swap
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condMutualInfoOf p X Y Z =
      condEntropyOf p Y Z -
        condEntropyOf p Y (fun omega => (X omega, Z omega)) := by
  calc
    condMutualInfoOf p X Y Z = condMutualInfoOf p Y X Z :=
      (condMutualInfoOf_swap p X Y Z).symm
    _ = condEntropyOf p Y Z -
          condEntropyOf p Y (fun omega => (X omega, Z omega)) :=
      condMutualInfoOf_eq_condEntropyOf_sub_condEntropyOf p Y X Z

/--
Conditional mutual information as conditional marginal entropies minus
conditional joint entropy:
`I(X;Y|Z) = H(X|Z) + H(Y|Z) - H(X,Y|Z)`.
-/
theorem condMutualInfoOf_eq_condEntropyOf_add_condEntropyOf_sub_condEntropyOf_pair
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) (Z : omega -> gamma) :
    condMutualInfoOf p X Y Z =
      condEntropyOf p X Z + condEntropyOf p Y Z -
        condEntropyOf p (fun omega => (X omega, Y omega)) Z := by
  rw [condMutualInfoOf_eq, condEntropyOf_eq, condEntropyOf_eq, condEntropyOf_eq]
  unfold jointEntropyOf
  rw [entropyOf_prodAssoc p X Y Z]
  ring

/-! ## Elementary Mutual Information Identities -/

/-- Mutual information as `I(A;B) = H(A) - H(A|B)`. -/
theorem mutualInfo_eq_entropy_fstMarginal_sub_condEntropy
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    mutualInfo p = entropy (fstMarginal p) - condEntropy p := by
  rw [mutualInfo_eq, condEntropy_eq]
  ring

/-- Mutual information as `I(A;B) = H(B) - H(B|A)`. -/
theorem mutualInfo_eq_entropy_sndMarginal_sub_condEntropy_swap
    {alpha : Type u} {beta : Type v} [Fintype alpha] [Fintype beta]
    (p : PMF (alpha × beta)) :
    mutualInfo p =
      entropy (sndMarginal p) - condEntropy (p.map Prod.swap) := by
  rw [mutualInfo_eq, condEntropy_eq, sndMarginal_map_swap, entropy_map_swap]
  ring

/-- Random-variable form `I(X;Y) = H(X) - H(X|Y)`. -/
theorem mutualInfoOf_eq_entropyOf_sub_condEntropyOf
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    mutualInfoOf p X Y = entropyOf p X - condEntropyOf p X Y := by
  rw [mutualInfoOf_eq, condEntropyOf_eq]
  ring

/-- Symmetric random-variable form `I(X;Y) = H(Y) - H(Y|X)`. -/
theorem mutualInfoOf_eq_entropyOf_sub_condEntropyOf_swap
    {omega : Type u} {alpha : Type v} {beta : Type w}
    [Fintype alpha] [Fintype beta]
    (p : PMF omega) (X : omega -> alpha) (Y : omega -> beta) :
    mutualInfoOf p X Y = entropyOf p Y - condEntropyOf p Y X := by
  calc
    mutualInfoOf p X Y = mutualInfoOf p Y X :=
      (mutualInfoOf_swap p X Y).symm
    _ = entropyOf p Y - condEntropyOf p Y X :=
      mutualInfoOf_eq_entropyOf_sub_condEntropyOf p Y X

/--
Decompose `I(Y;Z)` through an auxiliary variable `X`.

In canonical nats,
`I(Y;Z) = H(Y|X) - I(X;Z|Y) - H(Y|(X,Z)) + I(X;Z)`,
where `(X,Z)` is the ordered conditioning pair. The source type is arbitrary;
only the three observed alphabets are finite.
-/
theorem mutualInfoOf_condEntropyOf_decomposition
    {omega : Type u} {alpha : Type v} {beta : Type w} {gamma : Type x}
    [Fintype alpha] [Fintype beta] [Fintype gamma]
    (p : PMF omega) (X : omega → alpha) (Y : omega → beta) (Z : omega → gamma) :
    mutualInfoOf p Y Z =
      condEntropyOf p Y X - condMutualInfoOf p X Z Y -
        condEntropyOf p Y (fun omega => (X omega, Z omega)) +
        mutualInfoOf p X Z := by
  simp only [mutualInfoOf_eq, condEntropyOf_eq, condMutualInfoOf_eq]
  rw [jointEntropyOf_swap p X Y, jointEntropyOf_swap p Y Z,
    jointEntropyOf_swap p (fun omega => (X omega, Z omega)) Y,
    entropyOf_prodAssoc p X Z Y]
  unfold jointEntropyOf
  ring

/-- A diagonal joint law has mutual information equal to its source entropy. -/
@[simp]
theorem mutualInfo_map_diag
    {alpha : Type u} [Fintype alpha] (p : PMF alpha) :
    mutualInfo (p.map fun a => (a, a)) = entropy p := by
  have hdiag : Function.Injective (fun a : alpha => (a, a)) := by
    intro a a' h
    exact congrArg Prod.fst h
  have hfst : fstMarginal (p.map fun a => (a, a)) = p := by
    rw [fstMarginal_map]
    change p.map id = p
    exact PMF.map_id p
  have hsnd : sndMarginal (p.map fun a => (a, a)) = p := by
    rw [sndMarginal_map]
    change p.map id = p
    exact PMF.map_id p
  rw [mutualInfo_eq, hfst, hsnd, entropy_map_injective p hdiag]
  ring

/-- The mutual information of a finite-valued variable with itself is its entropy. -/
@[simp]
theorem mutualInfoOf_self
    {omega : Type u} {alpha : Type v} [Fintype alpha]
    (p : PMF omega) (X : omega -> alpha) :
    mutualInfoOf p X X = entropyOf p X := by
  simpa [mutualInfoOf, entropyOf, Function.comp_def, PMF.map_comp] using
    mutualInfo_map_diag (p.map X)

end

end Shannon
end LeanInfoTheory
