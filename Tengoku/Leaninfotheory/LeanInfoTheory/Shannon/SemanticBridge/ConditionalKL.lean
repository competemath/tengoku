/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.DataProcessing
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.KL

/-!
# Conditional relative entropy for PMF channels

This opt-in semantic-bridge module defines conditional relative entropy for
two PMF-valued channels under one common input law. The canonical value is
mathlib's `ENNReal`-valued KL divergence between the two induced joint laws.

The definition itself needs no finiteness assumptions. Finite weighted-fiber
semantics and the joint KL chain rule are developed in later theorem sections.

If `r x = 0`, both induced joint laws assign zero mass to every pair `(x, y)`.
The channel values `W x` and `V x` are therefore ignored at that base atom.
This is a property of the joint-law representation; it does not assign a
separate probabilistic meaning or fallback value to a null fiber.
-/

namespace LeanInfoTheory
namespace Shannon

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

universe u v

/-! ## Definition -/

/--
Conditional relative entropy between two channels under a common input law.

This is the KL divergence between the two induced joint laws. Consequently,
channel values outside the support of `r` do not affect the result: their
entire joint-law fiber has zero mass. No per-fiber KL convention is imposed at
those null base atoms.
-/
def conditionalKlDiv
    {alpha : Type u} {beta : Type v}
    [MeasurableSpace alpha] [MeasurableSpace beta]
    (r : PMF alpha) (W V : alpha -> PMF beta) : ENNReal :=
  InformationTheory.klDiv
    (PMF.channelJoint r W).toMeasure
    (PMF.channelJoint r V).toMeasure

/-! ## Elementary API -/

/-- Conditional relative entropy from a channel to itself is zero. -/
@[simp] theorem conditionalKlDiv_self
    {alpha : Type u} {beta : Type v}
    [MeasurableSpace alpha] [MeasurableSpace beta]
    (r : PMF alpha) (W : alpha -> PMF beta) :
    conditionalKlDiv r W W = 0 := by
  rw [conditionalKlDiv, InformationTheory.klDiv_self]

/-! ## Finite weighted-fiber semantics -/

private theorem channelJoint_support_subset_iff_active
    {alpha : Type u} {beta : Type v}
    (r : PMF alpha) (W V : alpha -> PMF beta) :
    (PMF.channelJoint r W).support ⊆
        (PMF.channelJoint r V).support ↔
      ∀ x, r x ≠ 0 -> (W x).support ⊆ (V x).support := by
  constructor
  · intro h x hx y hy
    have hr : x ∈ r.support := (r.mem_support_iff x).2 hx
    have hxy :
        (x, y) ∈ (PMF.channelJoint r W).support :=
      (PMF.mem_support_channelJoint_iff r W x y).2 ⟨hr, hy⟩
    exact
      ((PMF.mem_support_channelJoint_iff r V x y).1 (h hxy)).2
  · rintro h ⟨x, y⟩ hxy
    rw [PMF.mem_support_channelJoint_iff] at hxy ⊢
    exact
      ⟨hxy.1, h x ((r.mem_support_iff x).1 hxy.1) hxy.2⟩

private theorem weighted_klDiv_ne_top_of_active_support
    {alpha : Type u} {beta : Type v}
    [Finite beta]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (r : PMF alpha) (W V : alpha -> PMF beta)
    (hsupport : ∀ x, r x ≠ 0 -> (W x).support ⊆ (V x).support)
    (x : alpha) :
    r x *
        InformationTheory.klDiv
          (W x).toMeasure (V x).toMeasure ≠ ⊤ := by
  classical
  let := Fintype.ofFinite beta
  by_cases hx : r x = 0
  · simp [hx]
  · exact
      ENNReal.mul_ne_top (r.apply_ne_top x)
        ((klDiv_pmf_ne_top_iff_support_subset (W x) (V x)).2
          (hsupport x hx))

/--
Conditional relative entropy is the base-law-weighted sum of the fiberwise KL
divergences.

This identity is unconditional in `ENNReal`. An infinite KL value on a null
base fiber contributes `0 * ⊤ = 0`, while an infinite KL value on an active
fiber makes both sides `⊤`.
-/
theorem conditionalKlDiv_eq_sum
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (r : PMF alpha) (W V : alpha -> PMF beta) :
    conditionalKlDiv r W V =
      ∑ x, r x *
        InformationTheory.klDiv (W x).toMeasure (V x).toMeasure := by
  classical
  let := Fintype.ofFinite beta
  by_cases hactive :
      ∀ x, r x ≠ 0 -> (W x).support ⊆ (V x).support
  · have hjointSupport :
        (PMF.channelJoint r W).support ⊆
          (PMF.channelJoint r V).support :=
      (channelJoint_support_subset_iff_active r W V).2 hactive
    have hjointFinite :
        conditionalKlDiv r W V ≠ ⊤ := by
      apply
        (klDiv_pmf_ne_top_iff_support_subset
          (PMF.channelJoint r W) (PMF.channelJoint r V)).2
      exact hjointSupport
    have htermFinite (x : alpha) :
        r x *
            InformationTheory.klDiv
              (W x).toMeasure (V x).toMeasure ≠ ⊤ := by
      exact weighted_klDiv_ne_top_of_active_support r W V hactive x
    have hsumFinite :
        (∑ x, r x *
          InformationTheory.klDiv
            (W x).toMeasure (V x).toMeasure) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun x _ => htermFinite x
    apply
      (ENNReal.toReal_eq_toReal_iff'
        hjointFinite hsumFinite).mp
    have hjointAC :
        (PMF.channelJoint r W).toMeasure ≪
          (PMF.channelJoint r V).toMeasure :=
      (toMeasure_absolutelyContinuous_iff_support_subset
        (PMF.channelJoint r W) (PMF.channelJoint r V)).2
          hjointSupport
    rw [conditionalKlDiv]
    rw [toReal_klDiv_pmf_eq_sum
      (PMF.channelJoint r W) (PMF.channelJoint r V) hjointAC]
    rw [ENNReal.toReal_sum]
    · simp only [ENNReal.toReal_mul]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : r x = 0
      · simp [PMF.channelJoint_apply, hx]
      · have hcomponentAC :
            (W x).toMeasure ≪ (V x).toMeasure :=
          (toMeasure_absolutelyContinuous_iff_support_subset
            (W x) (V x)).2 (hactive x hx)
        rw [toReal_klDiv_pmf_eq_sum (W x) (V x) hcomponentAC]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _hy
        rw [PMF.channelJoint_apply, PMF.channelJoint_apply]
        have hxReal : (r x).toReal ≠ 0 :=
          ENNReal.toReal_ne_zero.mpr ⟨hx, r.apply_ne_top x⟩
        simp only [ENNReal.toReal_mul, ENNReal.toReal_div]
        rw [mul_div_mul_left _ _ hxReal]
        ring
    · intro x _hx
      exact htermFinite x
  · have hjointNotSupport :
        ¬ (PMF.channelJoint r W).support ⊆
          (PMF.channelJoint r V).support := by
      intro h
      exact hactive ((channelJoint_support_subset_iff_active r W V).1 h)
    have hjointTop :
        conditionalKlDiv r W V = ⊤ := by
      exact
        (klDiv_pmf_eq_top_iff_not_support_subset
          (PMF.channelJoint r W) (PMF.channelJoint r V)).2
            hjointNotSupport
    push Not at hactive
    rcases hactive with ⟨x, hx, hsupport⟩
    have hcomponentTop :
        InformationTheory.klDiv
            (W x).toMeasure (V x).toMeasure = ⊤ :=
      (klDiv_pmf_eq_top_iff_not_support_subset (W x) (V x)).2
        hsupport
    have htermTop :
        r x *
            InformationTheory.klDiv
              (W x).toMeasure (V x).toMeasure = ⊤ := by
      rw [hcomponentTop, ENNReal.mul_top hx]
    have hsumTop :
        (∑ x, r x *
          InformationTheory.klDiv
            (W x).toMeasure (V x).toMeasure) = ⊤ := by
      rw [ENNReal.sum_eq_top]
      exact ⟨x, Finset.mem_univ x, htermTop⟩
    calc
      conditionalKlDiv r W V = ⊤ := hjointTop
      _ = ∑ x, r x *
          InformationTheory.klDiv
            (W x).toMeasure (V x).toMeasure := hsumTop.symm

/-! ## Real-valued weighted semantics -/

/--
Real-valued weighted-fiber formula for conditional relative entropy under
support inclusion on the active base atoms:

`D(W || V | r) = ∑ x, r(x) D(W_x || V_x)`.

No support condition is imposed when `r x = 0`. In particular, an infinite
fiber KL divergence on a null base atom contributes zero to the canonical
`ENNReal` weighted sum before conversion to `Real`.
-/
theorem toReal_conditionalKlDiv_eq_sum
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (r : PMF alpha) (W V : alpha -> PMF beta)
    (hsupport :
      ∀ x ∈ r.support, (W x).support ⊆ (V x).support) :
    (conditionalKlDiv r W V).toReal =
      ∑ x, (r x).toReal *
        (InformationTheory.klDiv
          (W x).toMeasure (V x).toMeasure).toReal := by
  classical
  have hactive :
      ∀ x, r x ≠ 0 -> (W x).support ⊆ (V x).support := by
    intro x hx
    exact hsupport x ((r.mem_support_iff x).2 hx)
  have htermFinite (x : alpha) :
      r x *
          InformationTheory.klDiv
            (W x).toMeasure (V x).toMeasure ≠ ⊤ := by
    exact weighted_klDiv_ne_top_of_active_support r W V hactive x
  rw [conditionalKlDiv_eq_sum]
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro x _hx
    exact htermFinite x

/-! ## Finite joint KL chain rule -/

/--
KL chain rule for two finite channel-joint laws:

`D(P_X P_{Y|X} || Q_X Q_{Y|X}) =
  D(P_X || Q_X) + D(P_{Y|X} || Q_{Y|X} | P_X)`.

The conditional term is weighted by the numerator base law `p`. The identity
is unconditional in `ENNReal`, including when either summand is `⊤`.
-/
theorem klDiv_channelJoint_eq_add_conditionalKlDiv
    {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (W V : alpha -> PMF beta) :
    InformationTheory.klDiv
        (PMF.channelJoint p W).toMeasure
        (PMF.channelJoint q V).toMeasure =
      InformationTheory.klDiv p.toMeasure q.toMeasure +
        conditionalKlDiv p W V := by
  classical
  let := Fintype.ofFinite alpha
  let := Fintype.ofFinite beta
  simpa only [conditionalKlDiv, channelJoint_toMeasure] using
    (InformationTheory.klDiv_compProd_eq_add
      p.toMeasure q.toMeasure
      (pmfChannelKernel W) (pmfChannelKernel V))

/--
Real-valued finite joint KL chain rule under support inclusion for the base
laws and for every active numerator fiber:

`D(P_X P_{Y|X} || Q_X Q_{Y|X}) =
  D(P_X || Q_X) + D(P_{Y|X} || Q_{Y|X} | P_X)`.

The fiber condition is required only on `p.support`; an infinite fiber KL
divergence at a null numerator atom does not affect the identity.
-/
theorem toReal_klDiv_channelJoint_eq_add_conditionalKlDiv
    {alpha : Type u} {beta : Type v}
    [Finite alpha] [Finite beta]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    [MeasurableSpace beta] [MeasurableSingletonClass beta]
    (p q : PMF alpha) (W V : alpha -> PMF beta)
    (hbase : p.support ⊆ q.support)
    (hfiber :
      ∀ x ∈ p.support, (W x).support ⊆ (V x).support) :
    (InformationTheory.klDiv
      (PMF.channelJoint p W).toMeasure
      (PMF.channelJoint q V).toMeasure).toReal =
        (InformationTheory.klDiv
          p.toMeasure q.toMeasure).toReal +
          (conditionalKlDiv p W V).toReal := by
  have hbaseFinite :
      InformationTheory.klDiv p.toMeasure q.toMeasure ≠ ⊤ :=
    (klDiv_pmf_ne_top_iff_support_subset p q).2 hbase
  have hconditionalFinite :
      conditionalKlDiv p W V ≠ ⊤ := by
    apply
      (klDiv_pmf_ne_top_iff_support_subset
        (PMF.channelJoint p W) (PMF.channelJoint p V)).2
    apply (channelJoint_support_subset_iff_active p W V).2
    intro x hx
    exact hfiber x ((p.mem_support_iff x).2 hx)
  rw [klDiv_channelJoint_eq_add_conditionalKlDiv]
  exact ENNReal.toReal_add hbaseFinite hconditionalFinite

end

end Shannon
end LeanInfoTheory
