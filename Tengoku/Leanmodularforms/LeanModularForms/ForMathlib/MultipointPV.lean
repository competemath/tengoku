/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.CauchyPrincipalValue

/-!
# Multi-Point Cauchy Principal Value Infrastructure

Algebraic lemmas for multi-point Cauchy principal values and minimum separation
of finite sets. These are the building blocks for the generalized residue theorem.

## Main results

### Finite set separation

* `finset_discrete_min_sep` -- positive minimum separation in a finite set of distinct
  complex numbers.
* `finset_discrete_min_sep'` -- variant with `S.card > 1` hypothesis.
* `disjoint_balls_of_small_epsilon` -- disjoint balls for sufficiently small epsilon.

### Algebraic operations on `cpvIntegrandOn`

* `cpvIntegrandOn_sub` -- pointwise subtraction of CPV integrands
* `cpvIntegrandOn_add` -- pointwise addition of CPV integrands
* `cpvIntegrandOn_neg` -- pointwise negation of CPV integrands

### Algebraic operations on `HasCauchyPVOn`

* `HasCauchyPVOn.sub` -- subtraction of multi-point CPV limits
* `HasCauchyPVOn.add` -- addition of multi-point CPV limits
* `hasCauchyPVOn_of_tendsto_sub` -- transfer via vanishing difference

### Connection between single-point and multi-point CPV

* `hasCauchyPVOn_singleton_of_hasCauchyPV` -- single-point to multi-point
* `hasCauchyPV_of_hasCauchyPVOn_singleton` -- multi-point (singleton) to single-point

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set Filter Topology MeasureTheory Complex
open scoped Interval

noncomputable section

variable {x y : ℂ}

/-- The multi-point CPV integrand distributes over subtraction pointwise.
@isnad1 id=eq.0h6v.s5.071484326d11 from=translated src=- shape=03b2f40b vocab=5f9b2190
-/
theorem cpvIntegrandOn_sub (S : Finset ℂ) (f g : ℂ → ℂ) (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    cpvIntegrandOn S (fun z => f z - g z) γ ε t =
      cpvIntegrandOn S f γ ε t - cpvIntegrandOn S g γ ε t := by
  simp only [cpvIntegrandOn]
  split_ifs <;> ring

/-- The multi-point CPV integrand distributes over addition pointwise.
@isnad1 id=eq.0h6v.s5.d733ba091aab from=translated src=- shape=03b2f40b vocab=f60ed58e
-/
theorem cpvIntegrandOn_add (S : Finset ℂ) (f g : ℂ → ℂ) (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    cpvIntegrandOn S (fun z => f z + g z) γ ε t =
      cpvIntegrandOn S f γ ε t + cpvIntegrandOn S g γ ε t := by
  simp only [cpvIntegrandOn]
  split_ifs <;> ring

/-- Subtraction of multi-point CPV limits: if `HasCauchyPVOn S f γ L₁` and
`HasCauchyPVOn S g γ L₂`, then `HasCauchyPVOn S (f - g) γ (L₁ - L₂)`.

The integrability hypotheses are needed to split the integral of the difference
into a difference of integrals.
@isnad1 id=hascauch.4h8v.s8.b8a9c115e9d9 from=translated src=- shape=5cdda31b vocab=78ca8329
-/
theorem HasCauchyPVOn.sub {S : Finset ℂ} {f g : ℂ → ℂ}
    {γ : PiecewiseC1Path x y} {L₁ L₂ : ℂ}
    (hf : HasCauchyPVOn S f γ L₁) (hg : HasCauchyPVOn S g γ L₂)
    (hfi : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1)
    (hgi : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S g γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S (fun z => f z - g z) γ (L₁ - L₂) := by
  simp only [HasCauchyPVOn] at hf hg ⊢
  have heq : (fun ε => ∫ t in (0 : ℝ)..1,
      cpvIntegrandOn S (fun z => f z - g z) γ.toPath.extend ε t) =ᶠ[𝓝[>] 0]
      (fun ε => (∫ t in (0 : ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t) -
        (∫ t in (0 : ℝ)..1, cpvIntegrandOn S g γ.toPath.extend ε t)) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [← intervalIntegral.integral_sub (hfi ε hε) (hgi ε hε)]
    exact intervalIntegral.integral_congr
      (fun t _ => cpvIntegrandOn_sub S f g γ.toPath.extend ε t)
  exact (hf.sub hg).congr' heq.symm

/-- Addition of multi-point CPV limits: if `HasCauchyPVOn S f γ L₁` and
`HasCauchyPVOn S g γ L₂`, then `HasCauchyPVOn S (f + g) γ (L₁ + L₂)`.
@isnad1 id=hascauch.4h8v.s8.881d1cf334e0 from=translated src=- shape=5cdda31b vocab=0cf46d76
-/
theorem HasCauchyPVOn.add {S : Finset ℂ} {f g : ℂ → ℂ}
    {γ : PiecewiseC1Path x y} {L₁ L₂ : ℂ}
    (hf : HasCauchyPVOn S f γ L₁) (hg : HasCauchyPVOn S g γ L₂)
    (hfi : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1)
    (hgi : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S g γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S (fun z => f z + g z) γ (L₁ + L₂) := by
  simp only [HasCauchyPVOn] at hf hg ⊢
  have heq : (fun ε => ∫ t in (0 : ℝ)..1,
      cpvIntegrandOn S (fun z => f z + g z) γ.toPath.extend ε t) =ᶠ[𝓝[>] 0]
      (fun ε => (∫ t in (0 : ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t) +
        (∫ t in (0 : ℝ)..1, cpvIntegrandOn S g γ.toPath.extend ε t)) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [← intervalIntegral.integral_add (hfi ε hε) (hgi ε hε)]
    exact intervalIntegral.integral_congr
      (fun t _ => cpvIntegrandOn_add S f g γ.toPath.extend ε t)
  exact (hf.add hg).congr' heq.symm

/-- A `HasCauchyPVOn` for a singleton set implies `HasCauchyPV` at that point.
@isnad1 id=hascauch.1h6v.s5.574942655758 from=translated src=- shape=ce7a0c29 vocab=befe9553
-/
theorem hasCauchyPV_of_hasCauchyPVOn_singleton {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x y} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVOn {z₀} f γ L) : HasCauchyPV f γ z₀ L := by
  simp only [HasCauchyPV, HasCauchyPVOn] at h ⊢
  exact h.congr fun ε => intervalIntegral.integral_congr fun t _ =>
    cpvIntegrand_eq_cpvIntegrandOn_singleton.symm

/-- The multi-point CPV of the zero function is zero.
@isnad1 id=hascauch.0h4v.s5.974d0310fe86 from=translated src=- shape=a3d9e2af vocab=b9f4eb38
-/
theorem HasCauchyPVOn.zero_fun {S : Finset ℂ} {γ : PiecewiseC1Path x y} :
    HasCauchyPVOn S (fun _ => (0 : ℂ)) γ 0 := by
  simp only [HasCauchyPVOn]
  refine Tendsto.congr (f₁ := fun _ => (0 : ℂ)) (fun ε => ?_) tendsto_const_nhds
  rw [← intervalIntegral.integral_zero (a := (0 : ℝ)) (b := 1) (μ := volume) (E := ℂ)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [cpvIntegrandOn]
  split_ifs <;> simp

/-- Finite sum of `HasCauchyPVOn`: if each `f i` has multi-point CPV `L i` along `γ`
on `S` (with cutoff integrability), the sum `∑ i ∈ T, f i` has CPV `∑ i ∈ T, L i`.
@isnad1 id=hascauch.2h8v.s7.f840ed3ce5f1 from=translated src=- shape=3902a072 vocab=440aead5
-/
theorem HasCauchyPVOn.finset_sum {ι : Type*} [DecidableEq ι] (T : Finset ι)
    {S : Finset ℂ} {γ : PiecewiseC1Path x y} {f : ι → ℂ → ℂ} {L : ι → ℂ}
    (hf : ∀ i ∈ T, HasCauchyPVOn S (f i) γ (L i))
    (hfi : ∀ i ∈ T, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (f i) γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S (fun z => ∑ i ∈ T, f i z) γ (∑ i ∈ T, L i) := by
  induction T using Finset.induction_on with
  | empty =>
    simpa [Finset.sum_empty] using HasCauchyPVOn.zero_fun (S := S) (γ := γ)
  | @insert a T' hia ih =>
    have h_T'_int : ∀ ε > 0, IntervalIntegrable
        (fun t => cpvIntegrandOn S (fun z => ∑ i ∈ T', f i z) γ.toPath.extend ε t)
        volume 0 1 := fun ε hε => by
      refine (IntervalIntegrable.sum T'
        (f := fun i t => cpvIntegrandOn S (f i) γ.toPath.extend ε t)
        (fun i hi => hfi i (Finset.mem_insert_of_mem hi) ε hε)).congr fun t _ => ?_
      simp only [Finset.sum_apply, cpvIntegrandOn]
      split_ifs with h
      · exact Finset.sum_const_zero
      · rw [Finset.sum_mul]
    simp_rw [Finset.sum_insert hia]
    refine HasCauchyPVOn.add (hf a (Finset.mem_insert_self a T'))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hfi i (Finset.mem_insert_of_mem hi)))
      (hfi a (Finset.mem_insert_self a T')) h_T'_int

end
