/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.FiniteChaining
import Tengoku.Seed.Probability.IdentDistribIndep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite empirical-process symmetrization

This file provides the finite, measure-theoretically explicit core of three
standard empirical-process arguments.

* A ghost-sample reduction is proved first as a deterministic inclusion of
  events, then as an inequality for a product measure.  If the ghost process
  is uniformly small with probability at least `p`, a large deviation of the
  original process is reduced to a paired-difference deviation with the exact
  factor `1 / p`.
* Independent symmetric variables are invariant in law, after summation,
  under every fixed choice of signs.  A second formulation transports an
  arbitrary coordinatewise distributional invariance through independent
  finite sums; this is the reusable law-level interface for random signs.
* Centred Rademacher signs are formalized directly.  Hoeffding's lemma gives
  proxy `1`, hence a weighted independent Rademacher sum has proxy equal to
  the sum of squared coefficients.  A finite union bound then controls the
  maximum over a finite class.

The file deliberately makes no claim about infinite or non-separable
function classes.  It also does not hide the conditional step in the usual
random-sign argument: when random signs and data live on the same space, the
coordinatewise law invariance and independence across coordinates are stated
explicitly.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega Omega' T ι : Type*}
  [MeasurableSpace Omega] [MeasurableSpace Omega']
  {mu : Measure Omega} {nu : Measure Omega'}

/-! ## Finite deviation events and the ghost-sample reduction -/

/-- The event that a real process exceeds `r` in absolute value at one of the
points of a finite class `N`.  Using an existential event avoids any need to
choose or separately prove measurability of a supremum.-/
def finiteSupAbsEvent (X : Omega → T → ℝ) (N : Finset T) (r : ℝ) : Set Omega :=
  ⋃ t ∈ N, {omega | r < |X omega t|}

omit [MeasurableSpace Omega] in
@[simp]
theorem mem_finiteSupAbsEvent {X : Omega → T → ℝ} {N : Finset T}
    {r : ℝ} {omega : Omega} :
    omega ∈ finiteSupAbsEvent X N r ↔ ∃ t ∈ N, r < |X omega t| := by
  simp [finiteSupAbsEvent]

/-- The event that a process is bounded by `r`, simultaneously over a finite
class.  It is defined as the complement of the corresponding strict upper
event so that its measurability follows immediately.-/
def finiteUniformAbsLeEvent (X : Omega → T → ℝ) (N : Finset T) (r : ℝ) : Set Omega :=
  (finiteSupAbsEvent X N r)ᶜ

omit [MeasurableSpace Omega] in
@[simp]
theorem mem_finiteUniformAbsLeEvent {X : Omega → T → ℝ} {N : Finset T}
    {r : ℝ} {omega : Omega} :
    omega ∈ finiteUniformAbsLeEvent X N r ↔
      ∀ t ∈ N, |X omega t| ≤ r := by
  simp [finiteUniformAbsLeEvent, not_lt]

/-- The paired event used in ghost-sample symmetrization.-/
def finitePairedDifferenceEvent (X : Omega → T → ℝ)
    (Y : Omega' → T → ℝ) (N : Finset T) (r : ℝ) : Set (Omega × Omega') :=
  finiteSupAbsEvent (fun z t ↦ X z.1 t - Y z.2 t) N r

omit [MeasurableSpace Omega] [MeasurableSpace Omega'] in
@[simp]
theorem mem_finitePairedDifferenceEvent
    {X : Omega → T → ℝ} {Y : Omega' → T → ℝ}
    {N : Finset T} {r : ℝ} {z : Omega × Omega'} :
    z ∈ finitePairedDifferenceEvent X Y N r ↔
      ∃ t ∈ N, r < |X z.1 t - Y z.2 t| := by
  simp [finitePairedDifferenceEvent]

/-- Measurability of a finite upper event from coordinatewise measurability on
the finite class.-/
theorem measurableSet_finiteSupAbsEvent
    {X : Omega → T → ℝ} {N : Finset T} {r : ℝ}
    (hX : ∀ t ∈ N, Measurable (fun omega ↦ X omega t)) :
    MeasurableSet (finiteSupAbsEvent X N r) := by
  classical
  apply MeasurableSet.biUnion N.countable_toSet
  intro t ht
  exact measurableSet_lt measurable_const (hX t (by simpa using ht)).abs

/-- Measurability of the uniform-good ghost event.-/
theorem measurableSet_finiteUniformAbsLeEvent
    {X : Omega → T → ℝ} {N : Finset T} {r : ℝ}
    (hX : ∀ t ∈ N, Measurable (fun omega ↦ X omega t)) :
    MeasurableSet (finiteUniformAbsLeEvent X N r) :=
  (measurableSet_finiteSupAbsEvent hX).compl

/-- Measurability of the paired-difference event.-/
theorem measurableSet_finitePairedDifferenceEvent
    {X : Omega → T → ℝ} {Y : Omega' → T → ℝ}
    {N : Finset T} {r : ℝ}
    (hX : ∀ t ∈ N, Measurable (fun omega ↦ X omega t))
    (hY : ∀ t ∈ N, Measurable (fun omega ↦ Y omega t)) :
    MeasurableSet (finitePairedDifferenceEvent X Y N r) := by
  apply measurableSet_finiteSupAbsEvent
  intro t ht
  exact ((hX t ht).comp measurable_fst).sub ((hY t ht).comp measurable_snd)

omit [MeasurableSpace Omega] [MeasurableSpace Omega'] in
/-- Deterministic ghost-sample implication.  If `X` is larger than `2r` at
one index and `Y` is at most `r` at every index, their difference is larger
than `r` at the same index.-/
theorem finiteSupAbsEvent_prod_finiteUniformAbsLeEvent_subset
    (X : Omega → T → ℝ) (Y : Omega' → T → ℝ)
    (N : Finset T) {r : ℝ} :
    finiteSupAbsEvent X N (2 * r) ×ˢ finiteUniformAbsLeEvent Y N r ⊆
      finitePairedDifferenceEvent X Y N r := by
  intro z hz
  obtain ⟨hx, hy⟩ := hz
  obtain ⟨t, htN, ht⟩ := mem_finiteSupAbsEvent.1 hx
  have hy_t : |Y z.2 t| ≤ r :=
    (mem_finiteUniformAbsLeEvent.1 hy) t htN
  apply mem_finitePairedDifferenceEvent.2
  refine ⟨t, htN, ?_⟩
  have hreverse : |X z.1 t| - |Y z.2 t| ≤ |X z.1 t - Y z.2 t| :=
    abs_sub_abs_le_abs_sub _ _
  linarith

/-- Product-measure form of the exact ghost-sample reduction.  No identical
distribution or independence hypothesis is needed here: the two samples
already live under the product measure `mu.prod nu`.-/
theorem measureReal_mul_finiteUniformAbsLeEvent_le_pairedDifference
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (X : Omega → T → ℝ) (Y : Omega' → T → ℝ)
    (N : Finset T) {r : ℝ} :
    mu.real (finiteSupAbsEvent X N (2 * r)) *
        nu.real (finiteUniformAbsLeEvent Y N r) ≤
      (mu.prod nu).real (finitePairedDifferenceEvent X Y N r) := by
  rw [← measureReal_prod_prod]
  exact measureReal_mono
    (finiteSupAbsEvent_prod_finiteUniformAbsLeEvent_subset X Y N)

/-- Quantitative ghost-sample reduction.  If the uniform-good ghost event has
probability at least `p > 0` and the paired-difference event has probability
at most `delta`, then the original `2r` event has probability at most
`delta / p`.-/
theorem measureReal_finiteSupAbsEvent_le_of_ghost
    [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (X : Omega → T → ℝ) (Y : Omega' → T → ℝ)
    (N : Finset T) {r p delta : ℝ}
    (hp : 0 < p)
    (hgood : p ≤ nu.real (finiteUniformAbsLeEvent Y N r))
    (hpair : (mu.prod nu).real (finitePairedDifferenceEvent X Y N r) ≤ delta) :
    mu.real (finiteSupAbsEvent X N (2 * r)) ≤ delta / p := by
  apply (le_div_iff₀ hp).2
  calc
    mu.real (finiteSupAbsEvent X N (2 * r)) * p ≤
        mu.real (finiteSupAbsEvent X N (2 * r)) *
          nu.real (finiteUniformAbsLeEvent Y N r) :=
      mul_le_mul_of_nonneg_left hgood measureReal_nonneg
    _ ≤ (mu.prod nu).real (finitePairedDifferenceEvent X Y N r) :=
      measureReal_mul_finiteUniformAbsLeEvent_le_pairedDifference X Y N
    _ ≤ delta := hpair

/-- The unnormalised empirical sum of a finite family of processes.-/
def finiteEmpiricalSum (X : ι → Omega → T → ℝ)
    (s : Finset ι) (omega : Omega) (t : T) : ℝ :=
  ∑ i ∈ s, X i omega t

omit [MeasurableSpace Omega] [MeasurableSpace Omega'] in
/-- A paired empirical difference is the sum of the coordinatewise ghost
differences.-/
theorem finiteEmpiricalSum_sub_finiteEmpiricalSum
    (X : ι → Omega → T → ℝ) (Y : ι → Omega' → T → ℝ)
    (s : Finset ι) (omega : Omega) (omega' : Omega') (t : T) :
    finiteEmpiricalSum X s omega t - finiteEmpiricalSum Y s omega' t =
      ∑ i ∈ s, (X i omega t - Y i omega' t) := by
  simp only [finiteEmpiricalSum, Finset.sum_sub_distrib]

/-! ## Symmetric laws and sign invariance -/

/-- A real random variable has a symmetric law when it is identically
distributed with its negative.-/
def HasSymmetricLaw (X : Omega → ℝ) (mu : Measure Omega := by volume_tac) : Prop :=
  IdentDistrib X (-X) mu mu

/-- A difference of two copies of the same measurable variable on the product
space has a symmetric law.  This is the elementary exchangeability step in
ghost-sample symmetrization.-/
theorem hasSymmetricLaw_ghostDifference [IsProbabilityMeasure mu]
    {X : Omega → ℝ} (hX : Measurable X) :
    HasSymmetricLaw (fun z : Omega × Omega ↦ X z.1 - X z.2) (mu.prod mu) := by
  let D : Omega × Omega → ℝ := fun z ↦ X z.1 - X z.2
  have hD : Measurable D :=
    (hX.comp measurable_fst).sub (hX.comp measurable_snd)
  refine {
    aemeasurable_fst := hD.aemeasurable
    aemeasurable_snd := hD.neg.aemeasurable
    map_eq := ?_ }
  calc
    Measure.map D (mu.prod mu) =
        Measure.map D (Measure.map Prod.swap (mu.prod mu)) := by
      rw [Measure.prod_swap]
    _ = Measure.map (D ∘ Prod.swap) (mu.prod mu) := by
      rw [Measure.map_map hD measurable_swap]
    _ = Measure.map (-D) (mu.prod mu) := by
      apply Measure.map_congr
      filter_upwards [] with z
      simp [D]

/-- Coordinatewise identical laws and independence on both spaces transport
through a finite sum.  Taking `Y i = epsilon i * D i` is the exact abstract
interface for random-sign symmetrization: the caller must verify both the
coordinatewise sign invariance and independence of the signed coordinates.-/
theorem identDistrib_finset_sum_of_independent_coordinates
    [Countable ι]
    (X : ι → Omega → ℝ) (Y : ι → Omega' → ℝ)
    (hXY : ∀ i, IdentDistrib (X i) (Y i) mu nu)
    (hX_indep : iIndepFun X mu) (hY_indep : iIndepFun Y nu)
    (s : Finset ι) :
    IdentDistrib (fun omega ↦ ∑ i ∈ s, X i omega)
      (fun omega ↦ ∑ i ∈ s, Y i omega) mu nu := by
  have hpi := IdentDistrib.pi hXY hX_indep hY_indep
  have hsum : Measurable (fun x : ι → ℝ ↦ ∑ i ∈ s, x i) := by
    fun_prop
  simpa [Function.comp_def] using hpi.comp hsum

/-- An independent family of symmetric variables is invariant in law, after
finite summation, under every deterministic choice of signs `+1` or `-1`.
This is the exact fixed-sign form of the Rademacher symmetrization principle.-/
theorem identDistrib_finset_sum_sign_mul_of_independent_symmetric
    [Countable ι]
    (X : ι → Omega → ℝ) (hX_indep : iIndepFun X mu)
    (hX_symm : ∀ i, HasSymmetricLaw (X i) mu)
    (sign : ι → ℝ) (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (s : Finset ι) :
    IdentDistrib (fun omega ↦ ∑ i ∈ s, X i omega)
      (fun omega ↦ ∑ i ∈ s, sign i * X i omega) mu mu := by
  have hcoord : ∀ i,
      IdentDistrib (X i) (fun omega ↦ sign i * X i omega) mu mu := by
    intro i
    rcases hsign i with hi | hi
    · rw [hi]
      simpa using IdentDistrib.refl (hX_symm i).aemeasurable_fst
    · rw [hi]
      simp only [neg_one_mul]
      change IdentDistrib (X i) (-X i) mu mu
      exact hX_symm i
  have hsigned_indep :
      iIndepFun (fun i omega ↦ sign i * X i omega) mu := by
    have hcomp := hX_indep.comp
      (fun i (x : ℝ) ↦ sign i * x)
      (fun _ ↦ measurable_const.mul measurable_id)
    simpa [Function.comp_def] using hcomp
  exact identDistrib_finset_sum_of_independent_coordinates
    X (fun i omega ↦ sign i * X i omega)
      hcoord hX_indep hsigned_indep s

/-- Symmetry in law of the joint restriction of a process to a finite class.
The codomain is the finite product `N → ℝ`, equipped with its product
measurable space.-/
def HasSymmetricFiniteLaw (X : Omega → T → ℝ) (N : Finset T)
    (mu : Measure Omega := by volume_tac) : Prop :=
  IdentDistrib (fun omega (t : N) ↦ X omega t)
    (fun omega (t : N) ↦ -X omega t) mu mu

/-- The joint finite-dimensional ghost difference has a symmetric law.  This
is the process-valued version of `hasSymmetricLaw_ghostDifference`; swapping
the two samples negates every coordinate simultaneously.-/
theorem hasSymmetricFiniteLaw_ghostDifference [IsProbabilityMeasure mu]
    (X : Omega → T → ℝ) (N : Finset T)
    (hX : ∀ t ∈ N, Measurable (fun omega ↦ X omega t)) :
    HasSymmetricFiniteLaw
      (fun z : Omega × Omega ↦ fun t ↦ X z.1 t - X z.2 t)
      N (mu.prod mu) := by
  let D : Omega × Omega → (N → ℝ) :=
    fun z t ↦ X z.1 t - X z.2 t
  have hD : Measurable D := by
    apply measurable_pi_lambda
    intro t
    exact ((hX t t.property).comp measurable_fst).sub
      ((hX t t.property).comp measurable_snd)
  change IdentDistrib D (-D) (mu.prod mu) (mu.prod mu)
  refine {
    aemeasurable_fst := hD.aemeasurable
    aemeasurable_snd := hD.neg.aemeasurable
    map_eq := ?_ }
  calc
    Measure.map D (mu.prod mu) =
        Measure.map D (Measure.map Prod.swap (mu.prod mu)) := by
      rw [Measure.prod_swap]
    _ = Measure.map (D ∘ Prod.swap) (mu.prod mu) := by
      rw [Measure.map_map hD measurable_swap]
    _ = Measure.map (-D) (mu.prod mu) := by
      apply Measure.map_congr
      filter_upwards [] with z
      funext t
      simp [D]

/-- Joint finite-process sign invariance.  If the process-valued coordinates
are independent and each whole finite restriction is symmetric, multiplying
each coordinate process by an arbitrary fixed sign preserves the law of the
entire summed restriction.  Consequently every measurable functional of the
finite vector, including its maximum absolute coordinate, has the same law.-/
theorem identDistrib_finiteProcessSum_sign_mul_of_independent_symmetric
    [Countable ι]
    (X : ι → Omega → T → ℝ) (N : Finset T)
    (hX_indep : iIndepFun
      (fun i omega (t : N) ↦ X i omega t) mu)
    (hX_symm : ∀ i, HasSymmetricFiniteLaw (X i) N mu)
    (sign : ι → ℝ) (hsign : ∀ i, sign i = 1 ∨ sign i = -1)
    (s : Finset ι) :
    IdentDistrib
      (fun omega (t : N) ↦ ∑ i ∈ s, X i omega t)
      (fun omega (t : N) ↦ ∑ i ∈ s, sign i * X i omega t)
      mu mu := by
  let V : ι → Omega → (N → ℝ) :=
    fun i omega t ↦ X i omega t
  let W : ι → Omega → (N → ℝ) :=
    fun i omega t ↦ sign i * X i omega t
  have hcoord : ∀ i, IdentDistrib (V i) (W i) mu mu := by
    intro i
    rcases hsign i with hi | hi
    · have hrefl := IdentDistrib.refl (hX_symm i).aemeasurable_fst
      simpa [V, W, hi] using hrefl
    · have hsymm := hX_symm i
      simpa [HasSymmetricFiniteLaw, V, W, hi] using hsymm
  have hW_indep : iIndepFun W mu := by
    have hcomp := hX_indep.comp
      (fun i (x : N → ℝ) t ↦ sign i * x t)
      (fun _ ↦ by fun_prop)
    simpa [V, W, Function.comp_def] using hcomp
  have hpi := IdentDistrib.pi hcoord (by simpa [V] using hX_indep) hW_indep
  have hsum : Measurable
      (fun x : ι → (N → ℝ) ↦ fun t ↦ ∑ i ∈ s, x i t) := by
    fun_prop
  simpa [V, W, Function.comp_def] using hpi.comp hsum

omit [MeasurableSpace Omega'] in
/-- Conditional form of finite-process random-sign symmetrization.  For every
realization of any sign process taking values in `{+1,-1}`, the signed sum has
the same joint finite-dimensional law as the unsigned sum.  No probability
law for the signs is needed for this conditional statement.-/
theorem identDistrib_finiteProcessSum_randomSigns_conditionally
    [Countable ι]
    (X : ι → Omega → T → ℝ) (N : Finset T)
    (hX_indep : iIndepFun
      (fun i omega (t : N) ↦ X i omega t) mu)
    (hX_symm : ∀ i, HasSymmetricFiniteLaw (X i) N mu)
    (epsilon : Omega' → ι → ℝ)
    (hepsilon : ∀ eta i, epsilon eta i = 1 ∨ epsilon eta i = -1)
    (s : Finset ι) (eta : Omega') :
    IdentDistrib
      (fun omega (t : N) ↦ ∑ i ∈ s, X i omega t)
      (fun omega (t : N) ↦ ∑ i ∈ s, epsilon eta i * X i omega t)
      mu mu :=
  identDistrib_finiteProcessSum_sign_mul_of_independent_symmetric
    X N hX_indep hX_symm (epsilon eta) (hepsilon eta) s

/-! ## Rademacher signs and finite-class sub-Gaussian bounds -/

/-- A centred Rademacher random variable: it is measurable, takes only the
values `+1` and `-1` almost surely, and has expectation zero.  On a
probability space these conditions characterize the usual equiprobable
Rademacher law.-/
structure IsRademacher (epsilon : Omega → ℝ)
    (mu : Measure Omega := by volume_tac) : Prop where
  aemeasurable : AEMeasurable epsilon mu
  ae_eq_one_or_neg_one : ∀ᵐ omega ∂mu, epsilon omega = 1 ∨ epsilon omega = -1
  integral_eq_zero : ∫ omega, epsilon omega ∂mu = 0

namespace IsRademacher

variable {epsilon : Omega → ℝ}

/-- A Rademacher variable lies in `[-1,1]` almost surely.-/
theorem ae_mem_Icc (h : IsRademacher epsilon mu) :
    ∀ᵐ omega ∂mu, epsilon omega ∈ Set.Icc (-1 : ℝ) 1 := by
  filter_upwards [h.ae_eq_one_or_neg_one] with omega homega
  rcases homega with homega | homega <;> simp [homega]

/-- Hoeffding's lemma gives the sharp variance proxy `1` for a centred
Rademacher sign.-/
theorem hasSubgaussianMGF [IsProbabilityMeasure mu]
    (h : IsRademacher epsilon mu) :
    HasSubgaussianMGF epsilon 1 mu := by
  convert hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    h.aemeasurable h.ae_mem_Icc h.integral_eq_zero using 1
  norm_num

end IsRademacher

/-- The nonnegative variance proxy contributed by a coefficient in a
Rademacher sum.-/
def rademacherSqProxy (a : ℝ) : ℝ≥0 := ⟨a ^ 2, sq_nonneg a⟩

/-- A finite maximum of (possibly dependent) sub-Gaussian variables obeys
the sum of their bilateral tails.  Dependence across the class `N` is not
restricted because this is a pure union bound.-/
theorem measureReal_finiteSupAbsEvent_le_of_subgaussian
    [IsProbabilityMeasure mu]
    (X : Omega → T → ℝ) (N : Finset T) (c : T → ℝ≥0)
    {r : ℝ} (hr : 0 ≤ r)
    (hX : ∀ t ∈ N, HasSubgaussianMGF (fun omega ↦ X omega t) (c t) mu) :
    mu.real (finiteSupAbsEvent X N r) ≤
      ∑ t ∈ N, 2 * exp (-r ^ 2 / (2 * (c t : ℝ))) := by
  calc
    mu.real (finiteSupAbsEvent X N r) ≤
        ∑ t ∈ N, mu.real {omega | r < |X omega t|} := by
      simpa only [finiteSupAbsEvent] using
        (measureReal_biUnion_finset_le (μ := mu) N
          (fun t ↦ {omega | r < |X omega t|}))
    _ ≤ ∑ t ∈ N, 2 * exp (-r ^ 2 / (2 * (c t : ℝ))) :=
      Finset.sum_le_sum fun t ht ↦ (hX t ht).measureReal_abs_gt_le hr

end ProbabilityTheory
