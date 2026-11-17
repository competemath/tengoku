/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ComplexAnalysis.LogDerivative
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.Definitions
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.Xi.FunctionalEquation
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.LogDerivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# HadamardProduct.EntireXi

Hadamard data tailored to the genuine entire Riemann ξ. These are the interface bundles
that feed the classical genus-one Hadamard factorization: the concrete nonzero zero system,
its canonical index type, the away-from-zeros log-derivative source, the exponential-affine
prefactor properties, and the locally-uniform-convergence log-derivative data restricted to
the entire-ξ nonzero locus. Identity content only.

## Main declarations

* `ConcreteEntireXiZeroSystem` — nonzero zero system for the genuine entire ξ.
* `EntireXiNonzeroZeroIndex` — the subtype of nonzero zeros of `entireRiemannXi`.
* `EntireXiLogDerivativeSourceAwayFromZeros` — away-from-zeros log-derivative source
  (was `EntireXiLogDerivativeSourceAFZ`).
* `EntireXiHadamardPrefactor` — prefactor away-from-zeros properties.
* `HadamardProductLUCOnEntireXiNonzeroData` — locally-uniform-convergence log-derivative
  data on the entire-ξ nonzero locus.
-/

open Topology

namespace OverflowResidueRH

/-- 📦 **`EntireXiLogDerivativeSourceAwayFromZeros`** — away-from-zeros log-derivative
source for the genuine entire ξ.-/
structure EntireXiLogDerivativeSourceAwayFromZeros : Type where
  xiZeroContribution : ℂ → ℂ
  differentiable_at :
    ∀ s : ℂ, entireRiemannXi s ≠ 0 → DifferentiableAt ℂ entireRiemannXi s
  xi_logDeriv_eq :
    ∀ s : ℂ, entireRiemannXi s ≠ 0 →
      logDerivativeResponse entireRiemannXi s = xiZeroContribution s

/-- 📦 **`ConcreteEntireXiZeroSystem`** — nonzero zero system for
the genuine entire ξ.-/
structure ConcreteEntireXiZeroSystem (ι : Type) : Type where
  zeroLoc : ι → ℂ
  zeroLoc_ne_zero : ∀ i : ι, zeroLoc i ≠ 0
  zeroLoc_is_zero : ∀ i : ι, entireRiemannXi (zeroLoc i) = 0
  all_nonzero_entireXi_zeros :
    ∀ s : ℂ, entireRiemannXi s = 0 → s ≠ 0 →
      ∃ i : ι, zeroLoc i = s

/-- **Subtype of nonzero zeros of `entireRiemannXi`.** This is the
canonical zero-index type for the genuine entire ξ Hadamard theorem.-/
def EntireXiNonzeroZeroIndex : Type :=
  { s : ℂ // entireRiemannXi s = 0 ∧ s ≠ 0 }

/-- 📦 **`EntireXiHadamardPrefactor`** — prefactor away-from-zeros properties.-/
structure EntireXiHadamardPrefactor (prefactor : ℂ → ℂ) : Prop where
  differentiable_at_nonzero :
    ∀ s : ℂ, entireRiemannXi s ≠ 0 → DifferentiableAt ℂ prefactor s
  nonzero_at_nonzero :
    ∀ s : ℂ, entireRiemannXi s ≠ 0 → prefactor s ≠ 0

/-- 📦 **`HadamardProductLUCOnEntireXiNonzeroData`** — locally-uniform-convergence
log-derivative data on the entire-ξ nonzero locus.-/
structure HadamardProductLUCOnEntireXiNonzeroData
    {ι : Type*} (zeroLoc : ι → ℂ) where
  locally_uniform_product :
    TendstoLocallyUniformlyOn
      (fun F : Finset ι => fun s : ℂ =>
        indexedFiniteHadamardProduct zeroLoc F s)
      (infiniteHadamardProduct zeroLoc)
      Filter.atTop
      {s : ℂ | entireRiemannXi s ≠ 0}
  infinite_differentiable_at :
    ∀ s : ℂ,
      entireRiemannXi s ≠ 0 →
      DifferentiableAt ℂ (infiniteHadamardProduct zeroLoc) s
  logDeriv_eq_tsum :
    ∀ s : ℂ,
      entireRiemannXi s ≠ 0 →
      logDerivativeResponse (infiniteHadamardProduct zeroLoc) s
        = hadamardRegularizedLogDerivSeries zeroLoc s

/-- 🌟🌟 **PROVED — convert nonzero-locus LUC data to the general
`HadamardProductLUCLogDerivData` interface.**-/
noncomputable def HadamardProductLUCOnEntireXiNonzeroData.toLUCLogDerivData
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardProductLUCOnEntireXiNonzeroData zeroLoc) :
    HadamardProductLUCLogDerivData zeroLoc :=
  { region := {s : ℂ | entireRiemannXi s ≠ 0}
    locally_uniform_product := H.locally_uniform_product
    infinite_differentiable_at := by
      intro s hs
      exact H.infinite_differentiable_at s hs
    logDeriv_eq_tsum := by
      intro s hs
      exact H.logDeriv_eq_tsum s hs }

/-- 📦 **`HadamardProductLUCOnXiNonzeroData`** — locally-uniform-convergence
log-derivative data on the completed-ξ nonzero locus.-/
structure HadamardProductLUCOnXiNonzeroData
    {ι : Type*} (zeroLoc : ι → ℂ) where
  locally_uniform_product :
    TendstoLocallyUniformlyOn
      (fun F : Finset ι => fun s : ℂ =>
        indexedFiniteHadamardProduct zeroLoc F s)
      (infiniteHadamardProduct zeroLoc)
      Filter.atTop
      {s : ℂ | completedXiFunction s ≠ 0}
  infinite_differentiable_at :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      DifferentiableAt ℂ (infiniteHadamardProduct zeroLoc) s
  logDeriv_eq_tsum :
    ∀ s : ℂ,
      completedXiFunction s ≠ 0 →
      logDerivativeResponse (infiniteHadamardProduct zeroLoc) s
        = hadamardRegularizedLogDerivSeries zeroLoc s

/-- ⭐ **PROVED — `s ≠ zeroLoc i` when `entireRiemannXi s ≠ 0`.**
@isnad1 id=ne.1h4v.s4.d90fc3f137d8 from=translated src=- shape=e8c40d2d vocab=dd546fd6
-/
theorem ConcreteEntireXiZeroSystem.nonzero_no_collision
    {ι : Type} (H : ConcreteEntireXiZeroSystem ι)
    {s : ℂ} (hs : entireRiemannXi s ≠ 0) :
    ∀ i : ι, s ≠ H.zeroLoc i := by
  intro i hsi
  apply hs
  rw [hsi]
  exact H.zeroLoc_is_zero i

/-- The canonical entire-ξ nonzero-zero location map.-/
def entireXiNonzeroZeroLoc (i : EntireXiNonzeroZeroIndex) : ℂ := i.1

/-- ⭐ **PROVED — `C·exp(a + b·s)` is a valid entire-ξ prefactor.**
@isnad1 id=entirexi.1h3v.s5.e35bd284475a from=translated src=- shape=dd51e875 vocab=669f2d0a
-/
theorem EntireXiHadamardPrefactor.exp_affine
    {C a b : ℂ} (hC : C ≠ 0) :
    EntireXiHadamardPrefactor
      (fun s : ℂ => C * Complex.exp (a + b * s)) := by
  refine
    { differentiable_at_nonzero := ?_
      nonzero_at_nonzero := ?_ }
  · intro s _hs
    have h_aff : DifferentiableAt ℂ (fun s : ℂ => a + b * s) s :=
      (differentiableAt_const _).add
        ((differentiableAt_const _).mul differentiableAt_fun_id)
    exact (differentiableAt_const _).mul h_aff.cexp
  · intro s _hs
    exact mul_ne_zero hC (Complex.exp_ne_zero _)

/-- 📦 **`EntireXiHadamardFactorization`** — the classical
factorization identity `ξ = prefactor · ∏ E₁(·/ρᵢ)` for entire ξ.-/
structure EntireXiHadamardFactorization
    {ι : Type}
    (HZ : ConcreteEntireXiZeroSystem ι) (prefactor : ℂ → ℂ) : Prop where
  factorization :
    ∀ s : ℂ,
      entireRiemannXi s
        = prefactor s * infiniteHadamardProduct HZ.zeroLoc s

/-- 📦 **`EntireXiZeroInvSqDistribution`** — RvM-style zero
distribution for entire ξ.-/
structure EntireXiZeroInvSqDistribution
    {ι : Type} (HZ : ConcreteEntireXiZeroSystem ι) : Prop where
  inv_sq_summable :
    Summable fun i : ι => (‖HZ.zeroLoc i‖ ^ 2)⁻¹
  eventually_large :
    ∀ s : ℂ,
      ∀ᶠ i in Filter.cofinite, 2 * ‖s‖ ≤ ‖HZ.zeroLoc i‖

/-- **Canonical entire-ξ away-from-zeros log-derivative source** — the
log-derivative of `entireRiemannXi` itself, valid everywhere since
`entireRiemannXi` is entire.-/
noncomputable def canonicalEntireXiLogDerivativeSourceAwayFromZeros :
    EntireXiLogDerivativeSourceAwayFromZeros :=
  { xiZeroContribution := logDerivativeResponse entireRiemannXi
    differentiable_at := fun s _hs => entireRiemannXi_differentiableAt s
    xi_logDeriv_eq := fun _s _hs => rfl }

/-- ⭐ **PROVED — convert to `HadamardZeroInvSqSummability`.**
@isnad1 id=hadamard.1h2v.s3.725061c5148f from=translated src=- shape=232020f7 vocab=d7329e2d
-/
theorem EntireXiZeroInvSqDistribution.toHadamardZeroInvSqSummability
    {ι : Type} {HZ : ConcreteEntireXiZeroSystem ι}
    (H : EntireXiZeroInvSqDistribution HZ) :
    HadamardZeroInvSqSummability HZ.zeroLoc :=
  { zero_ne := HZ.zeroLoc_ne_zero
    inv_sq_summable := H.inv_sq_summable
    eventually_large := H.eventually_large }

/-- 🌟🌟🌟 **PROVED — entire-ξ inverse-square zero distribution gives
nonvanishing of the genus-one product off the indexed zero set.**
@isnad1 id=ne.2h3v.s5.681ac24af7b3 from=translated src=- shape=782f7483 vocab=767deceb
-/
theorem EntireXiZeroInvSqDistribution.infiniteProduct_ne_zero
    {ι : Type} {HZ : ConcreteEntireXiZeroSystem ι}
    (H : EntireXiZeroInvSqDistribution HZ)
    {s : ℂ} (hs_ne : ∀ i : ι, s ≠ HZ.zeroLoc i) :
    infiniteHadamardProduct HZ.zeroLoc s ≠ 0 :=
  H.toHadamardZeroInvSqSummability.infiniteProduct_ne_zero hs_ne

/-- 📦 **`EntireXiClassicalHadamardTheorem`** — publication-level
Hadamard theorem for entire ξ.-/
structure EntireXiClassicalHadamardTheorem (ι : Type) : Type where
  zeroSystem : ConcreteEntireXiZeroSystem ι
  prefactor : ℂ → ℂ
  zeroDistribution : EntireXiZeroInvSqDistribution zeroSystem
  luc : HadamardProductLUCLogDerivData zeroSystem.zeroLoc
  region :
    ∀ s : ℂ, entireRiemannXi s ≠ 0 → s ∈ luc.region
  factorization :
    EntireXiHadamardFactorization zeroSystem prefactor
  prefactorData :
    EntireXiHadamardPrefactor prefactor

/-- ⭐ **PROVED — `entireRiemannXi 0 = 1/2`.**
This gives a concrete nonzero value, so the entire-ξ zero set is not
locally identically zero anywhere.
@isnad1 id=eq.0h0v.s5.ed365be5d99d from=translated src=- shape=d4f6e56f vocab=f528f7f1
-/
theorem entireRiemannXi_zero :
    entireRiemannXi 0 = (1 / 2 : ℂ) := by
  simp [entireRiemannXi]

/-- 🌟🌟🌟 **PROVED — canonical concrete entire-ξ zero system.**

This discharges the `ConcreteEntireXiZeroSystem` Hadamard input by
choosing the index type to be the subtype of nonzero zeros itself.
Unlike the raw `completedXiFunction` subtype, there is no zero-at-origin
hazard here because the `ConcreteEntireXiZeroSystem` surjectivity field
is already restricted to nonzero zeros.-/
def concreteEntireXiZeroSystem :
    ConcreteEntireXiZeroSystem EntireXiNonzeroZeroIndex :=
  { zeroLoc := entireXiNonzeroZeroLoc
    zeroLoc_ne_zero := by
      intro i
      exact i.2.2
    zeroLoc_is_zero := by
      intro i
      exact i.2.1
    all_nonzero_entireXi_zeros := by
      intro s hs hs0
      exact ⟨⟨s, ⟨hs, hs0⟩⟩, rfl⟩ }

/-- 🌟🌟 **PROVED — entire-ξ zero distribution from inverse-square
summability plus norm-properness of the concrete zero system.**
@isnad1 id=entirexi.2h2v.s5.c50637cc1797 from=translated src=- shape=355075f3 vocab=16202165
-/
theorem EntireXiZeroInvSqDistribution.of_invSqSummable_normProper
    {ι : Type} {HZ : ConcreteEntireXiZeroSystem ι}
    (hinv : Summable fun i : ι => (‖HZ.zeroLoc i‖ ^ 2)⁻¹)
    (Hproper : HadamardZeroNormProper HZ.zeroLoc) :
    EntireXiZeroInvSqDistribution HZ :=
  { inv_sq_summable := hinv
    eventually_large := Hproper.eventually_large }

/-- 📦 **`EntireXiHadamardQuotientFactorization`** — quotient-form
Hadamard factorization data.

This is closer to the classical proof: the product is known to vanish at
the indexed zeros, be nonzero off them, and the quotient
`entireRiemannXi / product` is identified with the prefactor away from
the zero set. The theorem below turns that punctured quotient statement
into the global product factorization.-/
structure EntireXiHadamardQuotientFactorization
    {ι : Type}
    (HZ : ConcreteEntireXiZeroSystem ι) (prefactor : ℂ → ℂ) : Prop where
  product_vanishes_at_zeroLoc :
    ∀ i : ι,
      infiniteHadamardProduct HZ.zeroLoc (HZ.zeroLoc i) = 0
  product_nonzero_off_zeroLoc :
    ∀ s : ℂ,
      (∀ i : ι, s ≠ HZ.zeroLoc i) →
        infiniteHadamardProduct HZ.zeroLoc s ≠ 0
  quotient_eq_prefactor :
    ∀ s : ℂ,
      (∀ i : ι, s ≠ HZ.zeroLoc i) →
        entireRiemannXi s / infiniteHadamardProduct HZ.zeroLoc s
          = prefactor s

/-- 📦 **Canonical entire-ξ zero norm-properness.** This is the
finite-in-bounded-disks form of the classical zero discreteness input for
Mathlib's `entireRiemannXi`.-/
abbrev EntireXiCanonicalZeroNormProper : Prop :=
  HadamardZeroNormProper concreteEntireXiZeroSystem.zeroLoc

/-- ⭐ **PROVED — `entireRiemannXi` is not locally identically zero.**

If it vanished on a neighborhood of any point, the identity theorem on
the connected plane would force it to vanish at `0`, contradicting
`entireRiemannXi_zero`.
@isnad1 id=not.0h1v.s5.a49303369339 from=translated src=- shape=8dd287b1 vocab=7a46e9c8
-/
theorem entireRiemannXi_not_eventuallyEq_zero (p : ℂ) :
    ¬ entireRiemannXi =ᶠ[𝓝 p] 0 := by
  intro hlocal
  have h_on : AnalyticOnNhd ℂ entireRiemannXi Set.univ :=
    fun z _hz => entireRiemannXi_differentiable.analyticAt z
  have heq : Set.EqOn entireRiemannXi 0 Set.univ :=
    h_on.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ
      (Set.mem_univ p)
      hlocal
  have hzero_at_zero : entireRiemannXi 0 = 0 :=
    heq (Set.mem_univ (0 : ℂ))
  norm_num [entireRiemannXi_zero] at hzero_at_zero

/-- 🌟 **PROVED — build nonzero-locus LUC data from a region-based
`HadamardProductLUCLogDerivData` whose region contains the entire-ξ
nonzero locus.**-/
noncomputable def HadamardProductLUCOnEntireXiNonzeroData.of_LUCLogDerivData
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardProductLUCLogDerivData zeroLoc)
    (hregion :
      ∀ s : ℂ, entireRiemannXi s ≠ 0 → s ∈ H.region) :
    HadamardProductLUCOnEntireXiNonzeroData zeroLoc := by
  refine
    { locally_uniform_product := ?_
      infinite_differentiable_at := ?_
      logDeriv_eq_tsum := ?_ }
  · exact H.locally_uniform_product.mono (fun s hs => hregion s hs)
  · intro s hs
    exact H.infinite_differentiable_at s (hregion s hs)
  · intro s hs
    exact H.logDeriv_eq_tsum s (hregion s hs)

/-- ⭐ **PROVED — zeros of `entireRiemannXi` are locally finite.**

At nonzeros, continuity gives a zero-free neighborhood. At zeros,
Mathlib's isolated-zero theorem gives a punctured neighborhood with no
other zeros, and nontriviality is supplied by
`entireRiemannXi_not_eventuallyEq_zero`.
@isnad1 id=ex.0h1v.s5.2de4855de0f6 from=translated src=- shape=a3dc674e vocab=07061042
-/
theorem entireRiemannXi_zeroSet_locallyFinite (p : ℂ) :
    ∃ U ∈ 𝓝 p, (U ∩ {s : ℂ | entireRiemannXi s = 0}).Finite := by
  by_cases hp : entireRiemannXi p = 0
  · have hAn : AnalyticAt ℂ entireRiemannXi p :=
      entireRiemannXi_differentiable.analyticAt p
    rcases hAn.eventually_eq_zero_or_eventually_ne_zero with hlocal | hpunct
    · exact absurd hlocal (entireRiemannXi_not_eventuallyEq_zero p)
    · rw [eventually_nhdsWithin_iff] at hpunct
      refine
        ⟨{z : ℂ | z ∈ ({p}ᶜ : Set ℂ) → entireRiemannXi z ≠ 0},
          hpunct, ?_⟩
      apply Set.Finite.subset (Set.finite_singleton p)
      rintro z ⟨hzU, hzzero⟩
      by_cases hzp : z = p
      · simp [hzp]
      · have hzmem : z ∈ ({p}ᶜ : Set ℂ) := hzp
        exact absurd hzzero (hzU hzmem)
  · have hcont : ContinuousAt entireRiemannXi p :=
      (entireRiemannXi_differentiable.analyticAt p).continuousAt
    have hEventually_ne :
        ∀ᶠ z in 𝓝 p, entireRiemannXi z ≠ 0 :=
      hcont.eventually_ne hp
    refine ⟨{z : ℂ | entireRiemannXi z ≠ 0}, hEventually_ne, ?_⟩
    have hempty :
        {z : ℂ | entireRiemannXi z ≠ 0}
            ∩ {s : ℂ | entireRiemannXi s = 0}
          = ∅ := by
      ext z
      constructor
      · rintro ⟨hz_ne, hz_zero⟩
        exact (hz_ne hz_zero).elim
      · intro hz
        exact absurd hz (Set.notMem_empty z)
    rw [hempty]
    exact Set.finite_empty

/-- ⭐ **PROVED — zeros of `entireRiemannXi` are finite in every closed
norm disk.**
@isnad1 id=finite.0h1v.s5.393e5e3fcf90 from=translated src=- shape=4e1c758a vocab=10cdd522
-/
theorem entireRiemannXi_zeroSet_finite_in_closedBall (R : ℝ) :
    {s : ℂ |
      s ∈ Metric.closedBall (0 : ℂ) R ∧ entireRiemannXi s = 0}.Finite := by
  classical
  let Z : Set ℂ :=
    {s : ℂ |
      s ∈ Metric.closedBall (0 : ℂ) R ∧ entireRiemannXi s = 0}
  let K : Set ℂ := Metric.closedBall (0 : ℂ) R
  have hK : IsCompact K := ProperSpace.isCompact_closedBall (0 : ℂ) R
  have hZK : Z ⊆ K := by
    intro z hz
    exact hz.1
  have hlocal :
      ∀ p ∈ K, ∃ U ∈ 𝓝 p, (U ∩ Z).Finite := by
    intro p _hp
    obtain ⟨U, hU, hfin⟩ := entireRiemannXi_zeroSet_locallyFinite p
    refine ⟨U, hU, ?_⟩
    exact hfin.subset (by
      rintro z ⟨hzU, hz⟩
      exact ⟨hzU, hz.2⟩)
  choose! V hV_nhds hV_finite using hlocal
  obtain ⟨t, ht_sub, ht_cover⟩ := hK.elim_nhds_subcover V hV_nhds
  have hZsubset : Z ⊆ ⋃ p ∈ t, V p ∩ Z := by
    intro z hz
    have hzK : z ∈ K := hZK hz
    obtain ⟨p, hpt, hzVp⟩ := Set.mem_iUnion₂.mp (ht_cover hzK)
    exact Set.mem_iUnion₂.mpr ⟨p, hpt, hzVp, hz⟩
  have hZfinite : Z.Finite := by
    refine Set.Finite.subset ?_ hZsubset
    refine Set.Finite.biUnion t.finite_toSet ?_
    intro p hp
    exact hV_finite p (ht_sub p hp)
  simpa [Z] using hZfinite

/-- 🌟🌟🌟 **PROVED — canonical entire-ξ zero norm-properness.**

The canonical index type is a subtype of the actual nonzero zero set.
Local isolated-zero theory proves finite-in-disks for the zero values,
and subtype injectivity transfers that finiteness to the index set.
@isnad1 id=entirexi.0h0v.s0.8cf33f7dd67e from=translated src=- shape=45709ebd vocab=8cf33f7d
-/
theorem entireXiCanonicalZeroNormProper :
    EntireXiCanonicalZeroNormProper := by
  refine ⟨?_⟩
  intro R
  let S : Set EntireXiNonzeroZeroIndex :=
    {i : EntireXiNonzeroZeroIndex |
      ‖concreteEntireXiZeroSystem.zeroLoc i‖ ≤ R}
  let Z : Set ℂ :=
    {s : ℂ |
      s ∈ Metric.closedBall (0 : ℂ) R ∧ entireRiemannXi s = 0}
  have hZfinite : Z.Finite :=
    entireRiemannXi_zeroSet_finite_in_closedBall R
  have himage_sub :
      (fun i : EntireXiNonzeroZeroIndex =>
          concreteEntireXiZeroSystem.zeroLoc i) '' S ⊆ Z := by
    rintro s ⟨i, hi, rfl⟩
    refine ⟨?_, concreteEntireXiZeroSystem.zeroLoc_is_zero i⟩
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    exact hi
  have himage_finite :
      ((fun i : EntireXiNonzeroZeroIndex =>
          concreteEntireXiZeroSystem.zeroLoc i) '' S).Finite :=
    hZfinite.subset himage_sub
  exact
    Set.Finite.of_finite_image himage_finite (by
      intro i _hi j _hj hij
      exact Subtype.ext hij)

/-- The canonical norm-ceiling fiber of nonzero entire-ξ zeros is finite.
@isnad1 id=finite.0h1v.s4.a3ed620ab457 from=translated src=- shape=17de3894 vocab=da9814de
-/
theorem entireXiCanonicalZeroNormCeilFiberFinite (n : ℕ) :
    {i : EntireXiNonzeroZeroIndex |
      Nat.ceil ‖concreteEntireXiZeroSystem.zeroLoc i‖ = n}.Finite := by
  exact (entireXiCanonicalZeroNormProper.finite_norm_le (n : ℝ)).subset (by
    intro i hi
    have hceil :
        Nat.ceil ‖concreteEntireXiZeroSystem.zeroLoc i‖ ≤ n := by
      rw [hi]
    exact Nat.le_of_ceil_le hceil)

/-- 🌟🌟 **PROVED — lower radius bound for a canonical zero in a
norm-ceiling shell.**

If `ρ` lies in shell `ceil ‖ρ‖ = n`, then its norm is strictly larger
than the previous integer radius.  This is the pointwise estimate used to
convert shell zero counts into inverse-square mass bounds.
@isnad1 id=lt.2h2v.s5.e96146f709c1 from=translated src=- shape=2bdd17f7 vocab=c953789b
-/
theorem entireXiCanonicalZeroNormCeilFiber_pred_lt_norm
    {i : EntireXiNonzeroZeroIndex} {n : ℕ}
    (hn : 1 ≤ n)
    (hi : Nat.ceil ‖concreteEntireXiZeroSystem.zeroLoc i‖ = n) :
    ((n - 1 : ℕ) : ℝ) < ‖concreteEntireXiZeroSystem.zeroLoc i‖ := by
  have hpred_lt_ceil :
      n - 1 < Nat.ceil ‖concreteEntireXiZeroSystem.zeroLoc i‖ := by
    rw [hi]
    omega
  exact Nat.lt_ceil.mp hpred_lt_ceil

/-- 📦 **Canonical norm-ceiling majorant for inverse-square ξ-zero
summability.**

This is the RvM-facing A1 input: it is enough to dominate the
inverse-square mass in each finite norm-ceiling shell by a summable
sequence.-/
structure EntireXiCanonicalZeroCeilFiberInvSqMajorant : Type where
  majorant : ℕ → ℝ
  majorant_summable : Summable majorant
  fiber_tsum_le :
    ∀ n : ℕ,
      (∑' i :
        {i : EntireXiNonzeroZeroIndex //
          Nat.ceil ‖concreteEntireXiZeroSystem.zeroLoc i‖ = n},
        (‖concreteEntireXiZeroSystem.zeroLoc i‖ ^ 2)⁻¹)
        ≤ majorant n

/-- 🌟🌟🌟🌟 **PROVED — entire-ξ product factorization from the
quotient-form Hadamard data.**

This removes the removable-singularity bookkeeping from later interfaces:
once the quotient has been identified off the zeros and the product has
the right zero set, the ordinary factorization field follows pointwise.
@isnad1 id=entirexi.1h3v.s4.3fd0d1a9051f from=translated src=- shape=54fe90d4 vocab=bddbee37
-/
theorem EntireXiHadamardFactorization.of_quotientFactorization
    {ι : Type} {HZ : ConcreteEntireXiZeroSystem ι}
    {prefactor : ℂ → ℂ}
    (H : EntireXiHadamardQuotientFactorization HZ prefactor) :
    EntireXiHadamardFactorization HZ prefactor := by
  refine ⟨?_⟩
  intro s
  by_cases hhit : ∃ i : ι, HZ.zeroLoc i = s
  · rcases hhit with ⟨i, hi⟩
    have hxi : entireRiemannXi s = 0 := by
      rw [← hi]
      exact HZ.zeroLoc_is_zero i
    have hprod :
        infiniteHadamardProduct HZ.zeroLoc s = 0 := by
      rw [← hi]
      exact H.product_vanishes_at_zeroLoc i
    simp [hxi, hprod]
  · have hno : ∀ i : ι, s ≠ HZ.zeroLoc i := by
      intro i hsi
      exact hhit ⟨i, hsi.symm⟩
    have hprod_ne :
        infiniteHadamardProduct HZ.zeroLoc s ≠ 0 :=
      H.product_nonzero_off_zeroLoc s hno
    have hq := H.quotient_eq_prefactor s hno
    rw [div_eq_iff hprod_ne] at hq
    exact hq

/-- 🌟🌟🌟 **PROVED — nonzero-locus LUC data gives the Hadamard
log-derivative limit data.**

This is an internal Hadamard reduction, not a new front door: the
no-collision hypothesis required by `HadamardLogDerivLimitData` is
discharged from the concrete entire-ξ zero system. If
`entireRiemannXi s ≠ 0`, then `s` cannot be one of the indexed zeros.-/
noncomputable def HadamardProductLUCOnEntireXiNonzeroData.toLogDerivLimitData
    {ι : Type}
    (HZ : ConcreteEntireXiZeroSystem ι)
    (Hdist : EntireXiZeroInvSqDistribution HZ)
    (Hluc : HadamardProductLUCOnEntireXiNonzeroData HZ.zeroLoc) :
    HadamardLogDerivLimitData HZ.zeroLoc :=
  HadamardLogDerivLimitData.of_productLUC_and_invSq
    Hluc.toLUCLogDerivData
    Hdist.toHadamardZeroInvSqSummability
    (by
      intro s hs
      exact HZ.nonzero_no_collision hs)

/-- 🌟🌟 **PROVED — canonical entire-ξ zero distribution from canonical
inverse-square summability and finite-in-disks properness.**
@isnad1 id=entirexi.2h0v.s5.037f85fa2cd1 from=translated src=- shape=cd41c82e vocab=6cd4622c
-/
theorem EntireXiZeroInvSqDistribution.of_canonical_invSqSummable_normProper
    (hinv :
      Summable fun i : EntireXiNonzeroZeroIndex =>
        (‖concreteEntireXiZeroSystem.zeroLoc i‖ ^ 2)⁻¹)
    (Hproper : EntireXiCanonicalZeroNormProper) :
    EntireXiZeroInvSqDistribution concreteEntireXiZeroSystem :=
  EntireXiZeroInvSqDistribution.of_invSqSummable_normProper hinv Hproper

/-- 🌟🌟🌟 **PROVED — canonical norm-ceiling zero-counting majorants imply
the exact inverse-square summability required by Hadamard.**
@isnad1 id=summable.0h1v.s5.a21e7b488475 from=translated src=- shape=00d346fb vocab=dfa1b428
-/
theorem entireXiCanonical_invSqSummable_of_ceilFiberMajorant
    (H : EntireXiCanonicalZeroCeilFiberInvSqMajorant) :
    Summable fun i : EntireXiNonzeroZeroIndex =>
      (‖concreteEntireXiZeroSystem.zeroLoc i‖ ^ 2)⁻¹ := by
  refine
    summable_of_nonneg_fiber_tsum_le
      (fun i : EntireXiNonzeroZeroIndex =>
        Nat.ceil ‖concreteEntireXiZeroSystem.zeroLoc i‖)
      ?_
      ?_
      H.majorant_summable
      H.fiber_tsum_le
  · intro i
    positivity
  · intro n
    exact entireXiCanonicalZeroNormCeilFiberFinite n

/-- 🌟🌟 **PROVED — canonical entire-ξ zero distribution from canonical
inverse-square summability alone (norm-properness supplied internally by
the isolated-zero theory).**
@isnad1 id=entirexi.1h0v.s5.3c7069314eb5 from=translated src=- shape=dfb1c359 vocab=f6420875
-/
theorem EntireXiZeroInvSqDistribution.of_canonical_invSqSummable
    (hinv :
      Summable fun i : EntireXiNonzeroZeroIndex =>
        (‖concreteEntireXiZeroSystem.zeroLoc i‖ ^ 2)⁻¹) :
    EntireXiZeroInvSqDistribution concreteEntireXiZeroSystem :=
  EntireXiZeroInvSqDistribution.of_canonical_invSqSummable_normProper
    hinv entireXiCanonicalZeroNormProper

/-- 🌟🌟🌟 **PROVED — quotient-form Hadamard data with the zero-factor
side discharged.** A quotient proof now only needs product nonvanishing
off the indexed zero set and the off-zero quotient identity.
@isnad1 id=entirexi.2h3v.s6.125599cadbba from=translated src=- shape=a01c9a8f vocab=f4145bb2
-/
theorem EntireXiHadamardFactorization.of_offZeroQuotient
    {ι : Type} {HZ : ConcreteEntireXiZeroSystem ι}
    {prefactor : ℂ → ℂ}
    (hprod_ne :
      ∀ s : ℂ,
        (∀ i : ι, s ≠ HZ.zeroLoc i) →
          infiniteHadamardProduct HZ.zeroLoc s ≠ 0)
    (hquot :
      ∀ s : ℂ,
        (∀ i : ι, s ≠ HZ.zeroLoc i) →
          entireRiemannXi s / infiniteHadamardProduct HZ.zeroLoc s
            = prefactor s) :
    EntireXiHadamardFactorization HZ prefactor :=
  EntireXiHadamardFactorization.of_quotientFactorization
    { product_vanishes_at_zeroLoc :=
        infiniteHadamardProduct_eq_zero_at_zeroLoc HZ.zeroLoc_ne_zero
      product_nonzero_off_zeroLoc := hprod_ne
      quotient_eq_prefactor := hquot }

/-- 🌟🌟🌟 **PROVED — the same norm-ceiling majorant directly supplies the
canonical entire-ξ inverse-square zero-distribution package.**
@isnad1 id=entirexi.0h1v.s2.2cae28121a69 from=translated src=- shape=da6c7ba4 vocab=abe8b5da
-/
theorem EntireXiZeroInvSqDistribution.of_canonical_ceilFiberMajorant
    (H : EntireXiCanonicalZeroCeilFiberInvSqMajorant) :
    EntireXiZeroInvSqDistribution concreteEntireXiZeroSystem :=
  EntireXiZeroInvSqDistribution.of_canonical_invSqSummable
    (entireXiCanonical_invSqSummable_of_ceilFiberMajorant H)

/-- 🌟🌟🌟🌟 **PROVED — quotient-form Hadamard factorization with product
nonvanishing discharged from inverse-square zero distribution.** The
only remaining factorization input is the off-zero quotient identity.
@isnad1 id=entirexi.2h3v.s5.02015b318590 from=translated src=- shape=b42f5ff4 vocab=bc75e5e5
-/
theorem EntireXiHadamardFactorization.of_offZeroQuotient_invSq
    {ι : Type} {HZ : ConcreteEntireXiZeroSystem ι}
    {prefactor : ℂ → ℂ}
    (Hdist : EntireXiZeroInvSqDistribution HZ)
    (hquot :
      ∀ s : ℂ,
        (∀ i : ι, s ≠ HZ.zeroLoc i) →
          entireRiemannXi s / infiniteHadamardProduct HZ.zeroLoc s
            = prefactor s) :
    EntireXiHadamardFactorization HZ prefactor :=
  EntireXiHadamardFactorization.of_offZeroQuotient
    (fun _s hs => Hdist.infiniteProduct_ne_zero hs)
    hquot

end OverflowResidueRH
