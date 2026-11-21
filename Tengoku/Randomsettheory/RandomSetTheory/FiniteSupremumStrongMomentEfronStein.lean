/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteSupremumEfronStein
import Tengoku.Randomsettheory.RandomSetTheory.CenteredProcessEnvelope
import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentInterpolation
import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentChernoff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strong moments for a ghost-coordinate supremum fibre

The quadratic ghost estimate in `FiniteSupremumEfronStein` is complemented
here by bounds for every positive centred moment.  If a scalar fibre obeys

`|G b z - G b z'| ≤ A z + A z'`,

then its centred positive part is pointwise dominated by

`A z + ∫ A dν`.

Consequently every order `k ≤ q` is integrable when `A ∈ L^q`, and its
moment is bounded by the deterministic `k`-th moment of that envelope.  For
an independent revealed past/current-coordinate pair `(P,Y)`, the same
calculation becomes a conditional-expectation bound given `P`.  These are
the strong-moment inputs needed by the conditional Taylor/MGF layer.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Z : Type*} [MeasurableSpace Z] {nu : Measure Z}

/-- Deterministic envelope for a centred replace-one fibre.-/
def replaceOneCenteredEnvelope (nu : Measure Z) (A : Z → ℝ) (z : Z) : ℝ :=
  A z + ∫ z', A z' ∂nu

/-- Deterministic strong-moment proxy attached to the replace-one envelope.-/
def replaceOneCenteredMoment (nu : Measure Z) (A : Z → ℝ) (k : ℕ) : ℝ :=
  ∫ z, replaceOneCenteredEnvelope nu A z ^ k ∂nu

theorem replaceOneCenteredEnvelope_nonneg
    (A : Z → ℝ) (hA : ∀ z, 0 ≤ A z) (z : Z) :
    0 ≤ replaceOneCenteredEnvelope nu A z := by
  unfold replaceOneCenteredEnvelope
  exact add_nonneg (hA z) (integral_nonneg hA)

/-- A replace-one modulus and one `L^q` envelope automatically put every
scalar fibre in `L^q`; no separate fibre integrability assumption is needed.-/
theorem memLp_fiber_of_abs_sub_le_add_envelopes
    [IsProbabilityMeasure nu] [Nonempty Z]
    (F A : Z → ℝ) (q : ℕ)
    (hF : StronglyMeasurable F) (hAq : MemLp A q nu)
    (hA : ∀ z, 0 ≤ A z)
    (hreplace : ∀ z z', |F z - F z'| ≤ A z + A z') :
    MemLp F q nu := by
  let z₀ : Z := Classical.choice inferInstance
  let C : ℝ := |F z₀| + A z₀
  have hC : 0 ≤ C := add_nonneg (abs_nonneg _) (hA z₀)
  have hmajorant : MemLp (fun z ↦ C + A z) q nu :=
    (memLp_const C).add hAq
  apply hmajorant.mono' hF.aestronglyMeasurable
  filter_upwards [] with z
  have hbound : |F z| ≤ C + A z := by
    calc
      |F z| = |(F z - F z₀) + F z₀| := by rw [sub_add_cancel]
      _ ≤ |F z - F z₀| + |F z₀| := abs_add_le _ _
      _ ≤ A z + A z₀ + |F z₀| :=
        by simpa only [add_comm] using
          add_le_add_right (hreplace z z₀) |F z₀|
      _ = C + A z := by ring
  exact hbound

/-- Pointwise ghost-centering inequality.  It is the positive-moment analogue
of the variance identity: centring is represented as integration against an
independent ghost copy and the replace-one modulus is then integrated.-/
theorem max_sub_integral_le_replaceOneCenteredEnvelope
    [IsProbabilityMeasure nu]
    (F A : Z → ℝ) (hFint : Integrable F nu) (hAint : Integrable A nu)
    (hreplace : ∀ z z', |F z - F z'| ≤ A z + A z')
    (z : Z) :
    max (F z - ∫ z', F z' ∂nu) 0 ≤ replaceOneCenteredEnvelope nu A z := by
  have hdiffInt : Integrable (fun z' ↦ F z - F z') nu :=
    (integrable_const _).sub hFint
  have henvInt : Integrable (fun z' ↦ A z + A z') nu :=
    (integrable_const _).add hAint
  have heq : F z - ∫ z', F z' ∂nu =
      ∫ z', (F z - F z') ∂nu := by
    rw [integral_sub (integrable_const _) hFint, integral_const,
      probReal_univ, one_smul]
  have habs : |∫ z', (F z - F z') ∂nu| ≤
      ∫ z', (A z + A z') ∂nu := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le (f := fun z' ↦ F z - F z') henvInt
        (ae_of_all nu fun z' ↦ by
          simpa only [Real.norm_eq_abs] using hreplace z z')
  have hright : ∫ z', (A z + A z') ∂nu =
      replaceOneCenteredEnvelope nu A z := by
    rw [integral_add (integrable_const _) hAint, integral_const,
      probReal_univ, one_smul]
    rfl
  rw [heq]
  calc
    max (∫ z', (F z - F z') ∂nu) 0 ≤
        |∫ z', (F z - F z') ∂nu| :=
      max_le (le_abs_self _) (abs_nonneg _)
    _ ≤ ∫ z', (A z + A z') ∂nu := habs
    _ = replaceOneCenteredEnvelope nu A z := hright

/-- `L^q` membership of the raw envelope supplies integrability of the
deterministic centred-envelope power at every integer order `k ≤ q`.-/
theorem integrable_pow_replaceOneCenteredEnvelope
    [IsProbabilityMeasure nu]
    (A : Z → ℝ) (q k : ℕ) (hkq : k ≤ q)
    (hAq : MemLp A q nu) (hA : ∀ z, 0 ≤ A z) :
    Integrable (fun z ↦ replaceOneCenteredEnvelope nu A z ^ k) nu := by
  have hkq' : (k : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by exact_mod_cast hkq
  have hAk : MemLp A k nu := hAq.mono_exponent hkq'
  have hB : MemLp (replaceOneCenteredEnvelope nu A) k nu := by
    unfold replaceOneCenteredEnvelope
    exact hAk.add (memLp_const (∫ z, A z ∂nu))
  have hnorm := hB.integrable_norm_pow'
  convert hnorm using 1
  funext z
  rw [Real.norm_eq_abs,
    abs_of_nonneg (replaceOneCenteredEnvelope_nonneg A hA z)]

/-- Unconditional strong-moment ghost bound.  The hypotheses `2 ≤ k ≤ q`
match the range consumed by the strong-moment Taylor exponent.-/
theorem integral_pow_max_centeredFiber_le_replaceOneCenteredMoment
    [IsProbabilityMeasure nu] [Nonempty Z]
    (F A : Z → ℝ) (q k : ℕ) (hk : 2 ≤ k) (hkq : k ≤ q)
    (hF : StronglyMeasurable F) (hAq : MemLp A q nu)
    (hA : ∀ z, 0 ≤ A z)
    (hreplace : ∀ z z', |F z - F z'| ≤ A z + A z') :
    (∫ z, max (F z - ∫ z', F z' ∂nu) 0 ^ k ∂nu) ≤
      replaceOneCenteredMoment nu A k := by
  have hqone : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    exact_mod_cast (le_trans (by omega : 1 ≤ k) hkq)
  have hFq : MemLp F q nu :=
    memLp_fiber_of_abs_sub_le_add_envelopes F A q hF hAq hA hreplace
  have hFint : Integrable F nu :=
    (hFq.mono_exponent hqone).integrable (by norm_num)
  have hAint : Integrable A nu :=
    (hAq.mono_exponent hqone).integrable (by norm_num)
  have hright := integrable_pow_replaceOneCenteredEnvelope A q k hkq hAq hA
  have hleftStrong : AEStronglyMeasurable
      (fun z ↦ max (F z - ∫ z', F z' ∂nu) 0 ^ k) nu :=
    (((hF.measurable.sub measurable_const).max measurable_const).pow_const k).aestronglyMeasurable
  have hleft : Integrable
      (fun z ↦ max (F z - ∫ z', F z' ∂nu) 0 ^ k) nu := by
    apply hright.mono' hleftStrong
    filter_upwards [] with z
    have hpow := pow_le_pow_left₀ (le_max_right
        (F z - ∫ z', F z' ∂nu) 0)
      (max_sub_integral_le_replaceOneCenteredEnvelope
        F A hFint hAint hreplace z) k
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (le_max_right
        (F z - ∫ z', F z' ∂nu) 0) k)] using hpow
  unfold replaceOneCenteredMoment
  apply integral_mono hleft hright
  intro z
  exact pow_le_pow_left₀ (le_max_right _ _)
    (max_sub_integral_le_replaceOneCenteredEnvelope
      F A hFint hAint hreplace z) k

/-- The deterministic ghost proxies inherit Rio's exact interpolation
between their aggregate orders two and `q`.  This discharges the
intermediate-moment hypothesis of the optimized transform once aggregate
second- and `q`-moment bounds are known.-/
theorem sum_replaceOneCenteredMoment_le_interpolatedStrongMomentCoefficient
    {I : Type*} [IsProbabilityMeasure nu]
    (s : Finset I) (A : I → Z → ℝ)
    (q k : ℕ) (hq : 3 ≤ q) (hk : 2 ≤ k) (hkq : k ≤ q)
    (hAq : ∀ i ∈ s, MemLp (A i) q nu)
    (hA : ∀ i ∈ s, ∀ z, 0 ≤ A i z)
    {V Q : ℝ} (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (hSecond :
      (∑ i ∈ s, replaceOneCenteredMoment nu (A i) 2) ≤ V)
    (hQMoment :
      (∑ i ∈ s, replaceOneCenteredMoment nu (A i) q) ≤ Q) :
    (∑ i ∈ s, replaceOneCenteredMoment nu (A i) k) ≤
      interpolatedStrongMomentCoefficient q V Q k := by
  unfold interpolatedStrongMomentCoefficient
  apply sum_integral_pow_le_strongMomentInterpolation_of_le
    nu s (fun i ↦ replaceOneCenteredEnvelope nu (A i))
      hq hk hkq
  · intro i hi
    unfold replaceOneCenteredEnvelope
    exact (hAq i hi).aestronglyMeasurable.aemeasurable.add aemeasurable_const
  · intro i hi
    exact ae_of_all nu fun z ↦
      replaceOneCenteredEnvelope_nonneg (A i) (hA i hi) z
  · intro i hi
    exact integrable_pow_replaceOneCenteredEnvelope
      (A i) q 2 (by omega) (hAq i hi) (hA i hi)
  · intro i hi
    exact integrable_pow_replaceOneCenteredEnvelope
      (A i) q k hkq (hAq i hi) (hA i hi)
  · intro i hi
    exact integrable_pow_replaceOneCenteredEnvelope
      (A i) q q le_rfl (hAq i hi) (hA i hi)
  · exact hV
  · exact hQ
  · simpa only [replaceOneCenteredMoment] using hSecond
  · simpa only [replaceOneCenteredMoment] using hQMoment

/-! ## Conditional version under an independent revealed past -/

/-- Conditional strong-moment ghost bridge.  Given independence of `P` and
`Y`, conditioning on the revealed past freezes `b = P ω`, and the preceding
fibrewise estimate applies against the deterministic law `mu.map Y`.

All integrability assumptions are discharged from the single envelope
condition `A ∈ L^q(mu.map Y)` and joint strong measurability of `G`.-/
theorem condExp_pow_max_centeredGhostFiber_le
    {Omega Beta : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Beta]
    [StandardBorelSpace Z] [Nonempty Z]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (P : Omega → Beta) (Y : Omega → Z)
    (hPY : IndepFun P Y mu) (hP : Measurable P) (hY : Measurable Y)
    (G : Beta → Z → ℝ) (A : Z → ℝ) (q k : ℕ)
    (hk : 2 ≤ k) (hkq : k ≤ q)
    (hG : StronglyMeasurable (Function.uncurry G))
    (hAq : MemLp A q (mu.map Y)) (hA : ∀ z, 0 ≤ A z)
    (hreplace : ∀ b z z', |G b z - G b z'| ≤ A z + A z') :
    ∀ᵐ omega ∂mu,
      mu[fun omega' ↦
          max (G (P omega') (Y omega') -
            ∫ z, G (P omega') z ∂(mu.map Y)) 0 ^ k |
          MeasurableSpace.comap P inferInstance] omega ≤
        replaceOneCenteredMoment (mu.map Y) A k := by
  letI : IsProbabilityMeasure (mu.map Y) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  have hmean : StronglyMeasurable
      (fun b ↦ ∫ z, G b z ∂(mu.map Y)) :=
    hG.integral_prod_right
  have hcentered : StronglyMeasurable (fun bz : Beta × Z ↦
      G bz.1 bz.2 - ∫ z, G bz.1 z ∂(mu.map Y)) :=
    hG.sub (hmean.comp_measurable measurable_fst)
  have hmomentStrong : StronglyMeasurable (fun bz : Beta × Z ↦
      max (G bz.1 bz.2 - ∫ z, G bz.1 z ∂(mu.map Y)) 0 ^ k) :=
    (((hcentered.measurable.max measurable_const).pow_const k).stronglyMeasurable)
  have hqone : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    exact_mod_cast (le_trans (by omega : 1 ≤ k) hkq)
  have hAint : Integrable A (mu.map Y) :=
    (hAq.mono_exponent hqone).integrable (by norm_num)
  have hright := integrable_pow_replaceOneCenteredEnvelope
    (nu := mu.map Y) A q k hkq hAq hA
  have hrightComp : Integrable
      (fun omega ↦ replaceOneCenteredEnvelope (mu.map Y) A (Y omega) ^ k) mu :=
    hright.comp_measurable hY
  have hcomposed : Integrable (fun omega ↦
      max (G (P omega) (Y omega) -
        ∫ z, G (P omega) z ∂(mu.map Y)) 0 ^ k) mu := by
    apply hrightComp.mono'
      (hmomentStrong.comp_measurable (hP.prodMk hY)).aestronglyMeasurable
    filter_upwards [] with omega
    have hGb : StronglyMeasurable (G (P omega)) :=
      hG.comp_measurable (measurable_const.prodMk measurable_id)
    have hGq : MemLp (G (P omega)) q (mu.map Y) :=
      memLp_fiber_of_abs_sub_le_add_envelopes
        (G (P omega)) A q hGb hAq hA (hreplace (P omega))
    have hGint : Integrable (G (P omega)) (mu.map Y) :=
      (hGq.mono_exponent hqone).integrable (by norm_num)
    simp only [Function.comp_apply]
    have hpow := pow_le_pow_left₀ (le_max_right
        (G (P omega) (Y omega) -
          ∫ z, G (P omega) z ∂(mu.map Y)) 0)
      (max_sub_integral_le_replaceOneCenteredEnvelope
        (G (P omega)) A hGint hAint (hreplace (P omega)) (Y omega)) k
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (le_max_right
        (G (P omega) (Y omega) -
          ∫ z, G (P omega) z ∂(mu.map Y)) 0) k)] using hpow
  have hbase := hPY.condExp_prod_ae_eq_integral_map hP hY
    (fun bz : Beta × Z ↦
      max (G bz.1 bz.2 - ∫ z, G bz.1 z ∂(mu.map Y)) 0 ^ k)
    hmomentStrong hcomposed
  filter_upwards [hbase] with omega hbaseOmega
  rw [hbaseOmega]
  exact integral_pow_max_centeredFiber_le_replaceOneCenteredMoment
      (nu := mu.map Y) (G (P omega)) A q k hk hkq
      (hG.comp_measurable (measurable_const.prodMk measurable_id))
      hAq hA (hreplace (P omega))

/-! ## Transport to a concrete Doob increment -/

/-- A revealed-past/current-coordinate representation transports the full
strong-moment ghost estimate to a Doob difference.

This is the order-`k` analogue of
`condExp_sq_doobCenteredDifference_succ_le_of_finiteReplaceOne`.  The
representation is deliberately abstract because, after the unrevealed future
has been integrated out, the fibre `G b` need no longer be syntactically a
finite supremum; its replace-one modulus is the invariant property used by
the proof.-/
theorem condExp_pow_max_doobCenteredDifference_succ_le_of_centeredGhostFiber
    {Omega Beta : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Beta]
    [StandardBorelSpace Z] [Nonempty Z]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ inferInstance)
    (F : Omega → ℝ) (i : ℕ)
    (P : Omega → Beta) (Y : Omega → Z)
    (hPY : IndepFun P Y mu) (hP : Measurable P) (hY : Measurable Y)
    (hfiltration : filtration i = MeasurableSpace.comap P inferInstance)
    (G : Beta → Z → ℝ) (A : Z → ℝ) (q k : ℕ)
    (hk : 2 ≤ k) (hkq : k ≤ q)
    (hG : StronglyMeasurable (Function.uncurry G))
    (hAq : MemLp A q (mu.map Y)) (hA : ∀ z, 0 ≤ A z)
    (hreplace : ∀ b z z', |G b z - G b z'| ≤ A z + A z')
    (hrepresentation :
      doobCenteredDifference filtration mu F (i + 1) =ᵐ[mu]
        fun omega ↦ G (P omega) (Y omega) -
          ∫ z, G (P omega) z ∂(mu.map Y)) :
    ∀ᵐ omega ∂mu,
      mu[fun omega' ↦
          max (doobCenteredDifference filtration mu F (i + 1) omega') 0 ^ k |
        filtration i] omega ≤
          replaceOneCenteredMoment (mu.map Y) A k := by
  let R : Omega → ℝ := fun omega ↦
    G (P omega) (Y omega) - ∫ z, G (P omega) z ∂(mu.map Y)
  have hpower :
      (fun omega ↦
        max (doobCenteredDifference filtration mu F (i + 1) omega) 0 ^ k)
        =ᵐ[mu] fun omega ↦ max (R omega) 0 ^ k := by
    filter_upwards [hrepresentation] with omega homega
    rw [homega]
  have hcondCongr := condExp_congr_ae (m := filtration i) hpower
  have hghost := condExp_pow_max_centeredGhostFiber_le
    P Y hPY hP hY G A q k hk hkq hG hAq hA hreplace
  rw [hfiltration] at hcondCongr ⊢
  filter_upwards [hcondCongr, hghost] with omega hcongrOmega hghostOmega
  exact hcongrOmega.trans_le hghostOmega

end ProbabilityTheory
