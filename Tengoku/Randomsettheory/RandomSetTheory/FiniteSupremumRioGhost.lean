/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteSupremumRio
import Tengoku.Randomsettheory.RandomSetTheory.FiniteSupremumStrongMomentEfronStein

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rio's finite-supremum endpoint from ghost-coordinate representations

This file discharges the abstract conditional-moment interface of
`FiniteSupremumRio` from explicit revealed-past/current-coordinate
representations of the Doob differences.  The coordinate laws are allowed to
be represented by different random variables, but are assumed to coincide
with one common law `nu`; this is the iid hypothesis needed to interpolate
their deterministic ghost-moment proxies.

The construction of the canonical product filtration and the proof that its
Doob differences have the displayed ghost-fibre form remain separate.  The
initial difference is assumed to vanish, as it does when time zero is the
trivial sigma-algebra.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Z : Type*} [MeasurableSpace Z] {nu : Measure Z}

omit [MeasurableSpace Z] in
/-- Integrating out future coordinates preserves a replace-one envelope.

This elementary contraction is the deterministic step needed to pass a
coordinatewise modulus of the terminal process to its future-integrated value
functions.-/
theorem abs_integral_sub_integral_le_add_envelopes
    {Beta W : Type*} [MeasurableSpace W]
    {kappa : Measure W} [IsProbabilityMeasure kappa]
    (H : Beta → Z → W → ℝ) (A : Z → ℝ)
    (hH : ∀ b z, Integrable (H b z) kappa)
    (hreplace : ∀ b z z' w,
      |H b z w - H b z' w| ≤ A z + A z')
    (b : Beta) (z z' : Z) :
    |∫ w, H b z w ∂kappa - ∫ w, H b z' w ∂kappa| ≤
      A z + A z' := by
  rw [← integral_sub (hH b z) (hH b z')]
  have hbound := norm_integral_le_of_norm_le
    (f := fun w ↦ H b z w - H b z' w)
    (integrable_const (A z + A z'))
    (ae_of_all kappa fun w ↦ by
      simpa only [Real.norm_eq_abs] using hreplace b z z' w)
  simpa only [Real.norm_eq_abs, integral_const, probReal_univ, one_smul]
    using hbound

/-- Absolute (rather than only positive-part) form of ghost centring.-/
theorem abs_sub_integral_le_replaceOneCenteredEnvelope
    [IsProbabilityMeasure nu]
    (F A : Z → ℝ) (hFint : Integrable F nu) (hAint : Integrable A nu)
    (hreplace : ∀ z z', |F z - F z'| ≤ A z + A z') (z : Z) :
    |F z - ∫ z', F z' ∂nu| ≤ replaceOneCenteredEnvelope nu A z := by
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
  rw [heq, ← hright]
  exact habs

/-- The composition of a centred ghost fibre with a measurable
past/current-coordinate pair inherits the envelope's `L^q` bound.-/
theorem memLp_centeredGhostFiber_comp
    {Omega Beta : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Beta]
    [StandardBorelSpace Z] [Nonempty Z]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (P : Omega → Beta) (Y : Omega → Z)
    (hP : Measurable P) (hY : Measurable Y)
    (G : Beta → Z → ℝ) (A : Z → ℝ) (q : ℕ) (hq : 1 ≤ q)
    (hG : StronglyMeasurable (Function.uncurry G))
    (hAq : MemLp A q (mu.map Y)) (hA : ∀ z, 0 ≤ A z)
    (hreplace : ∀ b z z', |G b z - G b z'| ≤ A z + A z') :
    MemLp (fun omega ↦
      G (P omega) (Y omega) - ∫ z, G (P omega) z ∂(mu.map Y)) q mu := by
  letI : IsProbabilityMeasure (mu.map Y) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  have hqone : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by exact_mod_cast hq
  have hAint : Integrable A (mu.map Y) :=
    (hAq.mono_exponent hqone).integrable (by norm_num)
  have hmean : StronglyMeasurable
      (fun b ↦ ∫ z, G b z ∂(mu.map Y)) :=
    hG.integral_prod_right
  have hcentered : StronglyMeasurable (fun bz : Beta × Z ↦
      G bz.1 bz.2 - ∫ z, G bz.1 z ∂(mu.map Y)) :=
    hG.sub (hmean.comp_measurable measurable_fst)
  have henv : MemLp (replaceOneCenteredEnvelope (mu.map Y) A) q
      (mu.map Y) := by
    unfold replaceOneCenteredEnvelope
    exact hAq.add (memLp_const (∫ z, A z ∂(mu.map Y)))
  have henvComp : MemLp
      (replaceOneCenteredEnvelope (mu.map Y) A ∘ Y) q mu :=
    henv.comp_of_map hY.aemeasurable
  apply henvComp.mono'
    (hcentered.comp_measurable (hP.prodMk hY)).aestronglyMeasurable
  filter_upwards [] with omega
  have hGb : StronglyMeasurable (G (P omega)) :=
    hG.comp_measurable (measurable_const.prodMk measurable_id)
  have hGq : MemLp (G (P omega)) q (mu.map Y) :=
    memLp_fiber_of_abs_sub_le_add_envelopes
      (G (P omega)) A q hGb hAq hA (hreplace (P omega))
  have hGint : Integrable (G (P omega)) (mu.map Y) :=
    (hGq.mono_exponent hqone).integrable (by norm_num)
  simpa only [Function.comp_apply, Real.norm_eq_abs] using
    abs_sub_integral_le_replaceOneCenteredEnvelope
      (G (P omega)) A hGint hAint (hreplace (P omega)) (Y omega)

/-- The full conditional square of a centred ghost fibre is controlled by
the same order-two proxy as the positive moments.  This common proxy is what
makes aggregate interpolation exact.-/
theorem condExp_sq_centeredGhostFiber_le_replaceOneCenteredMoment
    {Omega Beta : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Beta]
    [StandardBorelSpace Z] [Nonempty Z]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (P : Omega → Beta) (Y : Omega → Z)
    (hPY : IndepFun P Y mu) (hP : Measurable P) (hY : Measurable Y)
    (G : Beta → Z → ℝ) (A : Z → ℝ) (q : ℕ) (hq : 2 ≤ q)
    (hG : StronglyMeasurable (Function.uncurry G))
    (hAq : MemLp A q (mu.map Y)) (hA : ∀ z, 0 ≤ A z)
    (hreplace : ∀ b z z', |G b z - G b z'| ≤ A z + A z') :
    ∀ᵐ omega ∂mu,
      mu[fun omega' ↦
          (G (P omega') (Y omega') -
            ∫ z, G (P omega') z ∂(mu.map Y)) ^ 2 |
          MeasurableSpace.comap P inferInstance] omega ≤
        replaceOneCenteredMoment (mu.map Y) A 2 := by
  letI : IsProbabilityMeasure (mu.map Y) :=
    Measure.isProbabilityMeasure_map hY.aemeasurable
  have hqone : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
    exact_mod_cast (le_trans (by omega : 1 ≤ 2) hq)
  have hqtwo : (2 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by exact_mod_cast hq
  have hAint : Integrable A (mu.map Y) :=
    (hAq.mono_exponent hqone).integrable (by norm_num)
  have hmean : StronglyMeasurable
      (fun b ↦ ∫ z, G b z ∂(mu.map Y)) :=
    hG.integral_prod_right
  have hcentered : StronglyMeasurable (fun bz : Beta × Z ↦
      G bz.1 bz.2 - ∫ z, G bz.1 z ∂(mu.map Y)) :=
    hG.sub (hmean.comp_measurable measurable_fst)
  have hR2 := (memLp_centeredGhostFiber_comp
    P Y hP hY G A q (by omega) hG hAq hA hreplace).mono_exponent hqtwo
  have hbase := hPY.condExp_prod_ae_eq_integral_map hP hY
    (fun bz : Beta × Z ↦
      (G bz.1 bz.2 - ∫ z, G bz.1 z ∂(mu.map Y)) ^ 2)
    (hcentered.pow 2) hR2.integrable_sq
  filter_upwards [hbase] with omega hbaseOmega
  rw [hbaseOmega]
  have hGb : StronglyMeasurable (G (P omega)) :=
    hG.comp_measurable (measurable_const.prodMk measurable_id)
  have hGq : MemLp (G (P omega)) q (mu.map Y) :=
    memLp_fiber_of_abs_sub_le_add_envelopes
      (G (P omega)) A q hGb hAq hA (hreplace (P omega))
  have hG2 : MemLp (G (P omega)) 2 (mu.map Y) :=
    hGq.mono_exponent hqtwo
  have hGint : Integrable (G (P omega)) (mu.map Y) :=
    (hGq.mono_exponent hqone).integrable (by norm_num)
  have hleft : Integrable (fun z ↦
      (G (P omega) z - ∫ z', G (P omega) z' ∂(mu.map Y)) ^ 2)
      (mu.map Y) :=
    (hG2.sub (memLp_const _)).integrable_sq
  have hright := integrable_pow_replaceOneCenteredEnvelope
    (nu := mu.map Y) A q 2 hq hAq hA
  unfold replaceOneCenteredMoment
  apply integral_mono hleft hright
  intro z
  have habs := abs_sub_integral_le_replaceOneCenteredEnvelope
    (G (P omega)) A hGint hAint (hreplace (P omega)) z
  have hpow := pow_le_pow_left₀ (abs_nonneg _) habs 2
  simpa only [sq_abs] using hpow

/-- Transport of the preceding square estimate to a concrete successor Doob
difference represented by the centred ghost fibre.-/
theorem condExp_sq_doobCenteredDifference_succ_le_of_centeredGhostFiber
    {Omega Beta : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Beta]
    [StandardBorelSpace Z] [Nonempty Z]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ inferInstance)
    (F : Omega → ℝ) (i : ℕ)
    (P : Omega → Beta) (Y : Omega → Z)
    (hPY : IndepFun P Y mu) (hP : Measurable P) (hY : Measurable Y)
    (hfiltration : filtration i = MeasurableSpace.comap P inferInstance)
    (G : Beta → Z → ℝ) (A : Z → ℝ) (q : ℕ) (hq : 2 ≤ q)
    (hG : StronglyMeasurable (Function.uncurry G))
    (hAq : MemLp A q (mu.map Y)) (hA : ∀ z, 0 ≤ A z)
    (hreplace : ∀ b z z', |G b z - G b z'| ≤ A z + A z')
    (hrepresentation :
      doobCenteredDifference filtration mu F (i + 1) =ᵐ[mu]
        fun omega ↦ G (P omega) (Y omega) -
          ∫ z, G (P omega) z ∂(mu.map Y)) :
    ∀ᵐ omega ∂mu,
      mu[fun omega' ↦
          doobCenteredDifference filtration mu F (i + 1) omega' ^ 2 |
        filtration i] omega ≤
          replaceOneCenteredMoment (mu.map Y) A 2 := by
  let R : Omega → ℝ := fun omega ↦
    G (P omega) (Y omega) - ∫ z, G (P omega) z ∂(mu.map Y)
  have hsquare :
      (fun omega ↦
        doobCenteredDifference filtration mu F (i + 1) omega ^ 2)
        =ᵐ[mu] fun omega ↦ R omega ^ 2 := by
    filter_upwards [hrepresentation] with omega homega
    rw [homega]
  have hcondCongr := condExp_congr_ae (m := filtration i) hsquare
  have hghost := condExp_sq_centeredGhostFiber_le_replaceOneCenteredMoment
    P Y hPY hP hY G A q hq hG hAq hA hreplace
  rw [hfiltration] at hcondCongr ⊢
  filter_upwards [hcondCongr, hghost] with omega hcongrOmega hghostOmega
  exact hcongrOmega.trans_le hghostOmega

/-- Identify a successor Doob difference with a centred ghost fibre from an
identification of the *next* conditional expectation.

The past conditional expectation is not assumed: the tower property and
independence of `(P,Y)` compute it automatically as the integral of `G` in
the current coordinate.  This is the structural bridge used when `G` is the
future-integrated value function of a product process.-/
theorem doobCenteredDifference_succ_ae_eq_centeredGhostFiber_of_condExp_next
    {Omega Beta : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Beta]
    [StandardBorelSpace Z] [Nonempty Z]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ inferInstance)
    (F : Omega → ℝ) (i : ℕ)
    (P : Omega → Beta) (Y : Omega → Z)
    (hPY : IndepFun P Y mu) (hP : Measurable P) (hY : Measurable Y)
    (hfiltration : filtration i = MeasurableSpace.comap P inferInstance)
    (G : Beta → Z → ℝ)
    (hG : StronglyMeasurable (Function.uncurry G))
    (hnext : mu[F | filtration (i + 1)] =ᵐ[mu]
      fun omega ↦ G (P omega) (Y omega)) :
    doobCenteredDifference filtration mu F (i + 1) =ᵐ[mu]
      fun omega ↦ G (P omega) (Y omega) -
        ∫ z, G (P omega) z ∂(mu.map Y) := by
  let H : Omega → ℝ := fun omega ↦ G (P omega) (Y omega)
  have hHint : Integrable H mu := by
    exact integrable_condExp.congr hnext
  have hcondCongr :
      mu[mu[F | filtration (i + 1)] | filtration i] =ᵐ[mu]
        mu[H | filtration i] :=
    condExp_congr_ae (m := filtration i) hnext
  have htower :
      mu[mu[F | filtration (i + 1)] | filtration i] =ᵐ[mu]
        mu[F | filtration i] :=
    condExp_condExp_of_le (filtration.mono (Nat.le_succ i))
      (filtration.le (i + 1))
  have hghostRaw := hPY.condExp_prod_ae_eq_integral_map hP hY
    (Function.uncurry G) hG
      (by simpa only [Function.uncurry_apply_pair, H] using hHint)
  have hghost : mu[H | MeasurableSpace.comap P inferInstance] =ᵐ[mu]
      fun omega ↦ ∫ z, G (P omega) z ∂(mu.map Y) := by
    simpa only [H, Function.uncurry_apply_pair] using hghostRaw
  rw [← hfiltration] at hghost
  have hpast : mu[F | filtration i] =ᵐ[mu]
      fun omega ↦ ∫ z, G (P omega) z ∂(mu.map Y) :=
    htower.symm.trans (hcondCongr.trans hghost)
  filter_upwards [hnext, hpast] with omega hnextOmega hpastOmega
  change mu[F | filtration (i + 1)] omega -
      mu[F | filtration i] omega = _
  rw [hnextOmega, hpastOmega]

variable {Omega T Beta : Type*} {mOmega : MeasurableSpace Omega}
  {mu : Measure Omega}
  [MeasurableSpace Beta]

/-- The centred time-zero Doob difference vanishes automatically when the
initial sigma-algebra is trivial.  This removes a separate probabilistic
hypothesis from applications built with the canonical product filtration.-/
theorem doobCenteredDifference_zero_ae_eq_zero_of_filtration_zero_eq_bot
    [IsProbabilityMeasure mu]
    (filtration : Filtration ℕ mOmega) (F : Omega → ℝ)
    (hzero : filtration 0 = ⊥) :
    doobCenteredDifference filtration mu F 0 =ᵐ[mu] 0 := by
  rw [show doobCenteredDifference filtration mu F 0 =
      fun omega ↦ mu[F | filtration 0] omega - ∫ z, F z ∂mu by
        rfl, hzero, condExp_bot]
  exact Filter.Eventually.of_forall fun omega ↦ by simp

/-- Finite-supremum Rio bound whose conditional second and strong-moment
hypotheses are generated from explicit centred ghost-fibre representations.

The family `Acoord j` provides the deterministic proxy for Doob difference
`j`.  Index zero is unused probabilistically (the difference is assumed to
vanish), and may therefore be chosen to be the zero envelope.  Successor
index `i + 1` is represented by `G i (P i) (Y i)`, centred in the coordinate
`Y i`.  Equality of all laws `mu.map (Y i) = nu` permits one aggregate
application of Rio's interpolation theorem.-/
theorem conditionalValueAtRisk_finiteSupremum_le_rio_of_centeredGhostFibers
    (filtration : Filtration ℕ mOmega)
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    [SigmaFiniteFiltration mu filtration]
    [StandardBorelSpace Z] [Nonempty Z] [IsProbabilityMeasure nu]
    (s : Finset T) (hs : s.Nonempty) (X : T → Omega → ℝ)
    (B : Omega → ℝ) (hB : Integrable B mu)
    (hX : ∀ u ∈ s, Measurable (X u))
    (hdom : ∀ omega u, u ∈ s → |X u omega| ≤ |B omega|)
    (P : ℕ → Omega → Beta) (Y : ℕ → Omega → Z)
    (G : ℕ → Beta → Z → ℝ) (Acoord : ℕ → Z → ℝ)
    (n q : ℕ) (hq : 3 ≤ q)
    {V Q y alpha : ℝ} (hV : 0 < V) (hQ : 0 < Q) (hy : 0 < y)
    (hterminal : mu[finiteProcessSupremum s hs X | filtration n]
      =ᵐ[mu] finiteProcessSupremum s hs X)
    (hzero : doobCenteredDifference filtration mu
      (finiteProcessSupremum s hs X) 0 =ᵐ[mu] 0)
    (hPY : ∀ i < n, IndepFun (P i) (Y i) mu)
    (hP : ∀ i < n, Measurable (P i))
    (hY : ∀ i < n, Measurable (Y i))
    (hYlaw : ∀ i < n, mu.map (Y i) = nu)
    (hfiltration : ∀ i < n,
      filtration i = MeasurableSpace.comap (P i) inferInstance)
    (hG : ∀ i < n, StronglyMeasurable (Function.uncurry (G i)))
    (hAq : ∀ j < n + 1, MemLp (Acoord j) q nu)
    (hA : ∀ j < n + 1, ∀ z, 0 ≤ Acoord j z)
    (hreplace : ∀ i < n, ∀ b z z',
      |G i b z - G i b z'| ≤ Acoord (i + 1) z + Acoord (i + 1) z')
    (hrepresentation : ∀ i < n,
      doobCenteredDifference filtration mu
          (finiteProcessSupremum s hs X) (i + 1) =ᵐ[mu]
        fun omega ↦ G i (P i omega) (Y i omega) -
          ∫ z, G i (P i omega) z ∂(mu.map (Y i)))
    (hsecond :
      (∑ j ∈ Finset.range (n + 1),
        replaceOneCenteredMoment nu (Acoord j) 2) ≤ V)
    (hmomentQ :
      (∑ j ∈ Finset.range (n + 1),
        replaceOneCenteredMoment nu (Acoord j) q) ≤ Q)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hscale : Q * Real.exp (-Real.log alpha) ≤ y ^ q) :
    conditionalValueAtRisk alpha
        (fun omega ↦ finiteProcessSupremum s hs X omega -
          ∫ z, finiteProcessSupremum s hs X z ∂mu) mu ≤
      Real.sqrt (2 * V * (-Real.log alpha)) +
        (1 + 1 / (q : ℝ)) * y +
          Real.exp 1 * strongMomentQScale q Q * (-Real.log alpha) / 3 +
        alpha⁻¹ * (Q / ((q : ℝ) * y ^ (q - 1))) := by
  let F : Omega → ℝ := finiteProcessSupremum s hs X
  let D : ℕ → Omega → ℝ :=
    doobCenteredDifference filtration mu F
  let R : ℕ → Omega → ℝ := fun i omega ↦
    G i (P i omega) (Y i omega) -
      ∫ z, G i (P i omega) z ∂(mu.map (Y i))
  have hzero' : D 0 =ᵐ[mu] 0 := by
    simpa only [D, F] using hzero
  have hrepresentation' : ∀ i < n, D (i + 1) =ᵐ[mu] R i := by
    intro i hi
    simpa only [D, F, R] using hrepresentation i hi
  have hRmem : ∀ i < n, MemLp (R i) q mu := by
    intro i hi
    have hAqMap : MemLp (Acoord (i + 1)) q (mu.map (Y i)) := by
      rw [hYlaw i hi]
      exact hAq (i + 1) (by omega)
    simpa only [R] using memLp_centeredGhostFiber_comp
      (P i) (Y i) (hP i hi) (hY i hi) (G i) (Acoord (i + 1))
        q (by omega) (hG i hi) hAqMap (hA (i + 1) (by omega))
        (hreplace i hi)
  have hDsq : ∀ j < n + 1,
      Integrable (fun omega ↦ D j omega ^ 2) mu := by
    intro j hj
    cases j with
    | zero =>
        have heq : (fun omega ↦ D 0 omega ^ 2) =ᵐ[mu]
            (fun _ ↦ (0 : ℝ)) := by
          filter_upwards [hzero'] with omega homega
          rw [homega]
          norm_num
        exact (integrable_zero Omega ℝ mu).congr heq.symm
    | succ i =>
        have hi : i < n := by omega
        have hqtwo : (2 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
          exact_mod_cast (by omega : 2 ≤ q)
        have hR2 : MemLp (R i) 2 mu :=
          (hRmem i hi).mono_exponent hqtwo
        have hRint : Integrable (fun omega ↦ R i omega ^ 2) mu := by
          simpa only [Real.norm_eq_abs, sq_abs] using
            hR2.integrable_norm_pow (by norm_num : 2 ≠ 0)
        have heq : (fun omega ↦ D (i + 1) omega ^ 2) =ᵐ[mu]
            fun omega ↦ R i omega ^ 2 := by
          filter_upwards [hrepresentation' i hi] with omega homega
          rw [homega]
        exact hRint.congr heq.symm
  have hpow : ∀ j < n + 1, ∀ k ∈ Finset.Icc 2 q,
      Integrable (fun omega ↦ (max (D j omega) 0) ^ k) mu := by
    intro j hj k hk
    have hkIcc := Finset.mem_Icc.mp hk
    have hkpos : k ≠ 0 := by omega
    cases j with
    | zero =>
        have heq : (fun omega ↦ (max (D 0 omega) 0) ^ k) =ᵐ[mu]
            (fun _ ↦ (0 : ℝ)) := by
          filter_upwards [hzero'] with omega homega
          simp [homega, hkpos]
        exact (integrable_zero Omega ℝ mu).congr heq.symm
    | succ i =>
        have hi : i < n := by omega
        have hkq : (k : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
          exact_mod_cast (Finset.mem_Icc.mp hk).2
        have hRk : MemLp (R i) k mu :=
          (hRmem i hi).mono_exponent hkq
        have hRint : Integrable (fun omega ↦ (max (R i omega) 0) ^ k) mu := by
          simpa only [Real.norm_eq_abs,
            abs_of_nonneg (le_max_right (R i _) 0)] using
              hRk.pos_part.integrable_norm_pow hkpos
        have heq : (fun omega ↦ (max (D (i + 1) omega) 0) ^ k)
            =ᵐ[mu] fun omega ↦ (max (R i omega) 0) ^ k := by
          filter_upwards [hrepresentation' i hi] with omega homega
          rw [homega]
        exact hRint.congr heq.symm
  have hsecond0 : (∫ omega, D 0 omega ^ 2 ∂mu) ≤
      replaceOneCenteredMoment nu (Acoord 0) 2 := by
    have heq : (fun omega ↦ D 0 omega ^ 2) =ᵐ[mu]
        (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [hzero'] with omega homega
      rw [homega]
      norm_num
    rw [integral_congr_ae heq, integral_zero]
    unfold replaceOneCenteredMoment
    exact integral_nonneg fun z ↦ pow_nonneg
      (replaceOneCenteredEnvelope_nonneg
        (Acoord 0) (hA 0 (by omega)) z) 2
  have hsecondSucc : ∀ i < n,
      mu[fun omega ↦ D (i + 1) omega ^ 2 | filtration i] ≤ᵐ[mu]
        fun _ ↦ replaceOneCenteredMoment nu (Acoord (i + 1)) 2 := by
    intro i hi
    have hAqMap : MemLp (Acoord (i + 1)) q (mu.map (Y i)) := by
      rw [hYlaw i hi]
      exact hAq (i + 1) (by omega)
    have hghost :=
      condExp_sq_doobCenteredDifference_succ_le_of_centeredGhostFiber
        filtration F i (P i) (Y i) (hPY i hi) (hP i hi) (hY i hi)
          (hfiltration i hi) (G i) (Acoord (i + 1)) q (by omega)
          (hG i hi) hAqMap (hA (i + 1) (by omega))
          (hreplace i hi) (hrepresentation' i hi)
    rw [hYlaw i hi] at hghost
    exact hghost
  have hmoment0 : ∀ k ∈ Finset.Icc 2 q,
      (∫ omega, (max (D 0 omega) 0) ^ k ∂mu) ≤
        replaceOneCenteredMoment nu (Acoord 0) k := by
    intro k hk
    have hkIcc := Finset.mem_Icc.mp hk
    have hkpos : k ≠ 0 := by omega
    have heq : (fun omega ↦ (max (D 0 omega) 0) ^ k) =ᵐ[mu]
        (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [hzero'] with omega homega
      simp [homega, hkpos]
    rw [integral_congr_ae heq, integral_zero]
    unfold replaceOneCenteredMoment
    exact integral_nonneg fun z ↦ pow_nonneg
      (replaceOneCenteredEnvelope_nonneg
        (Acoord 0) (hA 0 (by omega)) z) k
  have hmomentSucc : ∀ i < n, ∀ k ∈ Finset.Icc 2 q,
      mu[fun omega ↦ (max (D (i + 1) omega) 0) ^ k | filtration i]
        ≤ᵐ[mu] fun _ ↦
          replaceOneCenteredMoment nu (Acoord (i + 1)) k := by
    intro i hi k hk
    have hAqMap : MemLp (Acoord (i + 1)) q (mu.map (Y i)) := by
      rw [hYlaw i hi]
      exact hAq (i + 1) (by omega)
    have hghost :=
      condExp_pow_max_doobCenteredDifference_succ_le_of_centeredGhostFiber
        filtration F i (P i) (Y i) (hPY i hi) (hP i hi) (hY i hi)
          (hfiltration i hi) (G i) (Acoord (i + 1)) q k
          (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
          (hG i hi) hAqMap (hA (i + 1) (by omega))
          (hreplace i hi) (hrepresentation' i hi)
    rw [hYlaw i hi] at hghost
    exact hghost
  have hmiddle : ∀ k ∈ Finset.Ico 3 q,
      (∑ j ∈ Finset.range (n + 1),
        replaceOneCenteredMoment nu (Acoord j) k) ≤
          interpolatedStrongMomentCoefficient q V Q k := by
    intro k hk
    have hkIco := Finset.mem_Ico.mp hk
    exact sum_replaceOneCenteredMoment_le_interpolatedStrongMomentCoefficient
      (nu := nu) (Finset.range (n + 1)) Acoord q k hq (by omega)
        (by omega) (fun j hj ↦ hAq j (Finset.mem_range.mp hj))
        (fun j hj ↦ hA j (Finset.mem_range.mp hj)) hV.le hQ.le
        hsecond hmomentQ
  apply conditionalValueAtRisk_finiteProcessSupremum_sub_integral_le_rioStrongMoment
    filtration s hs X B hB hX hdom
      (fun j ↦ replaceOneCenteredMoment nu (Acoord j) 2)
      (fun j k ↦ replaceOneCenteredMoment nu (Acoord j) k)
      n q hq hV hQ hy hterminal
  · simpa only [D, F] using hDsq
  · simpa only [D, F] using hpow
  · simpa only [D, F] using hsecond0
  · simpa only [D, F] using hsecondSucc
  · simpa only [D, F] using hmoment0
  · simpa only [D, F] using hmomentSucc
  · exact hsecond
  · exact hmiddle
  · exact hmomentQ
  · exact halpha0
  · exact halpha1
  · exact hscale

end ProbabilityTheory
