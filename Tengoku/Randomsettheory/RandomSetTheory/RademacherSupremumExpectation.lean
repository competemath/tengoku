/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteSymmetrization
import Tengoku.Randomsettheory.RandomSetTheory.GhostDifferenceIndependence
import Tengoku.Randomsettheory.RandomSetTheory.SubgaussianSupremumExpectation
import Tengoku.Randomsettheory.RandomSetTheory.QuadraticEnvelopeExpectation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Expected suprema of conditionally Rademacher processes

This file isolates the genuinely sub-Gaussian part of empirical-process
symmetrization.  The observations are frozen: only an independent family of
Rademacher signs is random.  Consequently no sub-Gaussian assumption is made
on the original observations.

If deterministic paths `F i` vanish at the origin and have Lipschitz
constants `A i`, chaining gives

`E_epsilon sup_u |c * sum_i epsilon_i F_i(u)|
    <= 84 * c * sqrt (sum_i A_i^2) * sqrt (dim(E) + 1)`.

The second half of the file supplies the missing measure-theoretic layer:
finite ghost-sample Jensen reduction, invariance under random signs, Fubini,
and passage from dense finite prefixes to a separable continuous class.  The
final endpoint bounds the original centred empirical supremum by
`168 * K₂ / sqrt(n) * sqrt(dim(E) + 1)` without assuming that the original
process is sub-Gaussian.
-/

open Filter Real Set Finset MeasureTheory Module TopologicalSpace
open scoped BigOperators ProbabilityTheory ENNReal NNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}

/-- A sub-Gaussian MGF certificate remains valid after enlarging its variance
proxy.  This elementary monotonicity lemma is useful when deterministic
Lipschitz bounds replace the exact sum of squared Rademacher coefficients.
@isnad1 id=hassubga.2h5v.s5.d042e459cd7e from=translated src=- shape=91ead777 vocab=66404da1
-/
theorem HasSubgaussianMGF.mono_proxy
    {X : Omega → ℝ} {c d : ℝ≥0}
    (hX : HasSubgaussianMGF X c mu) (hcd : c ≤ d) :
    HasSubgaussianMGF X d mu := by
  refine ⟨hX.integrable_exp_mul, ?_⟩
  intro t
  refine (hX.mgf_le t).trans ?_
  apply Real.exp_le_exp.mpr
  have hcdReal : (c : ℝ) ≤ (d : ℝ) := by exact_mod_cast hcd
  nlinarith [mul_le_mul_of_nonneg_right hcdReal (sq_nonneg t)]

/-- A finite Rademacher sum of deterministic Lipschitz paths.-/
def rademacherLipschitzProcess
    {ι T : Type*} (epsilon : ι → Omega → ℝ)
    (F : ι → T → ℝ) (I : Finset ι) (c : ℝ)
    (omega : Omega) (t : T) : ℝ :=
  c * ∑ i ∈ I, epsilon i omega * F i t

omit [MeasurableSpace Omega] in
/--
@isnad1 id=eq.0h10v.s6.419ef6f299c6 from=translated src=- shape=c32d56a1 vocab=50dbccf8
-/
theorem rademacherLipschitzProcess_sub
    {ι T : Type*} (epsilon : ι → Omega → ℝ)
    (F : ι → T → ℝ) (I : Finset ι) (c : ℝ)
    (omega : Omega) (s t : T) :
    rademacherLipschitzProcess epsilon F I c omega s -
        rademacherLipschitzProcess epsilon F I c omega t =
      ∑ i ∈ I, (c * (F i s - F i t)) * epsilon i omega := by
  simp only [rademacherLipschitzProcess]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

omit [MeasurableSpace Omega] in
/--
@isnad1 id=eq.1h8v.s6.0a9edb3261e8 from=translated src=- shape=d48a1dd5 vocab=356d3e70
-/
@[simp]
theorem rademacherLipschitzProcess_zero
    {ι T : Type*} [Zero T]
    (epsilon : ι → Omega → ℝ) (F : ι → T → ℝ)
    (I : Finset ι) (c : ℝ) (hzero : ∀ i ∈ I, F i 0 = 0)
    (omega : Omega) :
    rademacherLipschitzProcess epsilon F I c omega 0 = 0 := by
  unfold rademacherLipschitzProcess
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro i hi
  rw [hzero i hi, mul_zero]

/-- Squared real scale packaged as a nonnegative variance proxy.-/
def rademacherLipschitzProxy (x : ℝ) : ℝ≥0 := ⟨x ^ 2, sq_nonneg x⟩

/--
@isnad1 id=eq.0h1v.s4.b6813d0cd6e0 from=translated src=- shape=292bf1f0 vocab=e6f4187d
-/
@[simp]
theorem coe_rademacherLipschitzProxy (x : ℝ) :
    (rademacherLipschitzProxy x : ℝ) = x ^ 2 := rfl

/-! ## The finite-dimensional random-sign bridge -/

/-- Absolute maximum of a vector whose coordinates are indexed by a
nonempty finite set.-/
def finiteVectorSupAbs {T : Type*} (N : Finset T) (hN : N.Nonempty)
    (v : N → ℝ) : ℝ := by
  letI : Nonempty N := hN.to_subtype
  exact Finset.univ.sup' Finset.univ_nonempty fun t ↦ |v t|

omit [MeasurableSpace Omega] in
/-- Rewrite the subtype-indexed finite vector maximum as a maximum over the
original finset.
@isnad1 id=eq.1h3v.s6.22353eb522ea from=translated src=- shape=6348a251 vocab=5274a0ab
-/
theorem finiteVectorSupAbs_eq_sup' {T : Type*}
    (N : Finset T) (hN : N.Nonempty) (f : T → ℝ) :
    finiteVectorSupAbs N hN (fun t ↦ f t) =
      N.sup' hN (fun t ↦ |f t|) := by
  letI : Nonempty N := hN.to_subtype
  unfold finiteVectorSupAbs
  apply le_antisymm
  · apply Finset.sup'_le Finset.univ_nonempty
    intro t ht
    exact Finset.le_sup' (fun u ↦ |f u|) t.property
  · apply Finset.sup'_le hN
    intro t ht
    exact Finset.le_sup' (fun u : N ↦ |f u|)
      (Finset.mem_univ (⟨t, ht⟩ : N))

/-- Measurability of the absolute maximum functional on a finite vector.
@isnad1 id=measurab.1h2v.s6.7167b788a1fa from=translated src=- shape=9614d565 vocab=7f49f1a8
-/
theorem measurable_finiteVectorSupAbs {T : Type*}
    (N : Finset T) (hN : N.Nonempty) :
    Measurable (finiteVectorSupAbs N hN) := by
  letI : Nonempty N := hN.to_subtype
  unfold finiteVectorSupAbs
  have h : Measurable
      ((Finset.univ : Finset N).sup' Finset.univ_nonempty
        (fun t ↦ fun v : N → ℝ ↦ |v t|)) := by
    apply Finset.measurable_sup' Finset.univ_nonempty
    intro t ht
    exact (measurable_pi_apply t).abs
  convert h using 1
  funext v
  exact (Finset.sup'_apply Finset.univ_nonempty
    (fun t ↦ fun w : N → ℝ ↦ |w t|) v).symm

/-- Integrating independent symmetric process coordinates is unchanged by
independent random signs, for every fixed finite restriction.

This is the expectation-level Fubini bridge needed after the ghost-sample
step.  The signs may live on an arbitrary probability space and need only
take the values `+1` and `-1` pointwise.  `hJointInt` is the exact hypothesis
which justifies exchanging the data and sign integrals.
@isnad1 id=eq.5h10v.s8.dcd2ede46b8f from=translated src=- shape=17844089 vocab=00f90a2a
-/
theorem integral_finiteVectorSupAbs_sum_eq_iterated_randomSigns
    {OmegaData OmegaSign T ι : Type*}
    [MeasurableSpace OmegaData] [MeasurableSpace OmegaSign]
    [Countable ι]
    {muData : Measure OmegaData} {muSign : Measure OmegaSign}
    [IsProbabilityMeasure muData] [IsProbabilityMeasure muSign]
    (D : ι → OmegaData → T → ℝ)
    (N : Finset T) (hN : N.Nonempty)
    (I : Finset ι)
    (hDindep : iIndepFun (fun i x (t : N) ↦ D i x t) muData)
    (hDsymm : ∀ i, HasSymmetricFiniteLaw (D i) N muData)
    (epsilon : OmegaSign → ι → ℝ)
    (hepsilon : ∀ eta i, epsilon eta i = 1 ∨ epsilon eta i = -1)
    (hJointInt : Integrable (fun p : OmegaData × OmegaSign ↦
      finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, epsilon p.2 i * D i p.1 t))
      (muData.prod muSign)) :
    (∫ x, finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, D i x t) ∂muData) =
      ∫ x, ∫ eta, finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, epsilon eta i * D i x t) ∂muSign ∂muData := by
  let Phi : (N → ℝ) → ℝ := finiteVectorSupAbs N hN
  let J : OmegaData × OmegaSign → ℝ := fun p ↦
    Phi (fun t ↦ ∑ i ∈ I, epsilon p.2 i * D i p.1 t)
  let L : ℝ := ∫ x, Phi (fun t ↦ ∑ i ∈ I, D i x t) ∂muData
  have hPhi : Measurable Phi := measurable_finiteVectorSupAbs N hN
  have hfixed : ∀ eta,
      L = ∫ x, J (x, eta) ∂muData := by
    intro eta
    have hid := identDistrib_finiteProcessSum_randomSigns_conditionally
      D N hDindep hDsymm epsilon hepsilon I eta
    have hcomp := hid.comp hPhi
    simpa only [L, J, Phi, Function.comp_apply] using hcomp.integral_eq
  calc
    (∫ x, finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, D i x t) ∂muData) = L := rfl
    _ = ∫ eta, L ∂muSign := by
      rw [integral_const, probReal_univ, one_smul]
    _ = ∫ eta, ∫ x, J (x, eta) ∂muData ∂muSign := by
      apply integral_congr_ae
      exact ae_of_all muSign fun eta ↦ hfixed eta
    _ = ∫ p, J p ∂(muData.prod muSign) :=
      (integral_prod_symm J hJointInt).symm
    _ = ∫ x, ∫ eta, J (x, eta) ∂muSign ∂muData :=
      integral_prod J hJointInt
    _ = ∫ x, ∫ eta, finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, epsilon eta i * D i x t) ∂muSign ∂muData := rfl

/-- Finite-class Jensen ghost reduction for expected absolute suprema.

For each fixed sample `x`, the centred empirical vector is the integral of
its difference with an independent ghost copy.  Convexity of the finite
maximum of absolute coordinates then gives the displayed inequality.  The
two integrability hypotheses are exactly those needed for Jensen/Fubini and
are typically discharged by a finite sum of scalar envelopes.
@isnad1 id=le.4h7v.s9.4d5ade6c7cb9 from=translated src=- shape=25f332ad vocab=be90a756
-/
theorem integral_finiteVectorSupAbs_centeredSum_le_ghostDifference
    {OmegaData T ι : Type*} [MeasurableSpace OmegaData]
    [Countable ι]
    {muData : Measure OmegaData} [IsProbabilityMeasure muData]
    (X : ι → OmegaData → T → ℝ)
    (N : Finset T) (hN : N.Nonempty) (I : Finset ι)
    (hXint : ∀ i ∈ I, ∀ t : N, Integrable (fun x ↦ X i x t) muData)
    (hCenteredInt : Integrable (fun x ↦
      finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, (X i x t - ∫ y, X i y t ∂muData))) muData)
    (hGhostInt : Integrable (fun p : OmegaData × OmegaData ↦
      finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, (X i p.1 t - X i p.2 t)))
      (muData.prod muData)) :
    (∫ x, finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, (X i x t - ∫ y, X i y t ∂muData)) ∂muData) ≤
      ∫ p, finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, (X i p.1 t - X i p.2 t)) ∂(muData.prod muData) := by
  let C : OmegaData → N → ℝ := fun x t ↦
    ∑ i ∈ I, (X i x t - ∫ y, X i y t ∂muData)
  let D : OmegaData × OmegaData → N → ℝ := fun p t ↦
    ∑ i ∈ I, (X i p.1 t - X i p.2 t)
  let Phi : (N → ℝ) → ℝ := finiteVectorSupAbs N hN
  have hfiber := hGhostInt.prod_right_ae
  have hpoint : ∀ᵐ x ∂muData,
      Phi (C x) ≤ ∫ y, Phi (D (x, y)) ∂muData := by
    filter_upwards [hfiber] with x hfiberx
    letI : Nonempty N := hN.to_subtype
    unfold Phi finiteVectorSupAbs
    apply Finset.sup'_le Finset.univ_nonempty
    intro t ht
    have hDiffInt : Integrable (fun y ↦ D (x, y) t) muData := by
      apply integrable_finsetSum I
      intro i hi
      exact (integrable_const (X i x t)).sub (hXint i hi t)
    have hcenterEq : C x t = ∫ y, D (x, y) t ∂muData := by
      dsimp only [C, D]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_sub (integrable_const _) (hXint i hi t),
          integral_const, probReal_univ, one_smul]
      · intro i hi
        exact (integrable_const (X i x t)).sub (hXint i hi t)
    have habsInt : Integrable (fun y ↦ |D (x, y) t|) muData := hDiffInt.abs
    have hcoordLe : ∀ y, |D (x, y) t| ≤
        Finset.univ.sup' Finset.univ_nonempty (fun u ↦ |D (x, y) u|) := by
      intro y
      exact Finset.le_sup' (fun u ↦ |D (x, y) u|) (Finset.mem_univ t)
    calc
      |C x t| = |∫ y, D (x, y) t ∂muData| := by rw [hcenterEq]
      _ ≤ ∫ y, |D (x, y) t| ∂muData := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (fun y ↦ D (x, y) t))
      _ ≤ ∫ y, Finset.univ.sup' Finset.univ_nonempty
            (fun u ↦ |D (x, y) u|) ∂muData :=
        integral_mono habsInt hfiberx hcoordLe
  have hInnerInt : Integrable
      (fun x ↦ ∫ y, Phi (D (x, y)) ∂muData) muData :=
    hGhostInt.integral_prod_left
  have hmono : (∫ x, Phi (C x) ∂muData) ≤
      ∫ x, ∫ y, Phi (D (x, y)) ∂muData ∂muData :=
    integral_mono_ae hCenteredInt hInnerInt hpoint
  calc
    (∫ x, finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, (X i x t - ∫ y, X i y t ∂muData)) ∂muData) =
        ∫ x, Phi (C x) ∂muData := rfl
    _ ≤ ∫ x, ∫ y, Phi (D (x, y)) ∂muData ∂muData := hmono
    _ = ∫ p, Phi (D p) ∂(muData.prod muData) :=
      integral_integral hGhostInt
    _ = ∫ p, finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, (X i p.1 t - X i p.2 t)) ∂(muData.prod muData) := rfl

/-- Complete finite-class ghost-sample plus random-sign symmetrization.

The only structural independence hypothesis is stated on the paired ghost
process restricted to `N`.  For an independent original sample it follows
by applying independence to the coordinate-pair maps.  Symmetry itself is
proved here from exchangeability of the two ghost copies.
@isnad1 id=le.8h10v.s10.f5a771a338f9 from=translated src=- shape=1e56984f vocab=8933f2b3
-/
theorem integral_finiteVectorSupAbs_centeredSum_le_iterated_randomSigns_of_ghost
    {OmegaData OmegaSign T ι : Type*}
    [MeasurableSpace OmegaData] [MeasurableSpace OmegaSign]
    [Countable ι]
    {muData : Measure OmegaData} {muSign : Measure OmegaSign}
    [IsProbabilityMeasure muData] [IsProbabilityMeasure muSign]
    (X : ι → OmegaData → T → ℝ)
    (N : Finset T) (hN : N.Nonempty) (I : Finset ι)
    (hXmeas : ∀ i, ∀ t ∈ N, Measurable (fun x ↦ X i x t))
    (hXint : ∀ i ∈ I, ∀ t : N, Integrable (fun x ↦ X i x t) muData)
    (hCenteredInt : Integrable (fun x ↦
      finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, (X i x t - ∫ y, X i y t ∂muData))) muData)
    (hGhostInt : Integrable (fun p : OmegaData × OmegaData ↦
      finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, (X i p.1 t - X i p.2 t)))
      (muData.prod muData))
    (hDindep : iIndepFun (fun i p (t : N) ↦
      X i p.1 t - X i p.2 t) (muData.prod muData))
    (epsilon : OmegaSign → ι → ℝ)
    (hepsilon : ∀ eta i, epsilon eta i = 1 ∨ epsilon eta i = -1)
    (hSignedJointInt : Integrable
      (fun z : (OmegaData × OmegaData) × OmegaSign ↦
        finiteVectorSupAbs N hN (fun t ↦
          ∑ i ∈ I, epsilon z.2 i *
            (X i z.1.1 t - X i z.1.2 t)))
      ((muData.prod muData).prod muSign)) :
    (∫ x, finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, (X i x t - ∫ y, X i y t ∂muData)) ∂muData) ≤
      ∫ p, ∫ eta, finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, epsilon eta i *
          (X i p.1 t - X i p.2 t)) ∂muSign ∂(muData.prod muData) := by
  let D : ι → (OmegaData × OmegaData) → T → ℝ :=
    fun i p t ↦ X i p.1 t - X i p.2 t
  have hsymm : ∀ i, HasSymmetricFiniteLaw (D i) N (muData.prod muData) := by
    intro i
    exact hasSymmetricFiniteLaw_ghostDifference (X i) N (hXmeas i)
  have hghost := integral_finiteVectorSupAbs_centeredSum_le_ghostDifference
    X N hN I hXint hCenteredInt hGhostInt
  have hsignEq := integral_finiteVectorSupAbs_sum_eq_iterated_randomSigns
    D N hN I hDindep hsymm epsilon hepsilon hSignedJointInt
  exact hghost.trans_eq hsignEq

/-- User-facing finite symmetrization theorem from independence of the
original process-valued coordinates.  The independence of paired ghost
differences is derived internally by `iIndepFun_finiteProcess_ghostDifference`.
@isnad1 id=le.8h10v.s10.d6bdbf2506a6 from=translated src=- shape=28f6195b vocab=b6ec3cb9
-/
theorem integral_finiteVectorSupAbs_centeredSum_le_iterated_randomSigns
    {OmegaData OmegaSign T ι : Type*}
    [MeasurableSpace OmegaData] [MeasurableSpace OmegaSign]
    [Fintype ι]
    {muData : Measure OmegaData} {muSign : Measure OmegaSign}
    [IsProbabilityMeasure muData] [IsProbabilityMeasure muSign]
    (X : ι → OmegaData → T → ℝ)
    (N : Finset T) (hN : N.Nonempty) (I : Finset ι)
    (hXmeas : ∀ i, Measurable (fun x (t : N) ↦ X i x t))
    (hXindep : iIndepFun (fun i x (t : N) ↦ X i x t) muData)
    (hXint : ∀ i ∈ I, ∀ t : N, Integrable (fun x ↦ X i x t) muData)
    (hCenteredInt : Integrable (fun x ↦
      finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, (X i x t - ∫ y, X i y t ∂muData))) muData)
    (hGhostInt : Integrable (fun p : OmegaData × OmegaData ↦
      finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, (X i p.1 t - X i p.2 t)))
      (muData.prod muData))
    (epsilon : OmegaSign → ι → ℝ)
    (hepsilon : ∀ eta i, epsilon eta i = 1 ∨ epsilon eta i = -1)
    (hSignedJointInt : Integrable
      (fun z : (OmegaData × OmegaData) × OmegaSign ↦
        finiteVectorSupAbs N hN (fun t ↦
          ∑ i ∈ I, epsilon z.2 i *
            (X i z.1.1 t - X i z.1.2 t)))
      ((muData.prod muData).prod muSign)) :
    (∫ x, finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, (X i x t - ∫ y, X i y t ∂muData)) ∂muData) ≤
      ∫ p, ∫ eta, finiteVectorSupAbs N hN (fun t ↦
        ∑ i ∈ I, epsilon eta i *
          (X i p.1 t - X i p.2 t)) ∂muSign ∂(muData.prod muData) := by
  have hscalarMeas : ∀ i, ∀ t ∈ N,
      Measurable (fun x ↦ X i x t) := by
    intro i t ht
    exact (measurable_pi_apply (⟨t, ht⟩ : N)).comp (hXmeas i)
  have hDindep := iIndepFun_finiteProcess_ghostDifference
    X N hXmeas hXindep
  exact integral_finiteVectorSupAbs_centeredSum_le_iterated_randomSigns_of_ghost
    X N hN I hscalarMeas hXint hCenteredInt hGhostInt hDindep
      epsilon hepsilon hSignedJointInt

end ProbabilityTheory

namespace RandomSetTheory

open ProbabilityTheory

variable {Omega E ι : Type*} [MeasurableSpace Omega]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {mu : Measure Omega}

/-- A normalized empirical process centred coordinate by coordinate.-/
def centeredEmpiricalLipschitzProcess
    {OmegaData T : Type*} [MeasurableSpace OmegaData]
    (muData : Measure OmegaData) (n : ℕ)
    (X : Fin n → OmegaData → T → ℝ)
    (x : OmegaData) (t : T) : ℝ :=
  ∑ i : Fin n, ((n : ℝ)⁻¹ * X i x t -
    ∫ y, (n : ℝ)⁻¹ * X i y t ∂muData)

/-- The normalized Rademacher process of paired ghost differences.-/
def rademacherGhostEmpiricalProcess
    {OmegaData OmegaSign T : Type*}
    (n : ℕ) (epsilon : OmegaSign → Fin n → ℝ)
    (X : Fin n → OmegaData → T → ℝ)
    (p : OmegaData × OmegaData) (eta : OmegaSign) (t : T) : ℝ :=
  rademacherLipschitzProcess (fun i eta ↦ epsilon eta i)
    (fun i t ↦ X i p.1 t - X i p.2 t)
    Finset.univ ((n : ℝ)⁻¹) eta t

/-- Uniform expectation bounds for all dense finite prefixes pass to the
absolute supremum of a continuous process.  This is the expectation analogue
of the CVaR dense-prefix bridge.
@isnad1 id=le.5h6v.s7.5e538c447478 from=translated src=- shape=d8c5fdcc vocab=e7d414dd
-/
theorem integral_iSup_abs_le_of_densePrefixBounds
    {T : Type*} [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    (F : Omega → T → ℝ) (B : Omega → ℝ)
    (hcontinuous : ∀ omega, Continuous (F omega))
    (hmeas : ∀ k, Measurable (fun omega ↦ F omega (denseSeq T k)))
    (hB : Integrable B mu)
    (hdom : ∀ omega t, |F omega t| ≤ |B omega|)
    {C : ℝ}
    (hprefix : ∀ n, (∫ omega,
      densePrefixAbsSupremum (F omega) n ∂mu) ≤ C) :
    (∫ omega, (⨆ t : T, |F omega t|) ∂mu) ≤ C := by
  let G : Omega → T → ℝ := fun omega t ↦ |F omega t|
  let P : ℕ → Omega → ℝ := fun n omega ↦
    densePrefixSupremum (G omega) n
  let S : Omega → ℝ := fun omega ↦ ⨆ t, G omega t
  have hGcontinuous : ∀ omega, Continuous (G omega) := fun omega ↦
    (hcontinuous omega).abs
  have hGmeas : ∀ k, Measurable (fun omega ↦ G omega (denseSeq T k)) :=
    fun k ↦ (hmeas k).abs
  have hGdom : ∀ omega t, |G omega t| ≤ |B omega| := by
    intro omega t
    simpa only [G, abs_abs] using hdom omega t
  have hPmeas : ∀ n, Measurable (P n) := fun n ↦
    measurable_densePrefixSupremum G hGmeas n
  have hSmeas : Measurable S :=
    measurable_iSup_continuous_of_measurable_dense G hGcontinuous hGmeas
  have hPdom : ∀ n omega, |P n omega| ≤ |B omega| := by
    intro n omega
    have heq : P n omega = finiteProcessSupremum
        (Finset.range (n + 1)) Finset.nonempty_range_add_one
          (fun k omega ↦ G omega (denseSeq T k)) omega := by
      dsimp only [P, finiteProcessSupremum]
      exact densePrefixSupremum_eq_sup'_range _ n
    rw [heq]
    apply abs_finiteProcessSupremum_le
      (Finset.range (n + 1)) Finset.nonempty_range_add_one
      (fun k omega ↦ G omega (denseSeq T k)) B
    intro omega' k hk
    exact hGdom omega' (denseSeq T k)
  have hSdom : ∀ omega, |S omega| ≤ |B omega| := by
    intro omega
    have hbdd : BddAbove (Set.range (G omega)) := by
      refine ⟨|B omega|, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact (le_abs_self (G omega t)).trans (hGdom omega t)
    have hupper : S omega ≤ |B omega| :=
      ciSup_le fun t ↦ (le_abs_self (G omega t)).trans (hGdom omega t)
    let t0 : T := Classical.choice inferInstance
    have hlowerValue : -|B omega| ≤ G omega t0 :=
      (neg_le_neg (hGdom omega t0)).trans (neg_abs_le (G omega t0))
    have hlower : -|B omega| ≤ S omega :=
      hlowerValue.trans (le_ciSup hbdd t0)
    exact (abs_le).2 ⟨hlower, hupper⟩
  have hPint : ∀ n, Integrable (P n) mu := by
    intro n
    apply hB.abs.mono' (hPmeas n).aestronglyMeasurable
    exact ae_of_all mu fun omega ↦ by
      simpa only [Real.norm_eq_abs, abs_abs] using hPdom n omega
  have hSint : Integrable S mu := by
    apply hB.abs.mono' hSmeas.aestronglyMeasurable
    exact ae_of_all mu fun omega ↦ by
      simpa only [Real.norm_eq_abs, abs_abs] using hSdom omega
  have hL1 := tendsto_integral_abs_densePrefixSupremum_sub_iSup
    G B hGcontinuous hGmeas hB hGdom
  have hdistLe : ∀ n,
      dist (∫ omega, P n omega ∂mu) (∫ omega, S omega ∂mu) ≤
        ∫ omega, |P n omega - S omega| ∂mu := by
    intro n
    rw [Real.dist_eq, ← integral_sub (hPint n) hSint]
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (fun omega ↦ P n omega - S omega))
  have hdistTendsto : Tendsto
      (fun n ↦ dist (∫ omega, P n omega ∂mu)
        (∫ omega, S omega ∂mu)) atTop (nhds 0) := by
    apply squeeze_zero (fun n ↦ dist_nonneg) hdistLe
    simpa only [P, S] using hL1
  have hIntTendsto : Tendsto (fun n ↦ ∫ omega, P n omega ∂mu)
      atTop (nhds (∫ omega, S omega ∂mu)) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact hdistTendsto
  change (∫ omega, S omega ∂mu) ≤ C
  apply le_of_tendsto hIntTendsto
  filter_upwards [] with n
  simpa only [P, G, densePrefixAbsSupremum] using hprefix n

/-- One dense-prefix comparison between the centred empirical process and
the full continuous Rademacher ghost process.  This theorem composes the
finite ghost/sign symmetrization with the elementary inclusion of a finite
dense prefix in the full supremum.
@isnad1 id=le.9h9v.s10.27777691bf57 from=translated src=- shape=00dcf825 vocab=9327bd6b
-/
theorem integral_densePrefixAbs_centeredEmpirical_le_rademacherGhost
    {OmegaData OmegaSign : Type*}
    [MeasurableSpace OmegaData] [MeasurableSpace OmegaSign]
    {muData : Measure OmegaData} {muSign : Measure OmegaSign}
    [IsProbabilityMeasure muData] [IsProbabilityMeasure muSign]
    (n : ℕ) (k : ℕ)
    (epsilon : OmegaSign → Fin n → ℝ)
    (X : Fin n → OmegaData → EuclideanUnitBall E → ℝ)
    (hXmeas : ∀ i t, Measurable (fun x ↦ X i x t))
    (hXint : ∀ i t, Integrable (fun x ↦ X i x t) muData)
    (hXindep : iIndepFun (fun i x
      (j : Finset.range (k + 1)) ↦
        X i x (denseSeq (EuclideanUnitBall E) j)) muData)
    (hepsilon : ∀ eta i, epsilon eta i = 1 ∨ epsilon eta i = -1)
    (hCenteredInt : Integrable (fun x ↦
      densePrefixAbsSupremum
        (centeredEmpiricalLipschitzProcess muData n X x) k) muData)
    (hGhostInt : Integrable
      (fun p : OmegaData × OmegaData ↦
        finiteVectorSupAbs (Finset.range (k + 1))
          Finset.nonempty_range_add_one (fun j ↦
            ∑ i : Fin n, ((n : ℝ)⁻¹ *
              X i p.1 (denseSeq (EuclideanUnitBall E) j) -
              (n : ℝ)⁻¹ *
              X i p.2 (denseSeq (EuclideanUnitBall E) j))))
      (muData.prod muData))
    (hSignedJointInt : Integrable
      (fun z : (OmegaData × OmegaData) × OmegaSign ↦
        finiteVectorSupAbs (Finset.range (k + 1))
          Finset.nonempty_range_add_one (fun j ↦
            ∑ i : Fin n, epsilon z.2 i *
              ((n : ℝ)⁻¹ *
                X i z.1.1 (denseSeq (EuclideanUnitBall E) j) -
               (n : ℝ)⁻¹ *
                X i z.1.2 (denseSeq (EuclideanUnitBall E) j))))
      ((muData.prod muData).prod muSign))
    (hFullSignedJointInt : Integrable
      (fun z : (OmegaData × OmegaData) × OmegaSign ↦
        ⨆ t : EuclideanUnitBall E,
          |rademacherGhostEmpiricalProcess n epsilon X z.1 z.2 t|)
      ((muData.prod muData).prod muSign))
    (hRbdd : ∀ p eta, BddAbove (Set.range fun t : EuclideanUnitBall E ↦
      |rademacherGhostEmpiricalProcess n epsilon X p eta t|)) :
    (∫ x, densePrefixAbsSupremum
        (centeredEmpiricalLipschitzProcess muData n X x) k ∂muData) ≤
      ∫ p, ∫ eta, (⨆ t : EuclideanUnitBall E,
        |rademacherGhostEmpiricalProcess n epsilon X p eta t|)
        ∂muSign ∂(muData.prod muData) := by
  let N : Finset ℕ := Finset.range (k + 1)
  have hN : N.Nonempty := Finset.nonempty_range_add_one
  let Xn : Fin n → OmegaData → ℕ → ℝ := fun i x j ↦
    (n : ℝ)⁻¹ * X i x (denseSeq (EuclideanUnitBall E) j)
  have hXnMeas : ∀ i, Measurable (fun x (j : N) ↦ Xn i x j) := by
    intro i
    apply measurable_pi_lambda
    intro j
    exact measurable_const.mul (hXmeas i _)
  have hXnIndep : iIndepFun (fun i x (j : N) ↦ Xn i x j) muData := by
    have hcomp := hXindep.comp
      (fun _ (v : N → ℝ) j ↦ (n : ℝ)⁻¹ * v j)
      (fun _ ↦ by fun_prop)
    simpa only [N, Xn, Function.comp_def] using hcomp
  have hXnInt : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ j : N,
      Integrable (fun x ↦ Xn i x j) muData := by
    intro i hi j
    exact (hXint i _).const_mul _
  have hGhostInt' : Integrable
      (fun p : OmegaData × OmegaData ↦
        finiteVectorSupAbs N hN (fun j ↦
          ∑ i ∈ (Finset.univ : Finset (Fin n)),
            (Xn i p.1 j - Xn i p.2 j))) (muData.prod muData) := by
    convert hGhostInt using 1
  have hSignedJointInt' : Integrable
      (fun z : (OmegaData × OmegaData) × OmegaSign ↦
        finiteVectorSupAbs N hN (fun j ↦
          ∑ i ∈ (Finset.univ : Finset (Fin n)), epsilon z.2 i *
            (Xn i z.1.1 j - Xn i z.1.2 j)))
      ((muData.prod muData).prod muSign) := by
    convert hSignedJointInt using 1
  have hcenterEq : ∀ x,
      finiteVectorSupAbs N hN (fun j ↦
        ∑ i ∈ (Finset.univ : Finset (Fin n)),
          (Xn i x j - ∫ y, Xn i y j ∂muData)) =
        densePrefixAbsSupremum
          (centeredEmpiricalLipschitzProcess muData n X x) k := by
    intro x
    let fcenter : ℕ → ℝ := fun j ↦
      ∑ i ∈ (Finset.univ : Finset (Fin n)),
        (Xn i x j - ∫ y, Xn i y j ∂muData)
    calc
      finiteVectorSupAbs N hN (fun j ↦
          ∑ i ∈ (Finset.univ : Finset (Fin n)),
            (Xn i x j - ∫ y, Xn i y j ∂muData)) =
          N.sup' hN (fun j ↦ |fcenter j|) :=
        finiteVectorSupAbs_eq_sup' N hN fcenter
      _ = densePrefixAbsSupremum
          (centeredEmpiricalLipschitzProcess muData n X x) k := by
        rw [densePrefixAbsSupremum, densePrefixSupremum_eq_sup'_range]
        apply Finset.sup'_congr hN rfl
        intro j hj
        congr 1
  have hCenteredInt' : Integrable (fun x ↦
      finiteVectorSupAbs N hN (fun j ↦
        ∑ i ∈ (Finset.univ : Finset (Fin n)),
          (Xn i x j - ∫ y, Xn i y j ∂muData))) muData := by
    convert hCenteredInt using 1
    funext x
    exact hcenterEq x
  have hsymm :=
    integral_finiteVectorSupAbs_centeredSum_le_iterated_randomSigns
      Xn N hN Finset.univ hXnMeas hXnIndep hXnInt hCenteredInt'
        hGhostInt' epsilon hepsilon hSignedJointInt'
  have hsignedLe : ∀ z : (OmegaData × OmegaData) × OmegaSign,
      finiteVectorSupAbs N hN (fun j ↦
        ∑ i ∈ (Finset.univ : Finset (Fin n)), epsilon z.2 i *
          (Xn i z.1.1 j - Xn i z.1.2 j)) ≤
        ⨆ t : EuclideanUnitBall E,
          |rademacherGhostEmpiricalProcess n epsilon X z.1 z.2 t| := by
    intro z
    let fsigned : ℕ → ℝ := fun j ↦
      ∑ i ∈ (Finset.univ : Finset (Fin n)), epsilon z.2 i *
        (Xn i z.1.1 j - Xn i z.1.2 j)
    calc
      finiteVectorSupAbs N hN (fun j ↦
          ∑ i ∈ (Finset.univ : Finset (Fin n)), epsilon z.2 i *
            (Xn i z.1.1 j - Xn i z.1.2 j)) =
          N.sup' hN (fun j ↦ |fsigned j|) :=
        finiteVectorSupAbs_eq_sup' N hN fsigned
      _ ≤ ⨆ t : EuclideanUnitBall E,
          |rademacherGhostEmpiricalProcess n epsilon X z.1 z.2 t| := by
        apply Finset.sup'_le hN
        intro j hj
        have hvalue : fsigned j =
            rademacherGhostEmpiricalProcess n epsilon X z.1 z.2
              (denseSeq (EuclideanUnitBall E) j) := by
          simp only [fsigned, rademacherGhostEmpiricalProcess,
            rademacherLipschitzProcess, Xn]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        rw [hvalue]
        exact le_ciSup (hRbdd z.1 z.2) (denseSeq (EuclideanUnitBall E) j)
  have hjointMono :
      (∫ z, finiteVectorSupAbs N hN (fun j ↦
        ∑ i ∈ (Finset.univ : Finset (Fin n)), epsilon z.2 i *
          (Xn i z.1.1 j - Xn i z.1.2 j))
        ∂((muData.prod muData).prod muSign)) ≤
      ∫ z, (⨆ t : EuclideanUnitBall E,
        |rademacherGhostEmpiricalProcess n epsilon X z.1 z.2 t|)
        ∂((muData.prod muData).prod muSign) := by
    exact integral_mono hSignedJointInt' hFullSignedJointInt hsignedLe
  calc
    (∫ x, densePrefixAbsSupremum
        (centeredEmpiricalLipschitzProcess muData n X x) k ∂muData) =
        ∫ x, finiteVectorSupAbs N hN (fun j ↦
          ∑ i ∈ (Finset.univ : Finset (Fin n)),
            (Xn i x j - ∫ y, Xn i y j ∂muData)) ∂muData := by
      apply integral_congr_ae
      exact ae_of_all muData fun x ↦ (hcenterEq x).symm
    _ ≤ ∫ p, ∫ eta, finiteVectorSupAbs N hN (fun j ↦
          ∑ i ∈ (Finset.univ : Finset (Fin n)), epsilon eta i *
            (Xn i p.1 j - Xn i p.2 j)) ∂muSign
          ∂(muData.prod muData) := hsymm
    _ = ∫ z, finiteVectorSupAbs N hN (fun j ↦
          ∑ i ∈ (Finset.univ : Finset (Fin n)), epsilon z.2 i *
            (Xn i z.1.1 j - Xn i z.1.2 j))
          ∂((muData.prod muData).prod muSign) :=
      integral_integral hSignedJointInt'
    _ ≤ ∫ z, (⨆ t : EuclideanUnitBall E,
          |rademacherGhostEmpiricalProcess n epsilon X z.1 z.2 t|)
          ∂((muData.prod muData).prod muSign) := hjointMono
    _ = ∫ p, ∫ eta, (⨆ t : EuclideanUnitBall E,
          |rademacherGhostEmpiricalProcess n epsilon X p eta t|)
          ∂muSign ∂(muData.prod muData) :=
      integral_prod _ hFullSignedJointInt

end RandomSetTheory
