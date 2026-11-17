import Tengoku.PaperCLean.PaperC.Probability.ArratiaGoldsteinGordonInput

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 1200000

/-!
# Finite total-variation calculus for Section 13

This file isolates the probability calculus needed after the conditional
Arratia--Goldstein--Gordon estimate has been instantiated:

* total variation for summable real mass functions on `ℕ`;
* the triangle inequality;
* convexity under a finite uniform mixture;
* the coupling inequality for two integer-valued functions on one finite
  probability space;
* the exact algebraic assembly of the finite majorant in Corollary 13.9.

The concrete conditioned start indicators and their dependency graph belong in
`ConditionalAGGInstantiation`.  Keeping the present module independent of that
instantiation prevents the analytic bookkeeping from being entangled with the
coordinate-support proof.
-/

namespace PaperC
namespace SectionThirteenFiniteBound

open scoped BigOperators

open ArratiaGoldsteinGordonInput

noncomputable section

/-! ## Total variation for mass functions on `ℕ` -/

/-- Half-`ℓ¹` total variation for two real mass functions on `ℕ`.-/
noncomputable def natTotalVariation
    (p q : ℕ → ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * ∑' k : ℕ, |p k - q k|

/-- The absolute difference of two summable nonnegative mass functions is
summable.
@isnad1 id=summable.4h2v.s6.585609f0fcaa from=translated src=- shape=7f28e6b9 vocab=7f18a828
-/
theorem summable_abs_sub_of_nonneg
    {p q : ℕ → ℝ}
    (hp : Summable p) (hq : Summable q)
    (hp0 : ∀ k, 0 ≤ p k) (hq0 : ∀ k, 0 ≤ q k) :
    Summable fun k ↦ |p k - q k| := by
  apply (hp.add hq).of_nonneg_of_le
  · intro k
    exact abs_nonneg _
  · intro k
    exact abs_sub_le_iff.mpr
      ⟨by linarith [hp0 k, hq0 k], by linarith [hp0 k, hq0 k]⟩

/-- Total variation is nonnegative whenever its defining series is summable.
@isnad1 id=le.0h2v.s4.1e777a0046be from=translated src=- shape=5a3c7e9d vocab=5cc80388
-/
theorem natTotalVariation_nonneg
    (p q : ℕ → ℝ) :
    0 ≤ natTotalVariation p q := by
  unfold natTotalVariation
  exact mul_nonneg (by positivity)
    (tsum_nonneg fun _ ↦ abs_nonneg _)

/-- Symmetry of half-`ℓ¹` total variation.
@isnad1 id=eq.0h2v.s4.4ece758f74f6 from=translated src=- shape=4b5c2936 vocab=e6ed2902
-/
theorem natTotalVariation_comm
    (p q : ℕ → ℝ) :
    natTotalVariation p q = natTotalVariation q p := by
  unfold natTotalVariation
  congr 1
  apply tsum_congr
  intro k
  exact abs_sub_comm _ _

/-- Triangle inequality for discrete total variation.
@isnad1 id=le.6h3v.s6.b25eb4b6da4b from=translated src=- shape=a5f1a640 vocab=c73756cb
-/
theorem natTotalVariation_triangle
    {p q r : ℕ → ℝ}
    (hp : Summable p) (hq : Summable q) (hr : Summable r)
    (hp0 : ∀ k, 0 ≤ p k)
    (hq0 : ∀ k, 0 ≤ q k)
    (hr0 : ∀ k, 0 ≤ r k) :
    natTotalVariation p r ≤
      natTotalVariation p q + natTotalVariation q r := by
  have hpq :
      Summable fun k ↦ |p k - q k| :=
    summable_abs_sub_of_nonneg hp hq hp0 hq0
  have hqr :
      Summable fun k ↦ |q k - r k| :=
    summable_abs_sub_of_nonneg hq hr hq0 hr0
  have hpr :
      Summable fun k ↦ |p k - r k| :=
    summable_abs_sub_of_nonneg hp hr hp0 hr0
  have hsum :
      (∑' k : ℕ, |p k - r k|) ≤
        ∑' k : ℕ, (|p k - q k| + |q k - r k|) := by
    exact hpr.tsum_le_tsum
      (fun k ↦ by
        calc
          |p k - r k| =
              |(p k - q k) + (q k - r k)| := by ring_nf
          _ ≤ |p k - q k| + |q k - r k| := abs_add_le _ _)
      (hpq.add hqr)
  unfold natTotalVariation
  calc
    (2 : ℝ)⁻¹ * ∑' k : ℕ, |p k - r k| ≤
        (2 : ℝ)⁻¹ *
          ∑' k : ℕ, (|p k - q k| + |q k - r k|) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ =
        (2 : ℝ)⁻¹ * ∑' k : ℕ, |p k - q k| +
          (2 : ℝ)⁻¹ * ∑' k : ℕ, |q k - r k| := by
      rw [hpq.tsum_add hqr]
      ring

/-! ## Uniform finite mixtures -/

/-- Uniform average of a finite family of real numbers.-/
noncomputable def finiteUniformAverage
    {ι : Type*} [Fintype ι] (f : ι → ℝ) : ℝ :=
  (∑ i, f i) / (Fintype.card ι : ℝ)

/--
Convexity of total variation under a finite uniform mixture.  The reference
mass `q` is the same in every component.
@isnad1 id=le.1h3v.s6.e77a8e9f2c91 from=translated src=- shape=2e12046a vocab=c2ca038c
-/
theorem natTotalVariation_uniformMixture_le
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℕ → ℝ) (q : ℕ → ℝ)
    (hsummable :
      ∀ i, Summable fun k ↦ |p i k - q k|) :
    natTotalVariation
        (fun k ↦ finiteUniformAverage (fun i ↦ p i k)) q ≤
      finiteUniformAverage
        (fun i ↦ natTotalVariation (p i) q) := by
  classical
  let d : ℝ := Fintype.card ι
  have hdNat : 0 < Fintype.card ι := Fintype.card_pos
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast hdNat
  have hsumAbs :
      Summable fun k : ℕ ↦
        ∑ i : ι, |p i k - q k| :=
    (hasSum_sum (s := Finset.univ)
      (fun i _hi ↦ (hsummable i).hasSum)).summable
  have hpoint :
      ∀ k : ℕ,
        |finiteUniformAverage (fun i ↦ p i k) - q k| ≤
          finiteUniformAverage (fun i ↦ |p i k - q k|) := by
    intro k
    unfold finiteUniformAverage
    have hsumq :
        (∑ _i : ι, q k) = (Fintype.card ι : ℝ) * q k := by
      simp
    rw [show (∑ i, p i k) / (Fintype.card ι : ℝ) - q k =
        (∑ i, (p i k - q k)) / (Fintype.card ι : ℝ) by
      rw [Finset.sum_sub_distrib, hsumq]
      field_simp]
    rw [abs_div, abs_of_pos hd]
    apply div_le_div_of_nonneg_right
    · exact Finset.abs_sum_le_sum_abs _ _
    · exact hd.le
  have hleftSummable :
      Summable fun k ↦
        |finiteUniformAverage (fun i ↦ p i k) - q k| := by
    have hrightSummable :
        Summable fun k ↦
          finiteUniformAverage (fun i ↦ |p i k - q k|) := by
      unfold finiteUniformAverage
      exact hsumAbs.div_const _
    exact hrightSummable.of_nonneg_of_le
      (fun k ↦ abs_nonneg _) hpoint
  have hrightSummable :
      Summable fun k ↦
        finiteUniformAverage (fun i ↦ |p i k - q k|) := by
    unfold finiteUniformAverage
    exact hsumAbs.div_const _
  have htsum :
      (∑' k : ℕ,
          |finiteUniformAverage (fun i ↦ p i k) - q k|) ≤
        ∑' k : ℕ,
          finiteUniformAverage (fun i ↦ |p i k - q k|) :=
    hleftSummable.tsum_le_tsum hpoint hrightSummable
  have hinterchange :
      (∑' k : ℕ,
          finiteUniformAverage (fun i ↦ |p i k - q k|)) =
        finiteUniformAverage
          (fun i ↦ ∑' k : ℕ, |p i k - q k|) := by
    unfold finiteUniformAverage
    rw [tsum_div_const]
    congr 1
    exact Summable.tsum_finsetSum
      (s := Finset.univ) (fun i _hi ↦ hsummable i)
  unfold natTotalVariation
  calc
    (2 : ℝ)⁻¹ *
          ∑' k : ℕ,
            |finiteUniformAverage (fun i ↦ p i k) - q k| ≤
        (2 : ℝ)⁻¹ *
          ∑' k : ℕ,
            finiteUniformAverage (fun i ↦ |p i k - q k|) :=
      mul_le_mul_of_nonneg_left htsum (by positivity)
    _ =
        (2 : ℝ)⁻¹ *
          finiteUniformAverage
            (fun i ↦ ∑' k : ℕ, |p i k - q k|) := by
      rw [hinterchange]
    _ =
        finiteUniformAverage
          (fun i ↦
            (2 : ℝ)⁻¹ * ∑' k : ℕ, |p i k - q k|) := by
      unfold finiteUniformAverage
      rw [← Finset.mul_sum]
      ring

/-! ## Pushforward laws and the coupling inequality -/

/-- Law of an integer-valued function on a finite probability space.-/
noncomputable def finiteNatLaw
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → ℕ) (k : ℕ) : ℝ := by
  classical
  exact ∑ ω, if Z ω = k then μ.prob ω else 0

/-- The pushforward law is nonnegative.
@isnad1 id=le.0h4v.s4.624dc57d67e8 from=translated src=- shape=f7570c3b vocab=f0717a0a
-/
theorem finiteNatLaw_nonneg
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → ℕ) (k : ℕ) :
    0 ≤ finiteNatLaw μ Z k := by
  classical
  unfold finiteNatLaw
  exact Finset.sum_nonneg fun ω _ ↦ by
    split_ifs
    · exact μ.nonneg ω
    · exact le_rfl

/-- The pushforward mass function has total mass one.
@isnad1 id=hassum.0h3v.s5.30b2881366c0 from=translated src=- shape=fa021149 vocab=498e0dd0
-/
theorem hasSum_finiteNatLaw
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → ℕ) :
    HasSum (finiteNatLaw μ Z) 1 := by
  classical
  let support : Finset ℕ := Finset.univ.image Z
  have hout :
      ∀ k ∉ support, finiteNatLaw μ Z k = 0 := by
    intro k hk
    unfold finiteNatLaw
    apply Finset.sum_eq_zero
    intro ω _hω
    rw [ite_eq_right]
    intro hZ
    apply hk
    exact Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, hZ⟩
  have hsum :
      ∑ k ∈ support, finiteNatLaw μ Z k = 1 := by
    unfold finiteNatLaw
    rw [Finset.sum_comm]
    calc
      (∑ ω, ∑ k ∈ support, if Z ω = k then μ.prob ω else 0) =
          ∑ ω, μ.prob ω := by
        apply Finset.sum_congr rfl
        intro ω _hω
        have hmem : Z ω ∈ support :=
          Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩
        simp [hmem]
      _ = 1 := μ.sum_prob
  have hfinite :
      HasSum (finiteNatLaw μ Z)
        (∑ k ∈ support, finiteNatLaw μ Z k) :=
    hasSum_sum_of_ne_finset_zero hout
  rw [hsum] at hfinite
  exact hfinite

/-- The pushforward mass function is summable.
@isnad1 id=summable.0h3v.s4.858491089f2d from=translated src=- shape=d5911700 vocab=d24fce07
-/
theorem summable_finiteNatLaw
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z : Ω → ℕ) :
    Summable (finiteNatLaw μ Z) :=
  (hasSum_finiteNatLaw μ Z).summable

/-- Probability that two coupled integer-valued variables disagree.-/
noncomputable def disagreementProbability
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z W : Ω → ℕ) : ℝ := by
  classical
  exact ∑ ω, if Z ω ≠ W ω then μ.prob ω else 0

/--
Coupling inequality: total variation between two pushforward laws is bounded
by the probability that the coupled variables differ.
@isnad1 id=le.0h4v.s5.876f73016114 from=translated src=- shape=83a615c1 vocab=e6401a3a
-/
theorem natTotalVariation_finiteNatLaw_le_disagreement
    {Ω : Type*} [Fintype Ω]
    (μ : FinitePMF Ω) (Z W : Ω → ℕ) :
    natTotalVariation (finiteNatLaw μ Z) (finiteNatLaw μ W) ≤
      disagreementProbability μ Z W := by
  classical
  let support : Finset ℕ :=
    Finset.univ.image Z ∪ Finset.univ.image W
  have hout :
      ∀ k ∉ support,
        |finiteNatLaw μ Z k - finiteNatLaw μ W k| = 0 := by
    intro k hk
    have hkZ : k ∉ Finset.univ.image Z := by
      intro h
      exact hk (Finset.mem_union_left _ h)
    have hkW : k ∉ Finset.univ.image W := by
      intro h
      exact hk (Finset.mem_union_right _ h)
    have hZ : finiteNatLaw μ Z k = 0 := by
      unfold finiteNatLaw
      apply Finset.sum_eq_zero
      intro ω _hω
      rw [ite_eq_right]
      intro heq
      exact hkZ (Finset.mem_image.mpr
        ⟨ω, Finset.mem_univ _, heq⟩)
    have hW : finiteNatLaw μ W k = 0 := by
      unfold finiteNatLaw
      apply Finset.sum_eq_zero
      intro ω _hω
      rw [ite_eq_right]
      intro heq
      exact hkW (Finset.mem_image.mpr
        ⟨ω, Finset.mem_univ _, heq⟩)
    rw [hZ, hW, sub_zero, abs_zero]
  have hpoint :
      ∀ k,
        |finiteNatLaw μ Z k - finiteNatLaw μ W k| ≤
          ∑ ω,
            |(if Z ω = k then μ.prob ω else 0) -
              (if W ω = k then μ.prob ω else 0)| := by
    intro k
    unfold finiteNatLaw
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hfinite :
      ∑ k ∈ support,
          |finiteNatLaw μ Z k - finiteNatLaw μ W k| ≤
        ∑ k ∈ support, ∑ ω,
          |(if Z ω = k then μ.prob ω else 0) -
            (if W ω = k then μ.prob ω else 0)| :=
    Finset.sum_le_sum fun k _hk ↦ hpoint k
  have hswap :
      (∑ k ∈ support, ∑ ω,
          |(if Z ω = k then μ.prob ω else 0) -
            (if W ω = k then μ.prob ω else 0)|) =
        2 * disagreementProbability μ Z W := by
    rw [Finset.sum_comm]
    unfold disagreementProbability
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ω _hω
    by_cases hZW : Z ω = W ω
    · simp [hZW]
    · have hZmem : Z ω ∈ support := by
        exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩)
      have hWmem : W ω ∈ support := by
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨ω, Finset.mem_univ _, rfl⟩)
      have hμ : 0 ≤ μ.prob ω := μ.nonneg ω
      rw [ite_eq_left hZW]
      have hterm :
          ∀ k : ℕ,
            |(if Z ω = k then μ.prob ω else 0) -
                (if W ω = k then μ.prob ω else 0)| =
              (if Z ω = k then μ.prob ω else 0) +
                (if W ω = k then μ.prob ω else 0) := by
        intro k
        by_cases hkZ : Z ω = k
        · have hkW : W ω ≠ k := by
            intro hkW
            exact hZW (hkZ.trans hkW.symm)
          simp [hkZ, hkW, abs_of_nonneg hμ]
        · by_cases hkW : W ω = k
          · simp [hkZ, hkW, abs_of_nonneg hμ]
          · simp [hkZ, hkW]
      calc
        (∑ k ∈ support,
            |(if Z ω = k then μ.prob ω else 0) -
              (if W ω = k then μ.prob ω else 0)|) =
            (∑ k ∈ support, (
                (if Z ω = k then μ.prob ω else 0) +
                  (if W ω = k then μ.prob ω else 0))) := by
          exact Finset.sum_congr rfl
            (fun k _hk ↦ hterm k)
        _ =
            (∑ k ∈ support,
                (if Z ω = k then μ.prob ω else 0)) +
              (∑ k ∈ support,
                (if W ω = k then μ.prob ω else 0)) := by
          rw [Finset.sum_add_distrib]
        _ = μ.prob ω + μ.prob ω := by
          simp [hZmem, hWmem]
        _ = 2 * μ.prob ω := by
          ring
  unfold natTotalVariation
  rw [tsum_eq_sum hout]
  rw [hswap] at hfinite
  have hhalf : (2 : ℝ)⁻¹ * 2 = 1 := by norm_num
  calc
    (2 : ℝ)⁻¹ *
        ∑ k ∈ support,
          |finiteNatLaw μ Z k - finiteNatLaw μ W k| ≤
      (2 : ℝ)⁻¹ * (2 * disagreementProbability μ Z W) :=
        mul_le_mul_of_nonneg_left hfinite (by positivity)
    _ = disagreementProbability μ Z W := by ring

/-! ## Algebraic Corollary 13.9 envelope -/

/--
Abstract finite assembly behind Corollary 13.9.

The four inputs correspond respectively to:

* coupling away the bad starts;
* the conditional AGG estimate after averaging;
* coupling the two Poisson parameters;
* finite upper bounds for those three contributions.

This theorem is deliberately independent of the concrete cylinder
instantiation.
@isnad1 id=le.11h8v.s7.d7ac91772f25 from=translated src=- shape=d65718f5 vocab=60054153
-/
theorem finite_corollary_thirteen_nine
    {fullLaw goodLaw targetPoisson goodPoisson : ℕ → ℝ}
    {badMass bOne averageBTwo parameterShift : ℝ}
    (hfull : Summable fullLaw)
    (hgood : Summable goodLaw)
    (htarget : Summable targetPoisson)
    (hgoodPoisson : Summable goodPoisson)
    (hfull0 : ∀ k, 0 ≤ fullLaw k)
    (hgood0 : ∀ k, 0 ≤ goodLaw k)
    (htarget0 : ∀ k, 0 ≤ targetPoisson k)
    (hgoodPoisson0 : ∀ k, 0 ≤ goodPoisson k)
    (hbad :
      natTotalVariation fullLaw goodLaw ≤ badMass)
    (hagg :
      natTotalVariation goodLaw goodPoisson ≤
        2 * (bOne + averageBTwo))
    (hparameter :
      natTotalVariation goodPoisson targetPoisson ≤
        parameterShift) :
    natTotalVariation fullLaw targetPoisson ≤
      badMass + 2 * (bOne + averageBTwo) + parameterShift := by
  have hfirst :=
    natTotalVariation_triangle
      hfull hgood htarget hfull0 hgood0 htarget0
  have hsecond :=
    natTotalVariation_triangle
      hgood hgoodPoisson htarget
      hgood0 hgoodPoisson0 htarget0
  linarith

/--
Numerator-level version of the exact Section 13 majorant.

It records all constants instead of hiding them in `≪_C`.  In the concrete
application:

* `weightedBad = M_B`;
* `badCount = #D_Y`;
* `edgeCount = E_Y`;
* `pairDefect = R₂(N,L)`;
* `localPairs` is the ordered touching population (at most `2N`).
@isnad1 id=le.15h16v.s8.cb4f346242a2 from=translated src=- shape=4a0ef29d vocab=c901160c
-/
theorem finite_corollary_thirteen_nine_of_component_bounds
    {fullLaw goodLaw targetPoisson goodPoisson : ℕ → ℝ}
    {badMass bOne averageBTwo parameterShift : ℝ}
    {weightedBad badCount dyadicSize edgeCount
      localPairs pairDefect : ℝ}
    {twoPowL twoPowTwoL : ℝ}
    (hfull : Summable fullLaw)
    (hgood : Summable goodLaw)
    (htarget : Summable targetPoisson)
    (hgoodPoisson : Summable goodPoisson)
    (hfull0 : ∀ k, 0 ≤ fullLaw k)
    (hgood0 : ∀ k, 0 ≤ goodLaw k)
    (htarget0 : ∀ k, 0 ≤ targetPoisson k)
    (hgoodPoisson0 : ∀ k, 0 ≤ goodPoisson k)
    (hbadCoupling :
      natTotalVariation fullLaw goodLaw ≤ badMass)
    (hagg :
      natTotalVariation goodLaw goodPoisson ≤
        2 * (bOne + averageBTwo))
    (hparameterCoupling :
      natTotalVariation goodPoisson targetPoisson ≤
        parameterShift)
    (hbad :
      badMass ≤ (2 * weightedBad + badCount) / twoPowL)
    (hbOne :
      bOne ≤ (dyadicSize + edgeCount) / twoPowTwoL)
    (hbTwo :
      averageBTwo ≤
        (localPairs + edgeCount + pairDefect) / twoPowTwoL)
    (hparameter :
      parameterShift ≤ badCount / twoPowL) :
    natTotalVariation fullLaw targetPoisson ≤
      (2 * weightedBad + 2 * badCount) / twoPowL +
        2 * (dyadicSize + localPairs +
          2 * edgeCount + pairDefect) / twoPowTwoL := by
  have hbase :=
    finite_corollary_thirteen_nine
      hfull hgood htarget hgoodPoisson
      hfull0 hgood0 htarget0 hgoodPoisson0
      hbadCoupling hagg hparameterCoupling
  calc
    natTotalVariation fullLaw targetPoisson ≤
        badMass + 2 * (bOne + averageBTwo) +
          parameterShift := hbase
    _ ≤
        (2 * weightedBad + badCount) / twoPowL +
          2 *
            ((dyadicSize + edgeCount) / twoPowTwoL +
              (localPairs + edgeCount + pairDefect) /
                twoPowTwoL) +
          badCount / twoPowL := by
      gcongr
    _ =
        (2 * weightedBad + 2 * badCount) / twoPowL +
          2 * (dyadicSize + localPairs +
            2 * edgeCount + pairDefect) / twoPowTwoL := by
      ring

end

end SectionThirteenFiniteBound
end PaperC
