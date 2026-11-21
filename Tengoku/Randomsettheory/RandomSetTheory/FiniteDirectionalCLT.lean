/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.DirectionalCLT
import Tengoku.Seed.Probability.Distributions.Gaussian.Multivariate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-dimensional central limit theorems for random-set support processes

Mathlib's central limit theorem is currently one-dimensional, whereas the
support process of a random set is indexed by a family of directions.  This
file closes the finite-dimensional gap without assuming a vector CLT:

* `euclideanCovarianceMatrix` is the coordinate covariance matrix of a
  Euclidean random vector and is positive semidefinite;
* `tendstoInDistribution_euclidean_inv_sqrt_smul_sum_sub` proves the iid CLT
  in any finite Euclidean space.  Its proof applies the scalar CLT to every
  linear functional and then uses Levy's multivariate convergence theorem;
* `finiteDirectionalSupportDeviation` bundles finitely many centered support
  evaluations into one Euclidean vector;
* `tendstoInDistribution_finiteDirectionalSupport_minkowskiAverage` proves
  joint convergence for those directions, with an explicit covariance
  matrix;
* `tendstoInDistribution_iid_finiteDirectionalSupport_minkowskiAverage`
  transports iid observations through an Effros-measurable compact-valued
  correspondence automatically.

This is genuine convergence of every finite-dimensional distribution.  It is
strictly stronger than separate directional convergence, but it does not
claim tightness in an infinite-dimensional function space; the Donsker step
from Section 5 of the report remains a separate functional-CLT problem.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Real Set MeasureTheory ProbabilityTheory Filter Matrix WithLp
open scoped BigOperators InnerProductSpace ProbabilityTheory Topology
  RealInnerProductSpace MatrixOrder

noncomputable section

namespace RandomSetTheory

variable {Omega : Type*} [MeasurableSpace Omega]
variable {kappa : Type*} [Fintype kappa]

/-- Covariance matrix of a finite-dimensional random vector.-/
def euclideanCovarianceMatrix (X : Omega → EuclideanSpace ℝ kappa)
    (mu : Measure Omega) : Matrix kappa kappa ℝ :=
  fun i j => cov[fun omega => X omega i, fun omega => X omega j; mu]

/--
@isnad1 id=possemid.1h4v.s7.5950046e780b from=translated src=- shape=25737a1a vocab=d938987d
-/
theorem euclideanCovarianceMatrix_posSemidef
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (X : Omega → EuclideanSpace ℝ kappa) (hX : MemLp X 2 mu) :
    (euclideanCovarianceMatrix X mu).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [euclideanCovarianceMatrix, star_trivial]
    exact covariance_comm _ _
  · intro a
    have hcoord : ∀ i, MemLp (fun omega => X omega i) 2 mu := by
      intro i
      simpa only [EuclideanSpace.basisFun_inner] using
        hX.const_inner (𝕜 := ℝ) (EuclideanSpace.basisFun kappa ℝ i)
    have hscaled : ∀ i, MemLp (fun omega => a i * X omega i) 2 mu :=
      fun i => (hcoord i).const_mul (a i)
    calc
      0 ≤ Var[fun omega => ∑ i, a i * X omega i; mu] :=
        variance_nonneg _ _
      _ = cov[fun omega => ∑ i, a i * X omega i,
          fun omega => ∑ j, a j * X omega j; mu] := by
        rw [covariance_self]
        exact Finset.aemeasurable_fun_sum _
          (fun i _ => (hscaled i).aemeasurable)
      _ = ∑ i, ∑ j, cov[fun omega => a i * X omega i,
          fun omega => a j * X omega j; mu] :=
        covariance_fun_sum_fun_sum hscaled hscaled
      _ = star a ⬝ᵥ (euclideanCovarianceMatrix X mu *ᵥ a) := by
        simp only [dotProduct, mulVec, euclideanCovarianceMatrix, star_trivial,
          covariance_const_mul_left, covariance_const_mul_right]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring

/--
@isnad1 id=eq.1h5v.s8.1daf62b263e5 from=translated src=- shape=7d92708a vocab=51e06d2d
-/
theorem euclideanCovarianceMatrix_quadratic_eq_variance
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (X : Omega → EuclideanSpace ℝ kappa) (hX : MemLp X 2 mu)
    (t : EuclideanSpace ℝ kappa) :
    t ⬝ᵥ (euclideanCovarianceMatrix X mu *ᵥ t) =
      Var[fun omega => ⟪t, X omega⟫_ℝ; mu] := by
  classical
  have hcoord : ∀ i, MemLp (fun omega => X omega i) 2 mu := by
    intro i
    simpa only [EuclideanSpace.basisFun_inner] using
      hX.const_inner (𝕜 := ℝ) (EuclideanSpace.basisFun kappa ℝ i)
  have hscaled : ∀ i, MemLp (fun omega => t i * X omega i) 2 mu :=
    fun i => (hcoord i).const_mul (t i)
  have hfun : (fun omega => ⟪t, X omega⟫_ℝ) =
      fun omega => ∑ i, t i * X omega i := by
    funext omega
    simp [PiLp.inner_apply, mul_comm]
  rw [hfun, ← covariance_self]
  · rw [covariance_fun_sum_fun_sum hscaled hscaled]
    simp only [dotProduct, mulVec, euclideanCovarianceMatrix,
      covariance_const_mul_left, covariance_const_mul_right]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · exact Finset.aemeasurable_fun_sum _
      (fun i _ => (hscaled i).aemeasurable)

/--
@isnad1 id=eq.1h5v.s8.93f9de19f934 from=translated src=- shape=5b7d0b2b vocab=ede1fa63
-/
theorem charFun_map_inner_eq_charFun_map_one
    {mu : Measure Omega} (X : Omega → EuclideanSpace ℝ kappa)
    (hX : AEMeasurable X mu) (t : EuclideanSpace ℝ kappa) :
    charFun (mu.map X) t =
      charFun (mu.map (fun omega => ⟪t, X omega⟫_ℝ)) 1 := by
  rw [charFun_apply, integral_map hX (by fun_prop),
    charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
  congr with omega
  simp [real_inner_comm]

/-- Multivariate iid CLT in a finite Euclidean space, obtained from the
one-dimensional CLT and Levy's theorem.
@isnad1 id=tendstoi.4h7v.s9.ceb10a7fe1ed from=translated src=- shape=9349710e vocab=a8d1b4d9
-/
theorem tendstoInDistribution_euclidean_inv_sqrt_smul_sum_sub
    [DecidableEq kappa]
    {Omega' : Type*} [MeasurableSpace Omega']
    {mu : Measure Omega} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure mu']
    (X : ℕ → Omega → EuclideanSpace ℝ kappa)
    (Y : Omega' → EuclideanSpace ℝ kappa)
    (hY : HasLaw Y
      (multivariateGaussian 0 (euclideanCovarianceMatrix (X 0) mu)) mu')
    (hL2 : MemLp (X 0) 2 mu)
    (hindep : iIndepFun X mu)
    (hident : ∀ i, IdentDistrib (X i) (X 0) mu mu) :
    TendstoInDistribution
      (fun (n : ℕ) omega =>
        (√n)⁻¹ •
          (∑ i ∈ Finset.range n, X i omega -
            (n : ℝ) • ∫ omega, X 0 omega ∂mu))
      atTop Y (fun _ => mu) mu' := by
  let Sigma := euclideanCovarianceMatrix (X 0) mu
  have hSigma : Sigma.PosSemidef :=
    euclideanCovarianceMatrix_posSemidef (X 0) hL2
  have hInt : Integrable (X 0) mu := hL2.integrable (by norm_num)
  have hXmeas : ∀ i, AEMeasurable (X i) mu :=
    fun i => (hident i).aemeasurable_fst
  refine
    { forall_aemeasurable := fun n => ?_
      aemeasurable_limit := hY.aemeasurable
      tendsto := ?_ }
  · have hc : AEMeasurable
        (fun _ : Omega => (n : ℝ) • ∫ omega, X 0 omega ∂mu) mu :=
      aemeasurable_const
    exact ((Finset.aemeasurable_fun_sum (Finset.range n)
      (fun i _ => hXmeas i)).sub hc).const_smul ((√n)⁻¹ : ℝ)
  · apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.2
    intro t
    let Xt : ℕ → Omega → ℝ := fun i omega => ⟪t, X i omega⟫_ℝ
    let Yt : Omega' → ℝ := fun omega => ⟪t, Y omega⟫_ℝ
    have hXtL2 : MemLp (Xt 0) 2 mu := hL2.const_inner (𝕜 := ℝ) t
    have hindep_t : iIndepFun Xt mu := by
      simpa only [Xt, Function.comp_def] using
        hindep.comp (fun _ x => ⟪t, x⟫_ℝ) (fun _ => by fun_prop)
    have hident_t : ∀ i, IdentDistrib (Xt i) (Xt 0) mu mu := by
      intro i
      simpa only [Xt, Function.comp_def] using
        (hident i).comp (by fun_prop : Measurable (fun x => ⟪t, x⟫_ℝ))
    have hquad : t ⬝ᵥ (Sigma *ᵥ t) = Var[Xt 0; mu] := by
      simpa only [Sigma, Xt] using
        euclideanCovarianceMatrix_quadratic_eq_variance (X 0) hL2 t
    have hproj : HasLaw (fun x : EuclideanSpace ℝ kappa => ⟪t, x⟫_ℝ)
        (gaussianReal 0 Var[Xt 0; mu].toNNReal)
        (multivariateGaussian 0 Sigma) := by
      refine ⟨by fun_prop, ?_⟩
      let L : EuclideanSpace ℝ kappa →L[ℝ] ℝ := innerSL ℝ t
      change (multivariateGaussian 0 Sigma).map L = _
      rw [IsGaussian.map_eq_gaussianReal]
      congr 2
      · rw [L.integral_comp_id_comm IsGaussian.integrable_id,
          integral_id_multivariateGaussian]
        simp
      · change Var[fun u => ⟪t, u⟫_ℝ; multivariateGaussian 0 Sigma] = _
        rw [← covarianceBilin_self IsGaussian.memLp_two_id t,
          covarianceBilin_multivariateGaussian hSigma]
        exact hquad
    have hYt : HasLaw Yt (gaussianReal 0 Var[Xt 0; mu].toNNReal) mu' := by
      have hcomp := hproj.comp hY
      simpa only [Yt, Function.comp_def, Sigma] using hcomp
    have ht := tendstoInDistribution_inv_sqrt_mul_sum_sub
      hYt hXtL2 hindep_t hident_t
    have htchar :=
      (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 ht.tendsto) 1
    simp only [ProbabilityMeasure.coe_mk] at htchar ⊢
    convert htchar using 1
    · funext n
      rw [charFun_map_inner_eq_charFun_map_one]
      · congr 2
        funext omega
        simp only [Xt]
        rw [real_inner_smul_right, inner_sub_right, inner_sum,
          integral_inner hInt, real_inner_smul_right]
      · have hc : AEMeasurable
            (fun _ : Omega => (n : ℝ) • ∫ omega, X 0 omega ∂mu) mu :=
          aemeasurable_const
        exact ((Finset.aemeasurable_fun_sum (Finset.range n)
          (fun i _ => hXmeas i)).sub hc).const_smul ((√n)⁻¹ : ℝ)
    · congr 1
      exact charFun_map_inner_eq_charFun_map_one Y hY.aemeasurable t

section FiniteSupportProcess

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The centered support process evaluated at a finite family of directions,
bundled as a Euclidean random vector.-/
def finiteDirectionalSupportDeviation
    (S : ℕ → Omega → Set E) (L : Set E)
    (u : kappa → E) (i : ℕ) (omega : Omega) : EuclideanSpace ℝ kappa :=
  toLp 2 (fun j => directionalSupportDeviation S L (u j) i omega)

/-- Covariance matrix of the finite vector of support deviations.-/
def finiteDirectionalSupportCovariance
    (S : ℕ → Omega → Set E) (L : Set E) (u : kappa → E)
    (mu : Measure Omega) : Matrix kappa kappa ℝ :=
  euclideanCovarianceMatrix (finiteDirectionalSupportDeviation S L u 0) mu

omit [Fintype kappa] in
/--
@isnad1 id=eq.0h9v.s6.43b394348913 from=translated src=- shape=2fe845fa vocab=2a9278da
-/
@[simp]
theorem finiteDirectionalSupportCovariance_apply
    (S : ℕ → Omega → Set E) (L : Set E) (u : kappa → E)
    (mu : Measure Omega) (j l : kappa) :
    finiteDirectionalSupportCovariance S L u mu j l =
      cov[directionalSupportDeviation S L (u j) 0,
        directionalSupportDeviation S L (u l) 0; mu] := rfl

omit [Fintype kappa] in
/-- The covariance matrix of the centered finite support vector is exactly
the covariance kernel of the raw support functions.
@isnad1 id=eq.2h9v.s7.c58ba912babe from=translated src=- shape=f5b56ea0 vocab=3651cc5b
-/
theorem finiteDirectionalSupportCovariance_apply_eq_supportFunction
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (S : ℕ → Omega → Set E) (L : Set E) (u : kappa → E)
    (j l : kappa)
    (hj : Integrable (fun omega => supportFunction (S 0 omega) (u j)) mu)
    (hl : Integrable (fun omega => supportFunction (S 0 omega) (u l)) mu) :
    finiteDirectionalSupportCovariance S L u mu j l =
      cov[fun omega => supportFunction (S 0 omega) (u j),
        fun omega => supportFunction (S 0 omega) (u l); mu] := by
  rw [finiteDirectionalSupportCovariance_apply]
  exact covariance_directionalSupportDeviation_eq_supportFunction
    S L (u j) (u l) hj hl

/--
@isnad1 id=possemid.1h7v.s7.c978f6063911 from=translated src=- shape=a58457e1 vocab=0e2d485c
-/
theorem finiteDirectionalSupportCovariance_posSemidef
    {mu : Measure Omega} [IsFiniteMeasure mu]
    (S : ℕ → Omega → Set E) (L : Set E) (u : kappa → E)
    (hL2 : MemLp (finiteDirectionalSupportDeviation S L u 0) 2 mu) :
    (finiteDirectionalSupportCovariance S L u mu).PosSemidef :=
  euclideanCovarianceMatrix_posSemidef _ hL2

/-- Joint finite-dimensional CLT for support functions of empirical
Minkowski averages.  This proves convergence of the whole vector indexed by
`kappa`, not merely convergence of each coordinate separately.
@isnad1 id=tendstoi.7h10v.s9.544baaa002c9 from=translated src=- shape=de3ea212 vocab=b99996e9
-/
theorem tendstoInDistribution_finiteDirectionalSupport_minkowskiAverage
    [DecidableEq kappa]
    {Omega' : Type*} [MeasurableSpace Omega']
    {mu : Measure Omega} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure mu']
    (S : ℕ → Omega → Set E) (L : Set E) (u : kappa → E)
    (Y : Omega' → EuclideanSpace ℝ kappa)
    (hScompact : ∀ i omega, IsCompact (S i omega))
    (hSne : ∀ i omega, (S i omega).Nonempty)
    (hY : HasLaw Y
      (multivariateGaussian 0
        (finiteDirectionalSupportCovariance S L u mu)) mu')
    (hL2 : MemLp (finiteDirectionalSupportDeviation S L u 0) 2 mu)
    (hindep : iIndepFun (finiteDirectionalSupportDeviation S L u) mu)
    (hident : ∀ i, IdentDistrib
      (finiteDirectionalSupportDeviation S L u i)
      (finiteDirectionalSupportDeviation S L u 0) mu mu)
    (hcenter : ∀ j, mu[directionalSupportDeviation S L (u j) 0] = 0) :
    TendstoInDistribution
      (fun (n : ℕ) omega => toLp 2 (fun j =>
        √((n + 1 : ℕ) : ℝ) *
          (supportFunction
              (minkowskiAverage (Finset.range (n + 1))
                (fun i => S i omega)) (u j) -
            supportFunction L (u j))))
      atTop Y (fun _ => mu) mu' := by
  let V := finiteDirectionalSupportDeviation S L u
  have hVint : Integrable (V 0) mu := hL2.integrable (by norm_num)
  have hcenterV : ∫ omega, V 0 omega ∂mu = 0 := by
    ext j
    rw [eval_integral_piLp (fun l => hVint.eval_piLp l)]
    exact hcenter j
  have hclt := tendstoInDistribution_euclidean_inv_sqrt_smul_sum_sub
    V Y hY hL2 hindep hident
  have hshift : TendstoInDistribution
      (fun (n : ℕ) omega =>
        (√(n + 1 : ℕ))⁻¹ •
          (∑ i ∈ Finset.range (n + 1), V i omega -
            ((n + 1 : ℕ) : ℝ) • ∫ omega, V 0 omega ∂mu))
      atTop Y (fun _ => mu) mu' :=
    { forall_aemeasurable := fun n => hclt.forall_aemeasurable (n + 1)
      aemeasurable_limit := hclt.aemeasurable_limit
      tendsto := hclt.tendsto.comp (tendsto_add_atTop_nat 1) }
  apply hshift.congr
  · intro n
    filter_upwards [] with omega
    rw [hcenterV, smul_zero, sub_zero]
    ext j
    simp only [PiLp.smul_apply]
    have hsum :
        (∑ i ∈ Finset.range (n + 1), V i omega) j =
          ∑ i ∈ Finset.range (n + 1),
            directionalSupportDeviation S L (u j) i omega := by
      change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : kappa => ℝ) j)
          (∑ i ∈ Finset.range (n + 1), V i omega) = _
      rw [map_sum]
      simp [V, finiteDirectionalSupportDeviation, PiLp.proj_apply]
    rw [hsum]
    simp only [smul_eq_mul]
    rw [supportFunction_minkowskiAverage_sub_eq_average_deviation
      S L (Finset.range (n + 1)) (by simp)
      (fun i _ omega' => hScompact i omega')
      (fun i _ omega' => hSne i omega')]
    have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hsqrt : √(n + 1 : ℕ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hn)
    field_simp
    rw [Finset.card_range, Real.sq_sqrt hn.le]
    ring
  · exact Filter.Eventually.of_forall (fun _ => rfl)

/-- Observation-level iid specialization of the joint support-process CLT.
Effros measurability transports iid observations to the entire finite vector;
the population support identities center every coordinate automatically.
@isnad1 id=tendstoi.8h12v.s9.3bcf40ca818c from=translated src=- shape=0f993af8 vocab=e00f3b9e
-/
theorem tendstoInDistribution_iid_finiteDirectionalSupport_minkowskiAverage
    [DecidableEq kappa]
    {Omega' Z : Type*} [MeasurableSpace Omega'] [MeasurableSpace Z]
    {mu : Measure Omega} {mu' : Measure Omega'}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure mu']
    (X : ℕ → Omega → Z)
    (hindep : iIndepFun X mu)
    (hident : ∀ i, IdentDistrib (X i) (X 0) mu mu)
    (F : Z → Set E) (hF : RandomSet.IsEffrosMeasurable F)
    (hFcompact : ∀ z, IsCompact (F z))
    (hFne : ∀ z, (F z).Nonempty)
    (L : Set E) (u : kappa → E)
    (Y : Omega' → EuclideanSpace ℝ kappa)
    (hY : HasLaw Y
      (multivariateGaussian 0
        (finiteDirectionalSupportCovariance
          (fun i omega => F (X i omega)) L u mu)) mu')
    (hL2 : MemLp
      (finiteDirectionalSupportDeviation
        (fun i omega => F (X i omega)) L u 0) 2 mu)
    (hLsupport : ∀ j, supportFunction L (u j) =
      ∫ omega, supportFunction (F (X 0 omega)) (u j) ∂mu) :
    TendstoInDistribution
      (fun (n : ℕ) omega => toLp 2 (fun j =>
        √((n + 1 : ℕ) : ℝ) *
          (supportFunction
              (minkowskiAverage (Finset.range (n + 1))
                (fun i => F (X i omega))) (u j) -
            supportFunction L (u j))))
      atTop Y (fun _ => mu) mu' := by
  let S : ℕ → Omega → Set E := fun i omega => F (X i omega)
  let g : Z → EuclideanSpace ℝ kappa := fun z =>
    toLp 2 (fun j => supportFunction (F z) (u j) - supportFunction L (u j))
  have hsupp : ∀ j, Measurable (fun z => supportFunction (F z) (u j)) :=
    fun j => measurable_supportFunction hF hFcompact hFne (u j)
  have hg : Measurable g := by
    exact (WithLp.measurable_toLp 2 (kappa → ℝ)).comp
      (measurable_pi_lambda _ (fun j => (hsupp j).sub_const _))
  have hindepV : iIndepFun (finiteDirectionalSupportDeviation S L u) mu := by
    change iIndepFun (fun i omega => g (X i omega)) mu
    simpa only [Function.comp_def] using
      hindep.comp (fun _ => g) (fun _ => hg)
  have hidentV : ∀ i, IdentDistrib
      (finiteDirectionalSupportDeviation S L u i)
      (finiteDirectionalSupportDeviation S L u 0) mu mu := by
    intro i
    change IdentDistrib (fun omega => g (X i omega))
      (fun omega => g (X 0 omega)) mu mu
    simpa only [Function.comp_def] using (hident i).comp hg
  have hcenter : ∀ j, mu[directionalSupportDeviation S L (u j) 0] = 0 := by
    intro j
    have hdevInt : Integrable (directionalSupportDeviation S L (u j) 0) mu := by
      simpa only [finiteDirectionalSupportDeviation, S] using
        (hL2.eval_piLp j).integrable (by norm_num)
    have hsuppInt : Integrable
        (fun omega => supportFunction (F (X 0 omega)) (u j)) mu := by
      have h := hdevInt.add (integrable_const (supportFunction L (u j)))
      apply h.congr
      filter_upwards [] with omega
      change (supportFunction (F (X 0 omega)) (u j) -
        supportFunction L (u j)) + supportFunction L (u j) = _
      ring
    change ∫ omega,
      (supportFunction (F (X 0 omega)) (u j) -
        supportFunction L (u j)) ∂mu = 0
    rw [integral_sub hsuppInt (integrable_const (supportFunction L (u j))),
      ← hLsupport j]
    simp
  exact tendstoInDistribution_finiteDirectionalSupport_minkowskiAverage
    S L u Y
    (fun i omega => hFcompact (X i omega))
    (fun i omega => hFne (X i omega))
    hY hL2 hindepV hidentV hcenter

end FiniteSupportProcess

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
