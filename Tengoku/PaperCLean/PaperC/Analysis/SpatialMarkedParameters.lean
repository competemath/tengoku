import Tengoku.PaperCLean.PaperC.Analysis.SpatialRiemannSums
import Tengoku.PaperCLean.PaperC.Probability.SpatialThinningFinite
import Tengoku.Seed.MeasureTheory.Function.LocallyIntegrable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Spatial and marked parameter limits

This module turns the literal Riemann-sum theorem into the parameter limits
used in Sections 14.2 and 14.4.  The scale is the manuscript's exact
`λ_N = N / 2^L`; no rounding or asymptotic replacement is hidden in the
definitions.
-/

namespace PaperC
namespace SpatialMarkedParameters

open scoped BigOperators Topology
open Filter MeasureTheory Set
open SpatialRiemannSums

noncomputable section

/-- Auxiliary retention probability `1 - exp (-g(t))`.-/
def spatialRetention (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 - Real.exp (-g t)

/--
@isnad1 id=continuo.1h1v.s5.33dbeabcadd2 from=translated src=- shape=7861e8ca vocab=4f1ba1d3
-/
theorem continuous_spatialRetention
    {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (spatialRetention g) := by
  exact continuous_const.sub (Real.continuous_exp.comp hg.neg)

/--
@isnad1 id=continuo.1h1v.s6.c405ca66488d from=translated src=- shape=025ac4a0 vocab=88c0517f
-/
theorem continuousOn_spatialRetention
    {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Icc (1 : ℝ) 2)) :
    ContinuousOn (spatialRetention g) (Set.Icc (1 : ℝ) 2) := by
  exact continuousOn_const.sub
    (Real.continuous_exp.continuousOn.comp hg.neg
      (Set.mapsTo_univ _ _))

/--
@isnad1 id=le.1h2v.s5.d032bb73d47c from=translated src=- shape=8c2ee0a1 vocab=44866787
-/
theorem spatialRetention_nonneg
    {g : ℝ → ℝ} (hg : ∀ t, 0 ≤ g t) (t : ℝ) :
    0 ≤ spatialRetention g t := by
  unfold spatialRetention
  exact sub_nonneg.mpr
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hg t)))

/--
@isnad1 id=le.0h2v.s4.7eaff8611d34 from=translated src=- shape=5f12998d vocab=44866787
-/
theorem spatialRetention_le_one
    (g : ℝ → ℝ) (t : ℝ) :
    spatialRetention g t ≤ 1 := by
  unfold spatialRetention
  linarith [Real.exp_pos (-g t)]

/-- The exact critical scale `λ_N = N / 2^L`.-/
def criticalSpatialScale (N L : ℕ) : ℝ :=
  (N : ℝ) / (2 : ℝ) ^ L

/--
The exact Poisson parameter of the spatially thinned finite family:
`2⁻ᴸ ∑_{x∈[N,2N)} (1-exp(-g(x/N)))`.-/
def spatialThinnedParameter
    (N L : ℕ) (g : ℝ → ℝ) : ℝ :=
  (∑ x ∈ dyadicBlock N,
      spatialRetention g ((x : ℝ) / (N : ℝ))) /
    (2 : ℝ) ^ L

/-- Exact factorization into the critical scale and normalized Riemann sum.
@isnad1 id=eq.1h3v.s5.bf8020af82b6 from=translated src=- shape=29c5ea9f vocab=5a2307e6
-/
theorem spatialThinnedParameter_eq_scale_mul
    {N L : ℕ} (hN : 0 < N) (g : ℝ → ℝ) :
    spatialThinnedParameter N L g =
      criticalSpatialScale N L *
        dyadicRiemannSum N (spatialRetention g) := by
  unfold spatialThinnedParameter criticalSpatialScale dyadicRiemannSum
  field_simp

/--
Source-facing parameter limit for Section 14.2.  Along arbitrary sequences
with `N → ∞` and `N / 2^L → λ`, the thinned parameter tends to
`λ ∫_[1,2) (1-exp(-g(t))) dt`.
@isnad1 id=tendsto.3h4v.s7.366794d1bc10 from=translated src=- shape=aa520d4d vocab=2cb0db1a
-/
theorem tendsto_spatialThinnedParameter
    {N L : ℕ → ℕ} {rate : ℝ} {g : ℝ → ℝ}
    (hN : Tendsto N atTop atTop)
    (hscale : Tendsto
      (fun n ↦ criticalSpatialScale (N n) (L n))
      atTop (𝓝 rate))
    (hg : ContinuousOn g (Set.Icc (1 : ℝ) 2)) :
    Tendsto
      (fun n ↦ spatialThinnedParameter (N n) (L n) g)
      atTop
      (𝓝 (rate * ∫ t in Set.Ico (1 : ℝ) 2,
        spatialRetention g t)) := by
  have hR :
      Tendsto
        (fun n ↦ dyadicRiemannSum (N n) (spatialRetention g))
        atTop
        (𝓝 (∫ t in Set.Ico (1 : ℝ) 2,
          spatialRetention g t)) :=
    (tendsto_dyadicRiemannSum_of_continuousOn
      (continuousOn_spatialRetention hg)).comp hN
  apply (hscale.mul hR).congr'
  filter_upwards [hN.eventually (eventually_ge_atTop 1)] with n hn
  exact (spatialThinnedParameter_eq_scale_mul
    (Nat.zero_lt_of_lt hn) g).symm

/--
The corresponding convergence of exponential void probabilities, already in
the exact form of the Laplace functional of a homogeneous Poisson process.
@isnad1 id=tendsto.3h4v.s7.b302e805b5bc from=translated src=- shape=42c555b2 vocab=799ae543
-/
theorem tendsto_exp_neg_spatialThinnedParameter
    {N L : ℕ → ℕ} {rate : ℝ} {g : ℝ → ℝ}
    (hN : Tendsto N atTop atTop)
    (hscale : Tendsto
      (fun n ↦ criticalSpatialScale (N n) (L n))
      atTop (𝓝 rate))
    (hg : ContinuousOn g (Set.Icc (1 : ℝ) 2)) :
    Tendsto
      (fun n ↦ Real.exp
        (-spatialThinnedParameter (N n) (L n) g))
      atTop
      (𝓝 (Real.exp
        (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
          spatialRetention g t)))) := by
  exact Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_spatialThinnedParameter hN hscale hg).neg)

/-- Geometric mark weight `ν({e}) = 2^{-(e+1)}`.-/
def geometricMarkWeight (e : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ (e + 1)

/--
@isnad1 id=le.0h1v.s3.4843e54ca9a4 from=translated src=- shape=b9369acb vocab=abba516e
-/
theorem geometricMarkWeight_nonneg (e : ℕ) :
    0 ≤ geometricMarkWeight e := by
  unfold geometricMarkWeight
  positivity

/--
@isnad1 id=eq.0h1v.s5.1807e1845592 from=translated src=- shape=d8b7bfe7 vocab=fa07ff98
-/
theorem geometricMarkWeight_eq_half_pow (e : ℕ) :
    geometricMarkWeight e = ((1 / 2 : ℝ) ^ (e + 1)) := by
  unfold geometricMarkWeight
  rw [one_div_pow]

/--
@isnad1 id=hassum.0h0v.s4.06f72ed152c0 from=translated src=- shape=b3278842 vocab=ccd19b8d
-/
theorem hasSum_geometricMarkWeight :
    HasSum geometricMarkWeight 1 := by
  have h :=
    (hasSum_geometric_two :
      HasSum (fun e : ℕ ↦ (1 / 2 : ℝ) ^ e) 2)
  have hhalf := h.mul_left (1 / 2 : ℝ)
  have hfun :
      (fun e : ℕ ↦ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ e) =
        geometricMarkWeight := by
    funext e
    rw [geometricMarkWeight_eq_half_pow, pow_succ']
  rw [hfun] at hhalf
  norm_num at hhalf
  exact hhalf

/--
@isnad1 id=eq.0h0v.s4.b1622c5504de from=translated src=- shape=db078bc9 vocab=f91eabe5
-/
theorem tsum_geometricMarkWeight :
    ∑' e : ℕ, geometricMarkWeight e = 1 :=
  hasSum_geometricMarkWeight.tsum_eq

/--
Exact geometric tail used in the final de-truncation:
`∑_{e≥E+1} 2^{-(e+1)} = 2^{-(E+1)}`.
@isnad1 id=eq.0h1v.s6.92f194e07b8e from=translated src=- shape=fca6f41c vocab=8e2ed563
-/
theorem tsum_geometricMarkWeight_tail (E : ℕ) :
    ∑' e : ℕ, geometricMarkWeight (e + (E + 1)) =
      (1 / 2 : ℝ) ^ (E + 1) := by
  calc
    (∑' e : ℕ, geometricMarkWeight (e + (E + 1))) =
        ∑' e : ℕ,
          (1 / 2 : ℝ) ^ (E + 1) *
            geometricMarkWeight e := by
      apply tsum_congr
      intro e
      simp only [geometricMarkWeight_eq_half_pow]
      rw [show e + (E + 1) + 1 = (E + 1) + (e + 1) by omega,
        pow_add]
    _ = (1 / 2 : ℝ) ^ (E + 1) *
        ∑' e : ℕ, geometricMarkWeight e := by
      rw [tsum_mul_left]
    _ = (1 / 2 : ℝ) ^ (E + 1) := by
      rw [tsum_geometricMarkWeight, mul_one]

/--
@isnad1 id=tendsto.0h0v.s6.12acc6084bcd from=translated src=- shape=2e1d21af vocab=fc906693
-/
theorem tendsto_geometricMarkWeight_tail_zero :
    Tendsto (fun E : ℕ ↦ (1 / 2 : ℝ) ^ (E + 1))
      atTop (𝓝 0) := by
  simpa only [pow_succ, zero_mul] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (1 / 2 : ℝ)

/--
Exact finite marked parameter for marks `0 ≤ e ≤ E`.-/
def markedThinnedParameter
    (N L E : ℕ) (g : ℝ → ℕ → ℝ) : ℝ :=
  ∑ e ∈ Finset.range (E + 1),
    geometricMarkWeight e *
      spatialThinnedParameter N L (fun t ↦ g t e)

/--
The same marked parameter in the literal manuscript order: first the start
`x`, then its exact excess mark `e`, with mass `2^{-(L+e+1)}`.-/
def literalMarkedThinnedParameter
    (N L E : ℕ) (g : ℝ → ℕ → ℝ) : ℝ :=
  ∑ x ∈ dyadicBlock N,
    ∑ e ∈ Finset.range (E + 1),
      spatialRetention (fun t ↦ g t e)
          ((x : ℝ) / (N : ℝ)) /
        (2 : ℝ) ^ (L + e + 1)

/--
@isnad1 id=eq.0h4v.s4.bae10af701ce from=translated src=- shape=303bae66 vocab=2804e2e8
-/
theorem markedThinnedParameter_eq_literal
    (N L E : ℕ) (g : ℝ → ℕ → ℝ) :
    markedThinnedParameter N L E g =
      literalMarkedThinnedParameter N L E g := by
  classical
  unfold markedThinnedParameter literalMarkedThinnedParameter
    spatialThinnedParameter geometricMarkWeight
  calc
    (∑ e ∈ Finset.range (E + 1),
        (1 / (2 : ℝ) ^ (e + 1)) *
          ((∑ x ∈ dyadicBlock N,
            spatialRetention (fun t ↦ g t e)
              ((x : ℝ) / (N : ℝ))) / (2 : ℝ) ^ L)) =
      ∑ e ∈ Finset.range (E + 1),
        ∑ x ∈ dyadicBlock N,
          spatialRetention (fun t ↦ g t e)
              ((x : ℝ) / (N : ℝ)) /
            (2 : ℝ) ^ (L + e + 1) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [show L + e + 1 = L + (e + 1) by omega, pow_add]
      ring_nf
    _ = ∑ x ∈ dyadicBlock N,
        ∑ e ∈ Finset.range (E + 1),
          spatialRetention (fun t ↦ g t e)
              ((x : ℝ) / (N : ℝ)) /
            (2 : ℝ) ^ (L + e + 1) := by
      rw [Finset.sum_comm]

/-- The truncated intensity integrand in the marked Laplace functional.-/
def markedRetentionIntegrand
    (E : ℕ) (g : ℝ → ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ e ∈ Finset.range (E + 1),
    geometricMarkWeight e *
      spatialRetention (fun u ↦ g u e) t

/--
@isnad1 id=continuo.1h2v.s6.3bb7d622b2d6 from=translated src=- shape=05fa42bf vocab=2007937e
-/
theorem continuous_markedRetentionIntegrand
    {E : ℕ} {g : ℝ → ℕ → ℝ}
    (hg : ∀ e ≤ E,
      ContinuousOn (fun t ↦ g t e) (Set.Icc (1 : ℝ) 2)) :
    ContinuousOn (markedRetentionIntegrand E g)
      (Set.Icc (1 : ℝ) 2) := by
  unfold markedRetentionIntegrand
  apply continuousOn_finsetSum
  intro e he
  exact continuousOn_const.mul
    (continuousOn_spatialRetention
      (hg e (Nat.le_of_lt_succ (Finset.mem_range.mp he))))

/--
@isnad1 id=le.1h3v.s5.51274440e2fd from=translated src=- shape=eb73b81b vocab=2b404a3b
-/
theorem markedRetentionIntegrand_nonneg
    {E : ℕ} {g : ℝ → ℕ → ℝ}
    (hg : ∀ t e, 0 ≤ g t e) (t : ℝ) :
    0 ≤ markedRetentionIntegrand E g t := by
  unfold markedRetentionIntegrand
  exact Finset.sum_nonneg fun e _ ↦
    mul_nonneg (geometricMarkWeight_nonneg e)
      (spatialRetention_nonneg (fun u ↦ hg u e) t)

/-- Integration commutes with the finite sum over marks.
@isnad1 id=eq.1h2v.s7.fce416988a8c from=translated src=- shape=540cdbd1 vocab=47898064
-/
theorem integral_markedRetentionIntegrand
    {E : ℕ} {g : ℝ → ℕ → ℝ}
    (hg : ∀ e ≤ E,
      ContinuousOn (fun t ↦ g t e) (Set.Icc (1 : ℝ) 2)) :
    (∫ t in Set.Ico (1 : ℝ) 2,
        markedRetentionIntegrand E g t) =
      ∑ e ∈ Finset.range (E + 1),
        geometricMarkWeight e *
          ∫ t in Set.Ico (1 : ℝ) 2,
            spatialRetention (fun u ↦ g u e) t := by
  unfold markedRetentionIntegrand
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro e he
    rw [integral_const_mul]
  · intro e he
    have hcont :
        ContinuousOn
          (spatialRetention (fun u ↦ g u e))
          (Set.Icc (1 : ℝ) 2) :=
      continuousOn_spatialRetention
        (hg e (Nat.le_of_lt_succ (Finset.mem_range.mp he)))
    exact
      ((hcont.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self).const_mul
        (geometricMarkWeight e))

/--
Source-facing marked parameter limit for fixed truncation `E`.
@isnad1 id=tendsto.3h5v.s7.0eb7d96f5a86 from=translated src=- shape=8967940c vocab=e9bf3d62
-/
theorem tendsto_markedThinnedParameter
    {N L : ℕ → ℕ} {rate : ℝ} {E : ℕ}
    {g : ℝ → ℕ → ℝ}
    (hN : Tendsto N atTop atTop)
    (hscale : Tendsto
      (fun n ↦ criticalSpatialScale (N n) (L n))
      atTop (𝓝 rate))
    (hg : ∀ e ≤ E,
      ContinuousOn (fun t ↦ g t e) (Set.Icc (1 : ℝ) 2)) :
    Tendsto
      (fun n ↦ markedThinnedParameter (N n) (L n) E g)
      atTop
      (𝓝 (rate * ∫ t in Set.Ico (1 : ℝ) 2,
        markedRetentionIntegrand E g t)) := by
  have hsum :
      Tendsto
        (fun n ↦ ∑ e ∈ Finset.range (E + 1),
          geometricMarkWeight e *
            spatialThinnedParameter (N n) (L n)
              (fun t ↦ g t e))
        atTop
        (𝓝 (∑ e ∈ Finset.range (E + 1),
          geometricMarkWeight e *
            (rate * ∫ t in Set.Ico (1 : ℝ) 2,
              spatialRetention (fun u ↦ g u e) t))) := by
    apply tendsto_finsetSum
    intro e he
    exact (tendsto_spatialThinnedParameter hN hscale
      (hg e (Nat.le_of_lt_succ (Finset.mem_range.mp he)))).const_mul
        (geometricMarkWeight e)
  rw [integral_markedRetentionIntegrand hg]
  convert hsum using 1
  · rfl
  · apply congrArg nhds
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring

/--
The fixed-`E` marked Laplace exponent converges to the Poisson exponent.
@isnad1 id=tendsto.3h5v.s7.3aa5ba0b6350 from=translated src=- shape=29702ebc vocab=05e11338
-/
theorem tendsto_exp_neg_markedThinnedParameter
    {N L : ℕ → ℕ} {rate : ℝ} {E : ℕ}
    {g : ℝ → ℕ → ℝ}
    (hN : Tendsto N atTop atTop)
    (hscale : Tendsto
      (fun n ↦ criticalSpatialScale (N n) (L n))
      atTop (𝓝 rate))
    (hg : ∀ e ≤ E,
      ContinuousOn (fun t ↦ g t e) (Set.Icc (1 : ℝ) 2)) :
    Tendsto
      (fun n ↦ Real.exp
        (-markedThinnedParameter (N n) (L n) E g))
      atTop
      (𝓝 (Real.exp
        (-(rate * ∫ t in Set.Ico (1 : ℝ) 2,
          markedRetentionIntegrand E g t)))) := by
  exact Real.continuous_exp.continuousAt.tendsto.comp
    ((tendsto_markedThinnedParameter hN hscale hg).neg)

end

end SpatialMarkedParameters
end PaperC
