import Tengoku.LerayHopf.LerayHopf.R3.RellichBall
import Tengoku.LerayHopf.LerayHopf.Analysis.BoundedMultiplier

/-!
# Weighted-Fourier element and the unbounded-multiplier Bochner commute (`WeightedFourierCommute`)

This file isolates the single genuinely-new analytic pillar needed to close the viscous/H¹
Steklov–Jensen bound (`viscousFormSq_steklovAvg_le_average`, the issue-#15 gate): the
**unbounded spectral multiplier `√W` (`W ξ = (2π)²‖ξ‖²`) commutes with a Bochner interval
integral** of a continuous `L2C_R3`-valued curve, PROVIDED the weighted curve `s ↦ √W•(g s)`
is itself continuous into `L2C_R3`.

The weighted element `weightedFourierComponent j w := (√W • 𝓕(projⱼ w))` (as an `L2C_R3` class,
well-defined for `w ∈ H¹` via `integrable_viscous_integrand_of_memH1`) packages the viscous
form as a genuine Hilbert squared-norm:

  `viscousFormSq_R3 1 w = ∑ j, ‖weightedFourierComponent j w‖²`   (for `memH1VF_R3 w`).

The commute lemma `multiplier_smul_integral_comm` is proved by the standard truncation route:
truncate `√W` to `min(√W, k)` (a *bounded* multiplier, whose multiplication operator is a CLM on
`L²` and hence commutes with the Bochner integral via `integral_comp_comm`), then pass `k → ∞`
using dominated convergence on both sides — the curve continuity supplies the `L²` domination on
the compact window.  Every ingredient is in mathlib; the unbounded weight is handled by the limit.

This is exactly the content the spike (#15 Stage 1) showed is unreachable from the bare
`L²(vol)`-continuity of the Galerkin curve, and which the interface enrichment
(`GalerkinSolutionData_R3.viscous_curve_continuous`) supplies.
-/

open MeasureTheory FourierTransform
open scoped FourierTransform ENNReal

namespace LerayHopf

/-- The pointwise spectral weight `W ξ = (2π)² ‖ξ‖²` of the viscous form. -/
noncomputable def viscousWeight (ξ : Domain3) : ℝ := (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2

/-- The square-root spectral multiplier `√W ξ = 2π ‖ξ‖`, as a (real, nonnegative, continuous)
function on `Domain3`. -/
noncomputable def sqrtViscousWeight (ξ : Domain3) : ℝ := (2 * Real.pi) * ‖ξ‖

/-- The square-root weight `sqrtViscousWeight` is nonnegative.
@isnad1 id=le.0h1v.s3.bc2ff70051d7 from=translated src=- shape=b9369acb vocab=3b6167e7
-/
theorem sqrtViscousWeight_nonneg (ξ : Domain3) : 0 ≤ sqrtViscousWeight ξ := by
  unfold sqrtViscousWeight
  positivity

/-- Squaring `sqrtViscousWeight` recovers the viscous weight `viscousWeight`.
@isnad1 id=eq.0h1v.s4.aa4b59fd3eed from=translated src=- shape=1ea879dc vocab=d97c2f08
-/
theorem sqrtViscousWeight_sq (ξ : Domain3) : sqrtViscousWeight ξ ^ 2 = viscousWeight ξ := by
  unfold sqrtViscousWeight viscousWeight
  ring

/-- The square-root weight `sqrtViscousWeight` is continuous.
@isnad1 id=continuo.0h0v.s5.230bfde4f317 from=translated src=- shape=54c8eceb vocab=0c2f4370
-/
theorem continuous_sqrtViscousWeight : Continuous sqrtViscousWeight := by
  unfold sqrtViscousWeight
  exact continuous_const.mul continuous_norm

/-- Truncated square-root weight `min(√W ξ, k)` — bounded by `k`, continuous, nonneg. -/
noncomputable def sqrtViscousWeightTrunc (k : ℕ) (ξ : Domain3) : ℝ :=
  min (sqrtViscousWeight ξ) k

/-- The truncated square-root weight `sqrtViscousWeightTrunc k` is nonnegative.
@isnad1 id=le.0h2v.s4.6e3eef46a8f6 from=translated src=- shape=0d4521f5 vocab=11b27ae1
-/
theorem sqrtViscousWeightTrunc_nonneg (k : ℕ) (ξ : Domain3) : 0 ≤ sqrtViscousWeightTrunc k ξ :=
  le_min (sqrtViscousWeight_nonneg ξ) (Nat.cast_nonneg k)

/-- The truncated square-root weight `sqrtViscousWeightTrunc k` is bounded by `k`.
@isnad1 id=le.0h2v.s4.940a4ee172cc from=translated src=- shape=e4e031a1 vocab=4f235802
-/
theorem sqrtViscousWeightTrunc_abs_le (k : ℕ) (ξ : Domain3) :
    |sqrtViscousWeightTrunc k ξ| ≤ k := by
  rw [abs_of_nonneg (sqrtViscousWeightTrunc_nonneg k ξ)]
  exact min_le_right _ _

/-- The truncated square-root weight `sqrtViscousWeightTrunc k` is continuous, as the pointwise
`min` of two continuous functions.
@isnad1 id=continuo.0h1v.s5.9384844ef32b from=translated src=- shape=7000f90d vocab=47a4d26e
-/
theorem continuous_sqrtViscousWeightTrunc (k : ℕ) : Continuous (sqrtViscousWeightTrunc k) :=
  continuous_sqrtViscousWeight.min continuous_const

/-- The ℂ-coerced truncated weight is in `L^∞`.
@isnad1 id=memlp.0h1v.s8.3d127c65beae from=translated src=- shape=028d4ccd vocab=7900f521
-/
theorem memLp_top_sqrtViscousWeightTrunc (k : ℕ) :
    MemLp (fun ξ : Domain3 => (sqrtViscousWeightTrunc k ξ : ℂ)) ⊤ (volume : Measure Domain3) := by
  refine memLp_top_of_bound
    (Complex.continuous_ofReal.comp (continuous_sqrtViscousWeightTrunc k)).aestronglyMeasurable
    (k : ℝ) ?_
  filter_upwards with ξ
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact sqrtViscousWeightTrunc_abs_le k ξ

/-- The truncated weights increase to `√W` pointwise: `min(√W,k) ↑ √W` as `k → ∞`.
@isnad1 id=tendsto.0h1v.s4.580a33a752ea from=translated src=- shape=f0cc60ab vocab=55e88245
-/
theorem tendsto_sqrtViscousWeightTrunc (ξ : Domain3) :
    Filter.Tendsto (fun k : ℕ => sqrtViscousWeightTrunc k ξ) Filter.atTop
      (nhds (sqrtViscousWeight ξ)) := by
  -- For `k ≥ ⌈√W ξ⌉₊`, `min(√W ξ, k) = √W ξ`; the family is eventually constant.
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (⌈sqrtViscousWeight ξ⌉₊)] with k hk
  symm
  rw [sqrtViscousWeightTrunc, min_eq_left]
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr hk)

/-! ### The (unbounded) weighted Fourier component of an `H¹` state -/

/-- For `w ∈ H¹`, the weighted Fourier component `√W • 𝓕(projⱼ w)` lies in `L²`: its squared norm
is the (finite) viscous spectral integrand.
@isnad1 id=memlp.1h2v.s16.c0951f7e1b50 from=translated src=- shape=bea0bd09 vocab=d0621a39
-/
theorem memLp_sqrtWeight_smul_fourier (w : L2VF_R3) (hw : memH1VF_R3 w) (j : Fin 3) :
    MemLp (fun ξ : Domain3 => (sqrtViscousWeight ξ : ℂ) • (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ)
      2 (volume : Measure Domain3) := by
  have haesm : AEStronglyMeasurable
      (fun ξ : Domain3 => (sqrtViscousWeight ξ : ℂ) •
        (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ) (volume : Measure Domain3) :=
    (Complex.continuous_ofReal.comp continuous_sqrtViscousWeight).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable _)
  refine (memLp_two_iff_integrable_sq_norm haesm).mpr ?_
  -- `‖√W • 𝓕(projⱼ w) ξ‖² = W ξ ‖𝓕(projⱼ w) ξ‖²`, integrable via `integrable_viscous_integrand_of_memH1`
  refine (integrable_viscous_integrand_of_memH1 w hw j).congr ?_
  filter_upwards with ξ
  have hsw : sqrtViscousWeight ξ ^ 2 = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := by
    rw [sqrtViscousWeight_sq]; rfl
  conv_rhs => rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, hsw]

/-- The weighted Fourier component `√W • 𝓕(projⱼ w)` of an `H¹` state, as an `L²` element. -/
noncomputable def weightedFourierComponent (w : L2VF_R3) (hw : memH1VF_R3 w) (j : Fin 3) : L2C_R3 :=
  (memLp_sqrtWeight_smul_fourier w hw j).toLp _

/-- coeFn of the weighted Fourier component: `√W • 𝓕(projⱼ w)` a.e.
@isnad1 id=eventual.1h2v.s16.6b3c699361bc from=translated src=- shape=85289726 vocab=bd5c92e0
-/
theorem weightedFourierComponent_coeFn (w : L2VF_R3) (hw : memH1VF_R3 w) (j : Fin 3) :
    (weightedFourierComponent w hw j : Domain3 → ℂ)
      =ᵐ[volume] fun ξ => (sqrtViscousWeight ξ : ℂ) • (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ :=
  MemLp.coeFn_toLp _

/-- **Additivity of the weighted Fourier component** (in its `H¹` argument).
@isnad1 id=eq.3h3v.s15.60bd31350034 from=translated src=- shape=c5a97212 vocab=99834e33
-/
theorem weightedFourierComponent_add (w₁ w₂ : L2VF_R3) (hw₁ : memH1VF_R3 w₁) (hw₂ : memH1VF_R3 w₂)
    (hw : memH1VF_R3 (w₁ + w₂)) (j : Fin 3) :
    weightedFourierComponent (w₁ + w₂) hw j
      = weightedFourierComponent w₁ hw₁ j + weightedFourierComponent w₂ hw₂ j := by
  apply Lp.ext
  have hFeq : (𝓕 (L2VF_projComponentC_R3 j (w₁ + w₂)) : L2C_R3)
      = (𝓕 (L2VF_projComponentC_R3 j w₁) : L2C_R3) + 𝓕 (L2VF_projComponentC_R3 j w₂) := by
    rw [map_add (L2VF_projComponentC_R3 j), FourierTransform.fourier_add]
  have hfeq : ((𝓕 (L2VF_projComponentC_R3 j (w₁ + w₂)) : L2C_R3) : Domain3 → ℂ)
      =ᵐ[volume] fun ξ => (𝓕 (L2VF_projComponentC_R3 j w₁) : L2C_R3) ξ
        + (𝓕 (L2VF_projComponentC_R3 j w₂) : L2C_R3) ξ := by
    rw [hFeq]; exact Lp.coeFn_add _ _
  filter_upwards [weightedFourierComponent_coeFn (w₁ + w₂) hw j,
    Lp.coeFn_add (weightedFourierComponent w₁ hw₁ j) (weightedFourierComponent w₂ hw₂ j),
    weightedFourierComponent_coeFn w₁ hw₁ j, weightedFourierComponent_coeFn w₂ hw₂ j, hfeq]
    with ξ h1 h2 h3 h4 h5
  rw [h1, h2, Pi.add_apply, h3, h4, h5, smul_add]

/-- **ℝ-homogeneity of the weighted Fourier component.**
@isnad1 id=eq.2h3v.s17.b53acc9d0dae from=translated src=- shape=3652b805 vocab=0f7b0551
-/
theorem weightedFourierComponent_smul (r : ℝ) (w : L2VF_R3) (hw : memH1VF_R3 w)
    (hrw : memH1VF_R3 (r • w)) (j : Fin 3) :
    weightedFourierComponent (r • w) hrw j = r • weightedFourierComponent w hw j := by
  apply Lp.ext
  have hFeq : (𝓕 (L2VF_projComponentC_R3 j (r • w)) : L2C_R3)
      = r • (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) := by
    rw [map_smul (L2VF_projComponentC_R3 j)]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), FourierTransform.fourier_smul,
      ← RCLike.real_smul_eq_coe_smul (K := ℂ)]
  have hfeq : ((𝓕 (L2VF_projComponentC_R3 j (r • w)) : L2C_R3) : Domain3 → ℂ)
      =ᵐ[volume] fun ξ => r • (𝓕 (L2VF_projComponentC_R3 j w) : L2C_R3) ξ := by
    rw [hFeq]; exact Lp.coeFn_smul r _
  filter_upwards [weightedFourierComponent_coeFn (r • w) hrw j,
    Lp.coeFn_smul r (weightedFourierComponent w hw j), weightedFourierComponent_coeFn w hw j, hfeq]
    with ξ h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3, h4]
  simp only [Complex.real_smul, smul_eq_mul]
  ring

/-! ### Bounded multiplier on `L2C_R3` and its Bochner commute

The bounded-multiplier machinery is generic in the ambient measure space and lives in
`LerayHopf.Analysis.BoundedMultiplier`.  The wrappers below are thin `Domain3`
instantiations under the original names, kept so the many existing call sites in
`SobolevEmbedding.lean` and `AubinLionsLimitPassage.lean` (which invoke these names
without an explicit measure argument) are unaffected. -/

/-- `mulBdd m hm hC g` is the `L²`-class of `ξ ↦ (m ξ : ℂ) • g ξ`, for a bounded
a.e.-strongly-measurable real multiplier `m` (bound `C`).  Well-defined because the bounded
multiplier keeps `g ∈ L²` inside `L²` (Hölder `∞ · 2 ⊆ 2`).
@isnad1 id=memlp.1h2v.s12.ce03334ab86c from=translated src=- shape=9374077c vocab=62a7262c
-/
theorem memLp_mulBdd (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) (g : L2C_R3) :
    MemLp (fun ξ => (m ξ : ℂ) • (g : Domain3 → ℂ) ξ) 2 (volume : Measure Domain3) :=
  BoundedMultiplier.memLp_mulBdd (volume : Measure Domain3) m hmem g

/-- `Domain3`-instantiated wrapper around `BoundedMultiplier.mulBdd`: the `L²`-class of
`ξ ↦ (m ξ : ℂ) • g ξ` for a bounded a.e.-strongly-measurable real multiplier `m`. -/
noncomputable def mulBdd (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3))
    (g : L2C_R3) : L2C_R3 :=
  BoundedMultiplier.mulBdd (volume : Measure Domain3) m hmem g

/-- The `Lp`-coercion of `mulBdd m g` agrees a.e. with the pointwise multiplier action
`ξ ↦ (m ξ : ℂ) • g ξ`.
@isnad1 id=eventual.1h2v.s13.74576704544d from=translated src=- shape=b6eb7c32 vocab=6105a371
-/
theorem mulBdd_coeFn (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) (g : L2C_R3) :
    (mulBdd m hmem g : Domain3 → ℂ)
      =ᵐ[volume] fun ξ => (m ξ : ℂ) • (g : Domain3 → ℂ) ξ :=
  BoundedMultiplier.mulBdd_coeFn (volume : Measure Domain3) m hmem g

/-- **ℝ-homogeneity of the bounded multiplier.**
@isnad1 id=eq.1h3v.s16.7aa186f1f636 from=translated src=- shape=50e90930 vocab=8a7792ed
-/
theorem mulBdd_smul (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) (r : ℝ)
    (g : L2C_R3) :
    mulBdd m hmem (r • g) = r • mulBdd m hmem g :=
  BoundedMultiplier.mulBdd_smul (volume : Measure Domain3) m hmem r g

/-- **Additivity of the bounded multiplier.**
@isnad1 id=eq.1h3v.s15.56eaa16b24c0 from=translated src=- shape=32360d07 vocab=5860764c
-/
theorem mulBdd_add (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) (g h : L2C_R3) :
    mulBdd m hmem (g + h) = mulBdd m hmem g + mulBdd m hmem h :=
  BoundedMultiplier.mulBdd_add (volume : Measure Domain3) m hmem g h

/-- **Operator bound for the bounded multiplier:** `‖mulBdd m g‖ ≤ C ‖g‖` whenever `|m| ≤ C`
everywhere (the sup bound on `m` dominates the operator).
@isnad1 id=le.3h3v.s13.74a0f05747e1 from=translated src=- shape=b7a1d633 vocab=c609ca0e
-/
theorem norm_mulBdd_le (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) {C : ℝ}
    (hC : 0 ≤ C) (hmle : ∀ ξ, |m ξ| ≤ C) (g : L2C_R3) :
    ‖mulBdd m hmem g‖ ≤ C * ‖g‖ :=
  BoundedMultiplier.norm_mulBdd_le (volume : Measure Domain3) m hmem hC hmle g

/-- **Subtractivity of the bounded multiplier.**
@isnad1 id=eq.1h3v.s15.55d27aea7f16 from=translated src=- shape=32360d07 vocab=11b99442
-/
theorem mulBdd_sub (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) (g h : L2C_R3) :
    mulBdd m hmem (g - h) = mulBdd m hmem g - mulBdd m hmem h :=
  BoundedMultiplier.mulBdd_sub (volume : Measure Domain3) m hmem g h

/-- **Continuity of the bounded multiplier operator** (it is `C`-Lipschitz).
@isnad1 id=continuo.3h2v.s15.836883270bd8 from=translated src=- shape=d60af0b3 vocab=9ddaa044
-/
theorem continuous_mulBdd (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) {C : ℝ}
    (hC : 0 ≤ C) (hmle : ∀ ξ, |m ξ| ≤ C) :
    Continuous (fun g => mulBdd m hmem g) :=
  BoundedMultiplier.continuous_mulBdd (volume : Measure Domain3) m hmem hC hmle

/-- **Self-adjointness of the bounded real multiplier.**  `⟪c, mulBdd m g⟫ = ⟪mulBdd m c, g⟫`.
@isnad1 id=eq.1h3v.s13.cc9226ec4051 from=translated src=- shape=cdf56eb2 vocab=bb6c3048
-/
theorem inner_mulBdd_left (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3)) (c g : L2C_R3) :
    (inner ℂ c (mulBdd m hmem g) : ℂ) = inner ℂ (mulBdd m hmem c) g :=
  BoundedMultiplier.inner_mulBdd_left (volume : Measure Domain3) m hmem c g

/-- **Bounded-multiplier Bochner commute (interval integral).**  For a curve `G` that is
interval-integrable on `[a,b]`, the bounded multiplier commutes with the Bochner integral:
`mulBdd m (∫_a^b G s ds) = ∫_a^b mulBdd m (G s) ds`.
@isnad1 id=eq.3h4v.s15.2c1aa256efc4 from=translated src=- shape=933b3207 vocab=54aaf2b2
-/
theorem mulBdd_intervalIntegral_comm (m : Domain3 → ℝ)
    (hmem : MemLp (fun ξ : Domain3 => (m ξ : ℂ)) ⊤ (volume : Measure Domain3))
    {G : ℝ → L2C_R3} {a b : ℝ}
    (hGint : IntervalIntegrable G volume a b)
    (hMGint : IntervalIntegrable (fun s => mulBdd m hmem (G s)) volume a b) :
    mulBdd m hmem (∫ s in a..b, G s) = ∫ s in a..b, mulBdd m hmem (G s) :=
  BoundedMultiplier.mulBdd_intervalIntegral_comm (volume : Measure Domain3) m hmem hGint hMGint

end LerayHopf
