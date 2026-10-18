/-
Copyright (c) 2026 Benny Avelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benny Avelin
-/
import Tengoku.Absorptioncutoff.AbsorptionCutoff.Chains
import Tengoku.Absorptioncutoff.AbsorptionCutoff.Estimates
import Tengoku.Absorptioncutoff.AbsorptionCutoff.InvariantSelection
import Tengoku.Absorptioncutoff.AbsorptionCutoff.MeanMap.Dynamics
import Tengoku.Seed.Probability.Distributions.Gamma
import Tengoku.Seed.Probability.Independence.CharacteristicFunction
import Tengoku.Seed.Probability.Moments.ComplexMGF

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Gaussian radial laws and Gamma negative moments

This module starts the radial-moment infrastructure used in the paper's
supercritical dimension cutoff. It identifies the squared norm of `gaussianVec N`
with a sum of independent squared standard Gaussians, the representation of
`χ_N²` that will be sent to the Gamma law with shape `N / 2` and rate `1 / 2`.

It also proves the analytic half of the exact negative-moment calculation:
the sharp integrability condition and Gamma-function integral for a negative
real power against a Gamma density.
-/

open MeasureTheory ProbabilityTheory BigOperators Filter Topology Set
open scoped ENNReal NNReal Real

namespace AbsorptionCutoff

/-- Squared Euclidean norm of a vector in `ℝ^N`. Under `gaussianVec N`, this is
the paper's `χ_N²`. -/
noncomputable def gaussianSquaredNorm (N : ℕ) (g : Fin N → ℝ) : ℝ :=
  ∑ i, (g i) ^ 2

/-- Euclidean norm associated with `gaussianSquaredNorm`. This is explicit
because the default norm on the function space `Fin N → ℝ` is the sup norm. -/
noncomputable def gaussianEuclideanNorm (N : ℕ) (g : Fin N → ℝ) : ℝ :=
  Real.sqrt (gaussianSquaredNorm N g)

lemma measurable_gaussianSquaredNorm (N : ℕ) : Measurable (gaussianSquaredNorm N) := by
  unfold gaussianSquaredNorm
  fun_prop

lemma gaussianSquaredNorm_nonneg (N : ℕ) (g : Fin N → ℝ) :
    0 ≤ gaussianSquaredNorm N g := by
  unfold gaussianSquaredNorm
  positivity

/-- Coordinatewise squaring sends the standard Gaussian product to the product
of the one-dimensional squared-Gaussian laws. -/
lemma map_coordinatewise_sq_gaussianVec (N : ℕ) :
    (gaussianVec N).map (fun g i => (g i) ^ 2) =
      Measure.pi (fun _ : Fin N => (gaussianReal 0 1).map (fun x : ℝ => x ^ 2)) := by
  unfold gaussianVec
  exact Measure.pi_map_pi (μ := fun _ : Fin N => gaussianReal 0 1)
    (f := fun _ : Fin N => fun x : ℝ => x ^ 2) (fun _ => by fun_prop)

/-- `χ_N²` is represented as the sum of `N` independent squared standard
Gaussians. This is the distributional bridge to the Gamma law with shape
`N / 2` and rate `1 / 2`. -/
lemma map_gaussianSquaredNorm_gaussianVec (N : ℕ) :
    (gaussianVec N).map (gaussianSquaredNorm N) =
      (Measure.pi (fun _ : Fin N => (gaussianReal 0 1).map (fun x : ℝ => x ^ 2))).map
        (fun y => ∑ i, y i) := by
  rw [← map_coordinatewise_sq_gaussianVec]
  rw [Measure.map_map]
  · congr 1
  · fun_prop
  · fun_prop

/-- MGF of a Gamma law on its interval of convergence. -/
lemma mgf_id_gammaMeasure_of_lt {a r t : ℝ}
    (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    mgf id (gammaMeasure a r) t = (r / (r - t)) ^ a := by
  have hpdf : Measurable (gammaPDF a r) :=
    (measurable_gammaPDFReal a r).ennreal_ofReal
  rw [mgf, gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul hpdf
      (ae_of_all _ fun x => by simp [gammaPDF])]
  simp_rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), id_eq,
    smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ici 0) (f :=
    fun x : ℝ => gammaPDFReal a r x * Real.exp (t * x)) (by
      intro x hx
      rw [gammaPDFReal, ite_eq_right]
      · simp
      · exact not_le.mpr (lt_of_not_ge hx))]
  rw [integral_Ici_eq_integral_Ioi]
  rw [setIntegral_congr_fun measurableSet_Ioi
    (g := fun x => r ^ a / Real.Gamma a *
      (x ^ (a - 1) * Real.exp (-((r - t) * x))))]
  · rw [integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (a := a) (r := r - t) ha (sub_pos.mpr ht)]
    rw [one_div, Real.inv_rpow (sub_pos.mpr ht).le]
    rw [Real.div_rpow hr.le (sub_pos.mpr ht).le]
    field_simp [(Real.Gamma_pos_of_pos ha).ne']
  · intro x hx
    have hx0 : 0 < x := hx
    simp only [gammaPDFReal, ite_eq_left hx0.le]
    have hexp : Real.exp (-(r * x)) * Real.exp (t * x) =
        Real.exp (-((r - t) * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, hexp]
    exact mul_assoc _ _ _

/-- MGF of the square of a standard real Gaussian. -/
lemma mgf_sq_gaussianReal_of_lt {t : ℝ} (ht : t < 1 / 2) :
    mgf (fun x : ℝ => x ^ 2) (gaussianReal 0 1) t =
      ((1 / 2 : ℝ) / (1 / 2 - t)) ^ (1 / 2 : ℝ) := by
  rw [mgf, integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul]
  change (∫ x : ℝ, (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) *
      Real.exp (t * x ^ 2)) =
    ((1 / 2 : ℝ) / (1 / 2 - t)) ^ (1 / 2 : ℝ)
  rw [show (fun x : ℝ => (√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2) *
      Real.exp (t * x ^ 2)) =
      fun x => (√(2 * π))⁻¹ * Real.exp (-((1 / 2 - t) * x ^ 2)) by
    funext x
    have hexp : Real.exp (-(x ^ 2) / 2) * Real.exp (t * x ^ 2) =
        Real.exp (-((1 / 2 - t) * x ^ 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [mul_assoc, hexp]]
  rw [integral_const_mul]
  rw [show (∫ a : ℝ, Real.exp (-((1 / 2 - t) * a ^ 2))) =
      √(π / (1 / 2 - t)) by
    convert integral_gaussian (1 / 2 - t) using 1
    ring_nf]
  have hden : 0 < 1 / 2 - t := sub_pos.mpr ht
  rw [show ((1 / 2 : ℝ) / (1 / 2 - t)) ^ (1 / 2 : ℝ) =
      √((1 / 2) / (1 / 2 - t)) by rw [Real.sqrt_eq_rpow]]
  rw [inv_mul_eq_div]
  rw [← Real.sqrt_div (div_nonneg Real.pi_pos.le hden.le)]
  congr 1
  field_simp [ne_of_gt hden, ne_of_gt Real.pi_pos]

lemma integrable_exp_mul_sq_gaussianReal_of_lt {t : ℝ} (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff (by fun_prop)
    (ae_of_all _ fun x => by simp [gaussianPDF])]
  simp only [gaussianPDF]
  simp_rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _)]
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  have hbase : Integrable (fun x : ℝ => Real.exp (-((1 / 2 - t) * x ^ 2))) := by
    convert integrable_exp_neg_mul_sq (sub_pos.mpr ht) using 1
    ring_nf
  refine hbase.const_mul (√(2 * π))⁻¹ |>.congr (ae_of_all _ fun x => ?_)
  have hexp : Real.exp (t * x ^ 2) * Real.exp (-(x ^ 2) / 2) =
      Real.exp (-((1 / 2 - t) * x ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  symm
  calc
    Real.exp (t * x ^ 2) * ((√(2 * π))⁻¹ * Real.exp (-(x ^ 2) / 2)) =
        (√(2 * π))⁻¹ *
          (Real.exp (t * x ^ 2) * Real.exp (-(x ^ 2) / 2)) := by ring
    _ = (√(2 * π))⁻¹ * Real.exp (-((1 / 2 - t) * x ^ 2)) := by rw [hexp]

/-- Equality of MGFs on an open interval around zero determines the pushforward law. -/
lemma map_eq_of_mgf_eq_on_Ioo
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} {μ' : Measure Ω'} [IsFiniteMeasure μ] [IsFiniteMeasure μ']
    {X : Ω → ℝ} {Y : Ω' → ℝ} {a b : ℝ}
    (hX : Measurable X) (hY : Measurable Y) (ha : a < 0) (hb : 0 < b)
    (hXint : ∀ t ∈ Set.Ioo a b, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hYint : ∀ t ∈ Set.Ioo a b, Integrable (fun ω => Real.exp (t * Y ω)) μ')
    (hmgf : Set.EqOn (mgf X μ) (mgf Y μ') (Set.Ioo a b)) :
    μ.map X = μ'.map Y := by
  let D : Set ℂ := {z | z.re ∈ Set.Ioo a b}
  have hXsub : D ⊆ {z | z.re ∈ interior (integrableExpSet X μ)} := by
    intro z hz
    refine mem_interior_iff_mem_nhds.mpr (mem_of_superset (Ioo_mem_nhds hz.1 hz.2) ?_)
    intro t ht
    exact hXint t ht
  have hYsub : D ⊆ {z | z.re ∈ interior (integrableExpSet Y μ')} := by
    intro z hz
    refine mem_interior_iff_mem_nhds.mpr (mem_of_superset (Ioo_mem_nhds hz.1 hz.2) ?_)
    intro t ht
    exact hYint t ht
  have hCX : AnalyticOnNhd ℂ (complexMGF X μ) D :=
    analyticOnNhd_complexMGF.mono hXsub
  have hCY : AnalyticOnNhd ℂ (complexMGF Y μ') D :=
    analyticOnNhd_complexMGF.mono hYsub
  have h_real : ∃ᶠ x : ℝ in 𝓝[≠] 0, complexMGF X μ x = complexMGF Y μ' x := by
    apply Filter.Eventually.frequently
    filter_upwards [Filter.Eventually.filter_mono inf_le_left (Ioo_mem_nhds ha hb)] with x hx
    simpa only [complexMGF_ofReal] using
      congr_arg ((↑) : ℝ → ℂ) (hmgf hx)
  have hCEq : Set.EqOn (complexMGF X μ) (complexMGF Y μ') D := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq hCX hCY
      ((convex_Ioo a b).linear_preimage Complex.reLm).isPreconnected
      (z₀ := (0 : ℂ)) (by simp [D, ha, hb]) ?_
    rw [frequently_iff_seq_forall] at h_real ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
    refine ⟨fun n => xs n, ?_, fun n => ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
      constructor
      · change Tendsto (Complex.ofReal ∘ xs) atTop (𝓝 (0 : ℂ))
        exact Complex.continuous_ofReal.continuousAt.tendsto.comp hx_tendsto.1
      · simpa using hx_tendsto.2
    · simp [hx_eq]
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_mul_I hX.aemeasurable, ← complexMGF_mul_I hY.aemeasurable]
  exact hCEq (by simp [D, ha, hb])

lemma iIndepFun_gaussian_coordinate_sq (N : ℕ) :
    iIndepFun (fun i (g : Fin N → ℝ) => (g i) ^ 2) (gaussianVec N) := by
  have hEval : iIndepFun (fun i (g : Fin N → ℝ) => g i) (gaussianVec N) := by
    unfold gaussianVec
    exact iIndepFun_pi fun _ => aemeasurable_id
  change iIndepFun
    (fun i => (fun x : ℝ => x ^ 2) ∘ fun g : Fin N → ℝ => g i) (gaussianVec N)
  exact hEval.comp (fun (_ : Fin N) (x : ℝ) => x ^ 2)
    (fun _ => (by fun_prop : Measurable (fun x : ℝ => x ^ 2)))

lemma mgf_gaussianSquaredNorm_of_lt (N : ℕ) {t : ℝ} (ht : t < 1 / 2) :
    mgf (gaussianSquaredNorm N) (gaussianVec N) t =
      ((1 / 2 : ℝ) / (1 / 2 - t)) ^ ((N : ℝ) / 2) := by
  have hcoord (i : Fin N) :
      mgf (fun g : Fin N → ℝ => (g i) ^ 2) (gaussianVec N) t =
        ((1 / 2 : ℝ) / (1 / 2 - t)) ^ (1 / 2 : ℝ) := by
    rw [← mgf_id_map (by fun_prop :
      Measurable (fun g : Fin N → ℝ => (g i) ^ 2)).aemeasurable]
    rw [show (fun g : Fin N → ℝ => (g i) ^ 2) =
        (fun x : ℝ => x ^ 2) ∘ (fun g : Fin N → ℝ => g i) from rfl]
    rw [← Measure.map_map (μ := gaussianVec N) (f := fun g : Fin N → ℝ => g i)
      (g := fun x : ℝ => x ^ 2) (by fun_prop) (measurable_pi_apply i)]
    unfold gaussianVec
    rw [Measure.pi_map_eval]
    simp only [measure_univ, Finset.prod_const_one, one_smul, one_div]
    rw [mgf_id_map (by fun_prop : Measurable (fun x : ℝ => x ^ 2)).aemeasurable]
    simpa [one_div] using mgf_sq_gaussianReal_of_lt ht
  have hsum := (iIndepFun_gaussian_coordinate_sq N).mgf_sum
    (fun _ => by fun_prop) (Finset.univ : Finset (Fin N)) (t := t)
  rw [show gaussianSquaredNorm N =
      ∑ i : Fin N, (fun g : Fin N → ℝ => (g i) ^ 2) by
    funext g
    simp [gaussianSquaredNorm, Finset.sum_apply]]
  rw [hsum]
  simp_rw [hcoord]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hbase : 0 ≤ (1 / 2 : ℝ) / (1 / 2 - t) := by positivity
  rw [← Real.rpow_mul_natCast hbase]
  congr 1
  ring

lemma integrable_exp_mul_gaussianSquaredNorm_of_lt (N : ℕ) {t : ℝ}
    (ht : t < 1 / 2) :
    Integrable (fun g => Real.exp (t * gaussianSquaredNorm N g)) (gaussianVec N) := by
  have hsum := (iIndepFun_gaussian_coordinate_sq N).integrable_exp_mul_sum
    (fun _ => by fun_prop) (s := Finset.univ)
    (fun i _ => by
      refine Integrable.comp_measurable (f := fun g : Fin N → ℝ => g i)
        (g := fun x : ℝ => Real.exp (t * x ^ 2)) ?_ (measurable_pi_apply i)
      unfold gaussianVec
      rw [Measure.pi_map_eval]
      simp only [measure_univ, Finset.prod_const_one, one_smul]
      exact integrable_exp_mul_sq_gaussianReal_of_lt ht)
  simpa only [gaussianSquaredNorm, Finset.sum_apply] using hsum

/-- On the positive half-line, multiplying a Gamma density of shape `a` by
`x⁻ᵖ` changes the power in the Gamma integrand from `a - 1` to
`a - p - 1`. -/
lemma neg_rpow_mul_gammaPDFReal_of_pos {a r p x : ℝ} (hx : 0 < x) :
    x ^ (-p) * gammaPDFReal a r x =
      r ^ a / Real.Gamma a *
        (x ^ (a - p - 1) * Real.exp (-(r * x))) := by
  rw [gammaPDFReal, ite_eq_left hx.le]
  calc
    x ^ (-p) * (r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x))) =
        r ^ a / Real.Gamma a * (x ^ (-p) * x ^ (a - 1)) *
          Real.exp (-(r * x)) := by ring
    _ = r ^ a / Real.Gamma a *
        (x ^ (a - p - 1) * Real.exp (-(r * x))) := by
      rw [← Real.rpow_add hx]
      rw [show -p + (a - 1) = a - p - 1 by ring]
      ring

/-- Exact negative-moment integral for a Gamma density:
`∫₀∞ x⁻ᵖ f_{a,r}(x) dx = rᵖ Γ(a-p) / Γ(a)` for `p < a`.

After the remaining chi-square pushforward is established, specializing to
`a = N / 2` and `r = 1 / 2` gives the paper's exact negative moments of
`χ_N²`. -/
lemma integral_neg_rpow_mul_gammaPDFReal_Ioi {a r p : ℝ}
    (hr : 0 < r) (hp : p < a) :
    ∫ x : ℝ in Set.Ioi 0, x ^ (-p) * gammaPDFReal a r x =
      r ^ p * Real.Gamma (a - p) / Real.Gamma a := by
  rw [setIntegral_congr_fun measurableSet_Ioi]
  · rw [integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (show 0 < a - p by linarith) hr]
    change (r ^ a / Real.Gamma a) *
        ((1 / r) ^ (a - p) * Real.Gamma (a - p)) =
      r ^ p * Real.Gamma (a - p) / Real.Gamma a
    rw [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
    have hpow : r ^ a * r ^ (-(a - p)) = r ^ p := by
      rw [← Real.rpow_add hr]
      congr 1
      ring
    calc
      r ^ a / Real.Gamma a * (r ^ (-(a - p)) * Real.Gamma (a - p)) =
          (r ^ a * r ^ (-(a - p))) * Real.Gamma (a - p) / Real.Gamma a := by ring
      _ = r ^ p * Real.Gamma (a - p) / Real.Gamma a := by rw [hpow]
  · intro x hx
    exact neg_rpow_mul_gammaPDFReal_of_pos hx

/-- For every fixed `A > 1`, all sufficiently large dimensions exceed two
and satisfy the paper's explicit reciprocal-moment criterion. -/
lemma exists_dimension_threshold_for_reciprocal_moment
    {A : ℝ} (hA : 1 < A) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N →
      2 < N ∧ 2 * A ^ 2 < (A ^ 2 - 1) * N := by
  have hcoef : 0 < A ^ 2 - 1 := by nlinarith
  obtain ⟨N₀, hN₀⟩ :=
    exists_nat_gt (2 * A ^ 2 / (A ^ 2 - 1))
  refine ⟨max 3 N₀, fun N hN => ⟨by omega, ?_⟩⟩
  have hN₀N : N₀ ≤ N := le_trans (Nat.le_max_right 3 N₀) hN
  have hN₀Nreal : (N₀ : ℝ) ≤ N := by exact_mod_cast hN₀N
  have hquot : 2 * A ^ 2 / (A ^ 2 - 1) < (N : ℝ) :=
    hN₀.trans_le hN₀Nreal
  simpa [mul_comm] using (div_lt_iff₀ hcoef).1 hquot

/-- At fixed dimension and Gaussian sample, the squared-radius update divided
by its input converges at the origin to the paper's linearized multiplier
`A² ‖g‖₂² / N`. -/
lemma Fmap_div_tendsto_gaussianSquaredNorm {A : ℝ} (hA : A ≠ 0)
    (N : ℕ) (g : Fin N → ℝ) :
    Tendsto (fun q => Fmap A N q g / q) (𝓝[>] 0)
      (𝓝 (A ^ 2 * gaussianSquaredNorm N g / N)) := by
  have hcoord (i : Fin N) :
      Tendsto (fun q => Real.tanh (A * Real.sqrt q * g i) ^ 2 / q)
        (𝓝[>] 0) (𝓝 ((A * g i) ^ 2)) := by
    by_cases hi : g i = 0
    · simp [hi]
    · exact tendsto_tanh_sq_div_ratio hA hi
  have hsum :
      Tendsto
        (fun q => ∑ i : Fin N, Real.tanh (A * Real.sqrt q * g i) ^ 2 / q)
        (𝓝[>] 0) (𝓝 (∑ i : Fin N, (A * g i) ^ 2)) :=
    tendsto_finsetSum Finset.univ (fun i _ => hcoord i)
  have hscaled := hsum.const_mul ((N : ℝ)⁻¹)
  have hlimit :
      (N : ℝ)⁻¹ * ∑ i : Fin N, (A * g i) ^ 2 =
        A ^ 2 * gaussianSquaredNorm N g / N := by
    unfold gaussianSquaredNorm
    simp_rw [mul_pow]
    rw [← Finset.mul_sum]
    ring
  rw [hlimit] at hscaled
  refine hscaled.congr' ?_
  exact Filter.Eventually.of_forall fun q => by
    unfold Fmap
    simp only
    rw [mul_div_assoc, Finset.sum_div]

/-- For each fixed Gaussian sample, the radial update-to-input ratio is
nonincreasing on the positive half-line. -/
lemma antitoneOn_Fmap_div (A : ℝ) (N : ℕ) (g : Fin N → ℝ) :
    AntitoneOn (fun q => Fmap A N q g / q) (Set.Ioi (0 : ℝ)) := by
  intro q hq R hR hqR
  unfold Fmap
  simp only
  rw [mul_div_assoc, mul_div_assoc, Finset.sum_div, Finset.sum_div]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  apply Finset.sum_le_sum
  intro i _
  have harg (s : ℝ) :
      A * Real.sqrt s * g i = (A * g i) * Real.sqrt s := by ring
  by_cases hi : A * g i = 0
  · simp [harg, hi]
  · by_cases hqRne : q = R
    · subst R
      exact le_rfl
    · rw [harg q, harg R]
      exact (tanh_sq_comp_div_strictAnti' hi hq hR
        (lt_of_le_of_ne hqR hqRne)).le

/-- In particular, a smaller positive input gives the lower bound used to
dominate reciprocal radial-update ratios. -/
lemma Fmap_div_ge_of_pos_of_le {A : ℝ} {N : ℕ} {q R : ℝ}
    (g : Fin N → ℝ) (hq : 0 < q) (hqR : q ≤ R) :
    Fmap A N R g / R ≤ Fmap A N q g / q :=
  antitoneOn_Fmap_div A N g hq (hq.trans_le hqR) hqR

/-- A global quadratic-near-zero, constant-away-from-zero lower bound for
`tanh²`. This is the pointwise small-ball input for fixed-radius reciprocal
integrability. -/
lemma tanh_one_sq_mul_min_sq_one_le (x : ℝ) :
    Real.tanh 1 ^ 2 * min (x ^ 2) 1 ≤ Real.tanh x ^ 2 := by
  have htanh_abs : Real.tanh |x| ^ 2 = Real.tanh x ^ 2 := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, Real.tanh_neg, neg_sq]
  by_cases hx0 : x = 0
  · simp [hx0]
  by_cases hxsmall : x ^ 2 ≤ 1
  · rw [min_eq_left hxsmall]
    have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
    have hratio :=
      (tanh_sq_comp_div_strictAnti (c := (1 : ℝ)) zero_lt_one).antitoneOn
        (Set.mem_Ioi.mpr hx2pos) (Set.mem_Ioi.mpr zero_lt_one) hxsmall
    norm_num [Real.sqrt_sq_eq_abs] at hratio
    rw [htanh_abs] at hratio
    exact (le_div_iff₀ hx2pos).1 hratio
  · rw [min_eq_right (le_of_not_ge hxsmall)]
    have habs : 1 ≤ |x| := by
      have habssq : |x| ^ 2 = x ^ 2 := sq_abs x
      nlinarith [abs_nonneg x]
    have htanh_mono : Real.tanh 1 ≤ Real.tanh |x| :=
      tanh_strictMono.monotone habs
    have htanh_one_nonneg : 0 ≤ Real.tanh 1 := by
      rw [← Real.tanh_zero]
      exact tanh_strictMono.monotone zero_le_one
    have htanh_abs_nonneg : 0 ≤ Real.tanh |x| := by
      rw [← Real.tanh_zero]
      exact tanh_strictMono.monotone (abs_nonneg x)
    calc
      Real.tanh 1 ^ 2 * 1 = Real.tanh 1 ^ 2 := mul_one _
      _ ≤ Real.tanh |x| ^ 2 := by nlinarith
      _ = Real.tanh x ^ 2 := htanh_abs

/-- Summing the global `tanh²` lower bound controls the Gaussian radial update
by `S / (1 + S)`, where `S = ‖g‖₂²`. -/
lemma sum_tanh_sq_lower_gaussianSquaredNorm {A R : ℝ} (hR : 0 ≤ R)
    (N : ℕ) (g : Fin N → ℝ) :
    Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1 *
        (gaussianSquaredNorm N g / (1 + gaussianSquaredNorm N g)) ≤
      ∑ i, Real.tanh (A * Real.sqrt R * g i) ^ 2 := by
  let S := gaussianSquaredNorm N g
  let α := min (A ^ 2 * R) 1
  have hS : 0 ≤ S := gaussianSquaredNorm_nonneg N g
  have hα : 0 ≤ α := by
    dsimp [α]
    exact le_min (mul_nonneg (sq_nonneg A) hR) zero_le_one
  have hden : 0 < 1 + S := by linarith
  have hcoord (i : Fin N) :
      Real.tanh 1 ^ 2 * (α * (g i) ^ 2 / (1 + S)) ≤
        Real.tanh (A * Real.sqrt R * g i) ^ 2 := by
    have hgiS : (g i) ^ 2 ≤ S := by
      dsimp [S, gaussianSquaredNorm]
      exact Finset.single_le_sum (fun j _ => sq_nonneg (g j)) (Finset.mem_univ i)
    have hαc : α ≤ A ^ 2 * R := min_le_left _ _
    have hα1 : α ≤ 1 := min_le_right _ _
    have hscaled_sq :
        (A * Real.sqrt R * g i) ^ 2 = (A ^ 2 * R) * (g i) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hR]
    have hmin :
        α * (g i) ^ 2 / (1 + S) ≤
          min ((A * Real.sqrt R * g i) ^ 2) 1 := by
      apply le_min
      · rw [hscaled_sq]
        apply (div_le_iff₀ hden).2
        have hbase :
            α * (g i) ^ 2 ≤ (A ^ 2 * R) * (g i) ^ 2 :=
          mul_le_mul_of_nonneg_right hαc (sq_nonneg _)
        have hscaled_nonneg : 0 ≤ (A ^ 2 * R) * (g i) ^ 2 :=
          mul_nonneg (mul_nonneg (sq_nonneg A) hR) (sq_nonneg _)
        nlinarith
      · apply (div_le_iff₀ hden).2
        have hbase : α * (g i) ^ 2 ≤ (g i) ^ 2 :=
          mul_le_of_le_one_left (sq_nonneg _) hα1
        linarith
    calc
      Real.tanh 1 ^ 2 * (α * (g i) ^ 2 / (1 + S)) ≤
          Real.tanh 1 ^ 2 * min ((A * Real.sqrt R * g i) ^ 2) 1 :=
        mul_le_mul_of_nonneg_left hmin (sq_nonneg _)
      _ ≤ Real.tanh (A * Real.sqrt R * g i) ^ 2 :=
        tanh_one_sq_mul_min_sq_one_le _
  change Real.tanh 1 ^ 2 * α * (S / (1 + S)) ≤ _
  calc
    Real.tanh 1 ^ 2 * α * (S / (1 + S)) =
        ∑ i, Real.tanh 1 ^ 2 * (α * (g i) ^ 2 / (1 + S)) := by
      dsimp [S, gaussianSquaredNorm]
      calc
        Real.tanh 1 ^ 2 * α *
            ((∑ i, (g i) ^ 2) / (1 + ∑ i, (g i) ^ 2)) =
            Real.tanh 1 ^ 2 *
              (α * ∑ i, (g i) ^ 2 / (1 + ∑ j, (g j) ^ 2)) := by
            rw [Finset.sum_div]
            ring
        _ = Real.tanh 1 ^ 2 *
              ∑ i, α * ((g i) ^ 2 / (1 + ∑ j, (g j) ^ 2)) := by
            rw [Finset.mul_sum]
        _ = ∑ i, Real.tanh 1 ^ 2 *
              (α * ((g i) ^ 2 / (1 + ∑ j, (g j) ^ 2))) := by
            rw [Finset.mul_sum]
        _ = ∑ i, Real.tanh 1 ^ 2 *
              (α * (g i) ^ 2 / (1 + ∑ j, (g j) ^ 2)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ ≤ ∑ i, Real.tanh (A * Real.sqrt R * g i) ^ 2 :=
      Finset.sum_le_sum fun i _ => hcoord i

/-- The reciprocal fixed-radius update ratio is controlled pointwise by a
constant times `1 + ‖g‖₂⁻²`. -/
lemma inv_Fmap_div_le_one_add_inv_gaussianSquaredNorm
    {A R : ℝ} {N : ℕ} (hA : A ≠ 0) (hR : 0 < R) (hN : 0 < N)
    (g : Fin N → ℝ) :
    (Fmap A N R g / R)⁻¹ ≤
      ((N : ℝ) * R / (Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1)) *
        (1 + (gaussianSquaredNorm N g)⁻¹) := by
  let S := gaussianSquaredNorm N g
  let β := Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1
  have hS : 0 ≤ S := gaussianSquaredNorm_nonneg N g
  have htanh : 0 < Real.tanh 1 := by
    rw [← Real.tanh_zero]
    exact tanh_strictMono zero_lt_one
  have hα : 0 < min (A ^ 2 * R) 1 := by
    exact lt_min (mul_pos (sq_pos_of_ne_zero hA) hR) zero_lt_one
  have hβ : 0 < β := mul_pos (sq_pos_of_pos htanh) hα
  have hNR : 0 < (N : ℝ) * R :=
    mul_pos (by exact_mod_cast hN) hR
  have hraw :
      β * (S / (1 + S)) ≤
        ∑ i, Real.tanh (A * Real.sqrt R * g i) ^ 2 := by
    exact sum_tanh_sq_lower_gaussianSquaredNorm hR.le N g
  have hlower :
      β * (S / (1 + S)) / ((N : ℝ) * R) ≤ Fmap A N R g / R := by
    calc
      β * (S / (1 + S)) / ((N : ℝ) * R) =
          ((N : ℝ) * R)⁻¹ * (β * (S / (1 + S))) := by ring
      _ ≤ ((N : ℝ) * R)⁻¹ *
          ∑ i, Real.tanh (A * Real.sqrt R * g i) ^ 2 :=
        mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hNR.le)
      _ = Fmap A N R g / R := by
        unfold Fmap
        field_simp [hNR.ne']
  by_cases hS0 : S = 0
  · have hgi (i : Fin N) : g i = 0 := by
      have hsqi : (g i) ^ 2 = 0 := by
        apply (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ => sq_nonneg (g j))).1
            (show (∑ j, (g j) ^ 2) = 0 by simpa [S, gaussianSquaredNorm] using hS0)
        exact Finset.mem_univ i
      exact sq_eq_zero_iff.mp hsqi
    have hconst_nonneg :
        0 ≤ (N : ℝ) * R / (Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1) :=
      div_nonneg hNR.le hβ.le
    simp [Fmap, hgi, hS0, S, hconst_nonneg]
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hS0)
    have hLpos :
        0 < β * (S / (1 + S)) / ((N : ℝ) * R) := by positivity
    calc
      (Fmap A N R g / R)⁻¹ ≤
          (β * (S / (1 + S)) / ((N : ℝ) * R))⁻¹ :=
        inv_anti₀ hLpos hlower
      _ = ((N : ℝ) * R / β) * (1 + S⁻¹) := by
        field_simp [hβ.ne', hNR.ne', hSpos.ne']
        ring
      _ = ((N : ℝ) * R /
            (Real.tanh 1 ^ 2 * min (A ^ 2 * R) 1)) *
          (1 + (gaussianSquaredNorm N g)⁻¹) := by
        rfl

end AbsorptionCutoff
