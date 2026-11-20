/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.CausalCone
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.SDProfile
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.BrownianDensity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `lem:bridge-exponents`: from the causal cone to the line's cone

Home: line/cone:lem:bridge-exponents

What is built here is the `SDProfile` of `eq:bridge-profile`: Gaussian coefficient `b₀/2` and
folded profile `k(x) = 2x∫₀^∞ g_u(x)k_I(u)du/u`, with exponent `F_I(ω²/2)`. So
`bridge_exponents` is a map between the two shared cones, `CausalAdmissible` (`CausalCone`) and
`SDProfile` (`SDProfile`): subordinating Brownian motion by a causal kernel family.

Moved from the spatial article's export (`SpatialLine.BridgeExponents`, at `cone-v0.1`),
statements unchanged up to the namespace. The probabilistic reading `bridge_exponents_mixture`,
which mixes the Gaussian laws against a delay law, stayed behind with the Gaussian mixtures.

## The obligation is Tonelli and one change of variables

The statement asks for an `SDProfile` with prescribed data and prescribed exponent; the six
fields of `SDProfile` and the exponent identity are what has to be discharged:

* `k_nonneg`, `k_zero` — termwise;
* `k_antitone` — **not visible term by term**, because the derivative of `x g_u(x)` changes sign
  at `x = √u`. It becomes termwise after the substitution `u = x²v`, which leaves `du/u`
  invariant and turns the whole `x`-dependence into `k_I(x²v)`, nonincreasing in `x` because
  `k_I` is;
* the two integrability fields — Tonelli against `lem:profile-integrability`, the inner integral
  being at most `1 ∧ u`;
* the exponent identity — Tonelli against the Gaussian transform.

## The two integrability fields of `def:causal-admissible`, and where each is spent

The first field weights `k_I` by `du` and the second by `du/u`, and the mixture integrand
carries a `du/u`. The near-origin window is therefore the one that needs work:
`brownianDensity_div_le` bounds `g_u(x)/u` by `16/x⁴` uniformly for `u` in `(0,1]`, which is
where the Gaussian's flatness at `u = 0` pays for the missing power of `u`. Above `1` the
density is at most `1` (`brownianDensity_le_one`) and the second field is used verbatim.
-/

namespace ScaleSpace

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal

/-! ## The mixture density

`ν₂(x) = ∫₀^∞ g_u(x) k_I(u) du/u`, in `ℝ≥0∞` first so that no integrability side condition is
needed to write it down, and as a Bochner integral where the node's statement asks for one.
-/

/-- The weight the substitution `u = x²v` leaves behind:
`ψ(v) = (2πv)^{-1/2}e^{-1/2v}/v`. It carries no `x`, which is the whole point — after the
substitution the entire `x`-dependence of `xν₂(x)` sits inside `k_I(x²v)`.-/
noncomputable def mixWeight (v : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(2 * v)⁻¹) / v

theorem mixWeight_nonneg {v : ℝ} (hv : 0 < v) : 0 ≤ mixWeight v := by
  unfold mixWeight; positivity

namespace CausalAdmissible

/-- `ν₂(x)`, the two-sided Lévy density of the subordinated law, in `ℝ≥0∞`.-/
noncomputable def mixDensityL (F : CausalAdmissible) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (brownianDensity u x * F.k u / u)

/-- **The mixture density is finite off the origin.** The two windows are the two integrability
fields of `def:causal-admissible`, and the near-origin one is the one that needs the Gaussian:
`g_u(x)/u ≤ 16/x⁴` there. At `x = 0` the statement is false in general — `ν₂(0)` is the density
of the Lévy measure at the origin, which need not be finite — and no clause of the node reads
the profile there.-/
theorem mixDensityL_ne_top (F : CausalAdmissible) {x : ℝ} (hx : x ≠ 0) :
    F.mixDensityL x ≠ ⊤ := by
  rw [mixDensityL, lintegral_Ioi_split]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · have hmeas : AEMeasurable
        (fun u : ℝ => ENNReal.ofReal (16 / x ^ 4) * ENNReal.ofReal (F.k u))
        (volume.restrict (Ioo (0 : ℝ) 1)) :=
      aemeasurable_const.mul F.aemeasurable_k_Ioo.ennreal_ofReal
    have hle : (∫⁻ u in Ioo (0 : ℝ) 1, ENNReal.ofReal (brownianDensity u x * F.k u / u))
        ≤ ∫⁻ u in Ioo (0 : ℝ) 1,
            ENNReal.ofReal (16 / x ^ 4) * ENNReal.ofReal (F.k u) := by
      refine setLIntegral_mono_ae hmeas (.of_forall fun u hu => ?_)
      have hu0 : (0 : ℝ) < u := hu.1
      have hk : 0 ≤ F.k u := F.k_nonneg u hu0
      have hb := brownianDensity_div_le hu0 hu.2.le hx
      rw [← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hid : brownianDensity u x * F.k u / u = brownianDensity u x / u * F.k u := by
        field_simp
      rw [hid]
      exact mul_le_mul_of_nonneg_right hb hk
    refine ne_top_of_le_ne_top ?_ hle
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top F.integrable_near_zero
  · have hmeas : AEMeasurable (fun u : ℝ => ENNReal.ofReal (F.k u / u))
        (volume.restrict (Ioi (1 : ℝ))) :=
      ((F.aemeasurable_k_mono (Ioi_subset_Ioi zero_le_one)).div
        aemeasurable_id).ennreal_ofReal
    have hle : (∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (brownianDensity u x * F.k u / u))
        ≤ ∫⁻ u in Ioi (1 : ℝ), ENNReal.ofReal (F.k u / u) := by
      refine setLIntegral_mono_ae hmeas (.of_forall fun u hu => ?_)
      have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
      have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
      have hk : 0 ≤ F.k u := F.k_nonneg u hu0
      refine ENNReal.ofReal_le_ofReal ?_
      have hb := brownianDensity_le_one hu1 x
      have hbn := brownianDensity_nonneg u x
      rw [div_le_div_iff_of_pos_right hu0]
      nlinarith
    exact ne_top_of_le_ne_top F.integrable_at_top hle

/-- **The scaling substitution.** `x ν₂(x) = ∫₀^∞ ψ(v) k_I(x²v) dv`, where `ψ` is `mixWeight`.

This is the identity that makes `eq:bridge-profile`'s monotonicity termwise. The substitution is
`u = x²v`; it leaves `du/u` invariant, and it turns `x g_{x²v}(x)` into `ψ(v)`, a function of
`v` alone. What is left carrying `x` is `k_I(x²v)`, nonincreasing in `x` because `k_I` is
nonincreasing — where the untransformed integrand is not, its `x`-derivative changing sign at
`x = √u`.-/
theorem ofReal_mul_mixDensityL (F : CausalAdmissible) {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal x * F.mixDensityL x
      = ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (mixWeight v * F.k (x ^ 2 * v)) := by
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  rw [mixDensityL, setLIntegral_Ioi_comp_mul hx2, ← mul_assoc,
    ← ENNReal.ofReal_mul hx.le, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun measurableSet_Ioi fun v hv => ?_
  have hv0 : (0 : ℝ) < v := hv
  have hk : 0 ≤ F.k (x ^ 2 * v) := F.k_nonneg _ (mem_Ioi.mpr (by positivity))
  have hbd : brownianDensity (x ^ 2 * v) x
      = (x * Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(2 * v)⁻¹) := by
    rw [brownianDensity_eq (by positivity)]
    congr 1
    · rw [show 2 * Real.pi * (x ^ 2 * v) = x ^ 2 * (2 * Real.pi * v) by ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq hx.le]
    · congr 1
      field_simp
  rw [← ENNReal.ofReal_mul (by positivity), hbd]
  congr 1
  unfold mixWeight
  have hspos : (0 : ℝ) < Real.sqrt (2 * Real.pi * v) := by
    apply Real.sqrt_pos.mpr
    nlinarith [Real.two_le_pi]
  field_simp

/-- **`x ν₂(x)` is nonincreasing on `(0,∞)`**, in `ℝ≥0∞`.-/
theorem mixDensityL_antitone (F : CausalAdmissible) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    ENNReal.ofReal y * F.mixDensityL y ≤ ENNReal.ofReal x * F.mixDensityL x := by
  have hy : (0 : ℝ) < y := lt_of_lt_of_le hx hxy
  rw [F.ofReal_mul_mixDensityL hx, F.ofReal_mul_mixDensityL hy]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : (0 : ℝ) < v := hv
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (mixWeight_nonneg hv0))
  have hsq : x ^ 2 * v ≤ y ^ 2 * v :=
    mul_le_mul_of_nonneg_right (by nlinarith) hv0.le
  exact F.k_antitone (mem_Ioi.mpr (by positivity)) (mem_Ioi.mpr (by positivity)) hsq

/-! ## The folded profile as a real function -/

/-- **`eq:bridge-profile`**: `k(x) = 2x∫₀^∞ g_u(x)k_I(u)du/u`, exactly as
`Skeleton.bridge_exponents` states it, with a Bochner integral.-/
noncomputable def bridgeProfile (F : CausalAdmissible) (x : ℝ) : ℝ :=
  2 * x * ∫ u in Ioi (0 : ℝ), brownianDensity u x * F.k u / u

/-- The Bochner integral is the `toReal` of the `ℝ≥0∞` one. No integrability is required: both
sides are `0` when the integrand is not integrable.-/
theorem integral_eq_mixDensityL (F : CausalAdmissible) (x : ℝ) :
    (∫ u in Ioi (0 : ℝ), brownianDensity u x * F.k u / u) = (F.mixDensityL x).toReal := by
  rw [mixDensityL]
  refine integral_eq_lintegral_of_nonneg_ae ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    have hk := F.k_nonneg u hu0
    have hb := brownianDensity_nonneg u x
    positivity
  · exact (((measurable_brownianDensity_time x).aemeasurable.mul F.aemeasurable_k).div
      aemeasurable_id).aestronglyMeasurable

theorem bridgeProfile_eq (F : CausalAdmissible) {x : ℝ} (hx : 0 ≤ x) :
    F.bridgeProfile x = 2 * (ENNReal.ofReal x * F.mixDensityL x).toReal := by
  rw [bridgeProfile, F.integral_eq_mixDensityL x, ENNReal.toReal_mul, ENNReal.toReal_ofReal hx]
  ring

theorem bridgeProfile_nonneg (F : CausalAdmissible) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ F.bridgeProfile x := by
  rw [F.bridgeProfile_eq hx]; positivity

theorem bridgeProfile_zero (F : CausalAdmissible) : F.bridgeProfile 0 = 0 := by
  simp [bridgeProfile]

/-- **The profile is nonincreasing** — the clause the blueprint calls the content of the lemma.
It is `mixDensityL_antitone` read through `toReal`, which is legitimate because
`mixDensityL_ne_top` makes the larger value finite.-/
theorem bridgeProfile_antitoneOn (F : CausalAdmissible) :
    AntitoneOn F.bridgeProfile (Ioi (0 : ℝ)) := by
  intro x hx y _ hxy
  have hx0 : (0 : ℝ) < x := hx
  rw [F.bridgeProfile_eq hx0.le, F.bridgeProfile_eq (lt_of_lt_of_le hx0 hxy).le]
  have hfin : ENNReal.ofReal x * F.mixDensityL x ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (F.mixDensityL_ne_top hx0.ne')
  have hmono := ENNReal.toReal_mono hfin (F.mixDensityL_antitone hx0 hxy)
  linarith

/-- The profile read against `dx/x`, which is the form the exponent and the integrability
conditions use: `k(x)/x = 2ν₂(x)`.-/
theorem ofReal_bridgeProfile_div (F : CausalAdmissible) {x : ℝ} (hx : 0 < x) :
    ENNReal.ofReal (F.bridgeProfile x / x) = 2 * F.mixDensityL x := by
  rw [bridgeProfile, F.integral_eq_mixDensityL x]
  have hval : 2 * x * (F.mixDensityL x).toReal / x = 2 * (F.mixDensityL x).toReal := by
    field_simp
  rw [hval, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_toReal (F.mixDensityL_ne_top hx.ne')]
  norm_num

end CausalAdmissible

/-! ## The two Gaussian moments, and the truncated bound

The integrability fields need `∫(1 ∧ x²)g_u(x)dx ≤ 1 ∧ u`, which is the total mass on one side
and the variance on the other.
-/

/-- The total mass of `g_u` is `1`.-/
theorem lintegral_brownianDensity_eq_one {u : ℝ} (hu : 0 < u) :
    (∫⁻ x, ENNReal.ofReal (brownianDensity u x)) = 1 := by
  have h := lintegral_brownianDensity hu (fun _ => 1) measurable_const
  have hprob : IsProbabilityMeasure (brownianLaw u) := by rw [brownianLaw]; infer_instance
  simpa using h

namespace CausalAdmissible

/-- **The Tonelli exchange.** Everything the mixture is used for is an integral of the form
`∫₀^∞ w(x) ν₂(x) dx`, and every one of them is computed by exchanging the order: the inner
integral becomes a Gaussian integral of `w`, and the outer one keeps `k_I(u)du/u`.-/
theorem lintegral_Ioi_mul_mixDensityL (F : CausalAdmissible) {w : ℝ → ℝ}
    (hw : Measurable w) (hwnn : ∀ x, 0 ≤ w x) :
    (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (w x) * F.mixDensityL x)
      = ∫⁻ u in Ioi (0 : ℝ),
          (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (w x * brownianDensity u x))
            * ENNReal.ofReal (F.k u / u) := by
  have hswapm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (w p.1 * brownianDensity p.2 p.1) := by
    have h1 : Measurable fun p : ℝ × ℝ => brownianDensity p.2 p.1 :=
      measurable_brownianDensity_uncurry.comp measurable_swap
    exact ((hw.comp measurable_fst).mul h1).ennreal_ofReal
  have hkm : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (F.k p.2 / p.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hbase : AEMeasurable (fun u : ℝ => ENNReal.ofReal (F.k u / u))
        (volume.restrict (Ioi (0 : ℝ))) :=
      (F.aemeasurable_k.div aemeasurable_id).ennreal_ofReal
    exact hbase.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have huncurry : AEMeasurable
      (Function.uncurry fun x u : ℝ =>
        ENNReal.ofReal (w x * brownianDensity u x) * ENNReal.ofReal (F.k u / u))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    hswapm.aemeasurable.mul hkm
  have hL : (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (w x) * F.mixDensityL x)
      = ∫⁻ x in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ),
          ENNReal.ofReal (w x * brownianDensity u x) * ENNReal.ofReal (F.k u / u) := by
    refine setLIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [mixDensityL, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    have hk : 0 ≤ F.k u := F.k_nonneg u hu0
    have hb := brownianDensity_nonneg u x
    rw [← ENNReal.ofReal_mul (hwnn x), ← ENNReal.ofReal_mul (mul_nonneg (hwnn x) hb)]
    congr 1
    ring
  rw [hL, lintegral_lintegral_swap huncurry]
  refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]

/-! ## The two integrability fields -/

theorem aemeasurable_bridgeProfile (F : CausalAdmissible) :
    AEMeasurable F.bridgeProfile (volume.restrict (Ioi (0 : ℝ))) :=
  aemeasurable_restrict_of_antitoneOn measurableSet_Ioi F.bridgeProfile_antitoneOn

/-! ## The exponent identity -/

/-! ## The datum of `lem:bridge-exponents` -/

end CausalAdmissible

/-! ## `lem:bridge-exponents`, the admissibility clause -/

end ScaleSpace
