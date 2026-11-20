/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.InverseGamma
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.BrownianDensity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Student-t law as a Gaussian variance mixture, and its transform

Home: none (the classical normal variance-mixture representation of the Student-t law; second-
demand consumers — Paper V's corner and Student modules, Paper VII's `IsotropicBridge`
`prop:isotropic-bridge-student` — do not yet tag this shared declaration with `\lean`;
ref: @steutel2004infinite, Ch. IV, Example 11.6, p. 226)

The Brownian mixture over the inverse-gamma delay law of shape `a` is the Student-t law with `2a`
degrees of freedom at scale `1` (`bridge_families_bessel`), and its cosine transform is
`2^{1-a}Γ(a)^{-1}|ω|^a K_a(|ω|)` for `ω ≠ 0` (`student_transform`), with `K_ν` the modified
Bessel function of the second kind (`besselK`).

Moved (Q-0363, SSL-8) from Paper V's cone export (`cone-v0.1`, `f28c066e`), statements unchanged
up to the namespace: `besselK` from `SpatialLine.CornerDefs`; `studentDensity` and `studentLaw`
from `SpatialLine.Corners`; `lintegral_exp_mul_of_even` from `SpatialLine.FirstPassage`;
`inverseGamma_brownian_integrand`, `integral_inverseGamma_brownian`, `studentDensity_pos`,
`lintegral_inverseGamma_brownian` and `bridge_families_bessel` from `SpatialLine.BridgeBessel`;
`lintegral_Ioi_rpow_exp_besselKernel`, `lintegral_cosh_exp_eq_besselK`, `besselK_neg`,
`lintegral_exp_neg_inverseGammaLaw`, `besselK_nonneg` and `student_transform` from
`SpatialLine.StudentTransform`. Second demand: Paper V's corner and Student modules, and Paper
VII's `IsotropicBridge` (`prop:isotropic-bridge-student`).

This module imports neither `ScaleSpaceCore.BridgeExponents` nor anything stated in
`CausalAdmissible`: Paper V's package at `cone-v0.1` declares names in
`ScaleSpace.CausalAdmissible` that `ScaleSpaceCore.BridgeExponents` also declares, so a consumer
that imports Paper V's bridge modules can import this one beside them.

## References

* @steutel2004infinite, Ch. IV, Example 11.6, p. 226: a variance mixture of centred normal laws
  has density `f(x) = π^{-1/2} ∫ e^{-x²/t} t^{-1/2} dG(t)`, and with `V = 1/T` standard gamma(`r`)
  distributed this is the Student(`r`) density `B(r, ½)^{-1} (1 + x²)^{-(r+½)}` — the classical
  fact `bridge_families_bessel` states, in the book's scaling (its normal component has variance
  `t/2`, and `r` is half the degrees of freedom). The proof here is direct, from Mathlib's
  Gaussian and gamma integrals, not read off the book.
* @dlmf2026, §10.32.9: the integral representation `K_ν(z) = ∫₀^∞ e^{-z cosh u} cosh(νu) du`
  defining `besselK` (see "The special function Mathlib does not have" below).

## The special function Mathlib does not have

Mathlib (v4.31.0) has no modified Bessel function, so `besselK` is defined by the integral
representation `K_ν(z) = ∫₀^∞ e^{-z\cosh u}\cosh(νu)\,du` (DLMF 10.32.9), valid for `z > 0`. For
`z ≤ 0` the integral diverges and the Bochner integral is junk. Only the two properties the
transform reads are proved here: `besselK_neg` (even in the order) and `besselK_nonneg`.

## The route

The mixture is computed at the densities: the substitution `w = 1/u` (`integral_comp_rpow_Ioi`
at `p = -1`) turns the mixture integral into a Gamma integral, and the computed value being
strictly positive (`studentDensity_pos`) forces the `ℝ≥0∞` integral to be finite without an
integrability proof. The transform conditions on the delay (`fourierCos_bind_brownianLaw`) and
evaluates the Laplace transform of the inverse-gamma law by the substitution `u = c e^v`, which
lands on the defining integral of `K_a` itself, so no Bessel asymptotic is used.
-/

namespace ScaleSpace

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology

/-! ## The modified Bessel function -/

/-- **`K_ν`**, the modified Bessel function of the second kind, by its integral representation
`K_ν(z) = ∫₀^∞ e^{-z\cosh u}\cosh(νu)\,du` (DLMF 10.32.9), valid for `z > 0`.-/
noncomputable def besselK (ν z : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (-(z * Real.cosh u)) * Real.cosh (ν * u)

/-! ## The Student-t law -/

/-- The Student-t density with `2a` degrees of freedom at spatial scale `t`:
`φ_t(x) = \frac{\Gamma(a+1/2)}{\sqrt\pi\,\Gamma(a)}\,t^{-1}(1 + (x/t)^2)^{-a-1/2}`.

The scaling convention is the one that makes the degrees of freedom `2a` rather than `a`; read
it together with the rate in the inverse-gamma law (`inverseGammaDensity`).-/
noncomputable def studentDensity (a t x : ℝ) : ℝ :=
  Real.Gamma (a + 1 / 2) / (Real.sqrt Real.pi * Real.Gamma a) * t⁻¹
    * (1 + (x / t) ^ 2) ^ (-a - 1 / 2)

/-- The Student-t law with `2a` degrees of freedom at spatial scale `t`.-/
noncomputable def studentLaw (a t : ℝ) : Measure ℝ :=
  volume.withDensity fun x => ENNReal.ofReal (studentDensity a t x)

/-! ## The reflection fold -/

/-- **The reflection fold at a general exponential weight.** For an even nonnegative `G`,
`∫_ℝ e^{pv}G(v)\,dv = 2∫_0^∞ \cosh(pv)G(v)\,dv`.-/
theorem lintegral_exp_mul_of_even {p : ℝ} {G : ℝ → ℝ} (hGm : Measurable G)
    (hGnn : ∀ v, 0 ≤ G v) (hGeven : ∀ v, G (-v) = G v) :
    (∫⁻ v, ENNReal.ofReal (Real.exp (p * v) * G v))
      = 2 * ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (Real.cosh (p * v) * G v) := by
  have hemb : MeasurableEmbedding (fun x : ℝ => -x) :=
    (Homeomorph.neg ℝ).toMeasurableEquiv.measurableEmbedding
  have hmp : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg volume
  have hpre : (fun x : ℝ => -x) ⁻¹' (Ioi (0 : ℝ)) = Iio (0 : ℝ) := by ext x; simp
  set g : ℝ → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.exp (-(p * v)) * G v) with hgdef
  have hgm : Measurable g := by rw [hgdef]; fun_prop
  have hIio : (∫⁻ v in Iio (0 : ℝ), ENNReal.ofReal (Real.exp (p * v) * G v))
      = ∫⁻ v in Ioi (0 : ℝ), g v := by
    have hkey := hmp.setLIntegral_comp_preimage_emb hemb g (Ioi (0 : ℝ))
    rw [hpre] at hkey
    rw [← hkey]
    refine setLIntegral_congr_fun measurableSet_Iio fun v _ => ?_
    rw [hgdef]
    simp only
    rw [hGeven v, show -(p * -v) = p * v by ring]
  have hsplit := lintegral_add_compl (μ := (volume : Measure ℝ))
    (fun v => ENNReal.ofReal (Real.exp (p * v) * G v)) (measurableSet_Iio (a := (0 : ℝ)))
  rw [compl_Iio] at hsplit
  have hIci : (∫⁻ v in Ici (0 : ℝ), ENNReal.ofReal (Real.exp (p * v) * G v))
      = ∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (p * v) * G v) :=
    setLIntegral_congr Ioi_ae_eq_Ici.symm
  rw [hIio, hIci] at hsplit
  rw [← hsplit, ← lintegral_add_left' (hgm.aemeasurable.restrict)]
  have hpt : ∀ v : ℝ, g v + ENNReal.ofReal (Real.exp (p * v) * G v)
      = 2 * ENNReal.ofReal (Real.cosh (p * v) * G v) := by
    intro v
    rw [hgdef]
    simp only
    rw [← ENNReal.ofReal_add (mul_nonneg (Real.exp_pos _).le (hGnn v))
        (mul_nonneg (Real.exp_pos _).le (hGnn v)),
      show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [Real.cosh_eq]
    ring
  simp only [hpt]
  rw [lintegral_const_mul' _ _ (by norm_num)]

/-! ## The Brownian mixture over the inverse-gamma law is the Student-t law -/

/-! ## The Bessel–Laplace integral -/

/-- **The Bessel–Laplace integral, in `ℝ≥0∞` and down to the defining integral of `K_p`.**

`∫_0^∞ u^{p-1}e^{-A/u - Bu}\,du = 2c^pK_p(2s)` for `A, B > 0`, every real `p`, and
`c = \sqrt A/\sqrt B`, `s = \sqrt A\sqrt B` — here with the right-hand side left as the integral
that *defines* `besselK`, and with the constants written in the coordinates that keep fourth
roots out.-/
theorem lintegral_Ioi_rpow_exp_besselKernel {p A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (p - 1) * Real.exp (-(A / u + B * u))))
      = ENNReal.ofReal ((Real.sqrt A / Real.sqrt B) ^ p) * (2 * ∫⁻ v in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.cosh (p * v)
            * Real.exp (-(2 * (Real.sqrt A * Real.sqrt B) * Real.cosh v)))) := by
  have hsA : (0 : ℝ) < Real.sqrt A := Real.sqrt_pos.mpr hA
  have hsB : (0 : ℝ) < Real.sqrt B := Real.sqrt_pos.mpr hB
  set c : ℝ := Real.sqrt A / Real.sqrt B with hcdef
  set s : ℝ := Real.sqrt A * Real.sqrt B with hsdef
  have hc : (0 : ℝ) < c := by rw [hcdef]; positivity
  have hs : (0 : ℝ) < s := by rw [hsdef]; positivity
  have hcp : (0 : ℝ) < c ^ p := Real.rpow_pos_of_pos hc p
  have hAA : A / Real.sqrt A = Real.sqrt A := by
    rw [eq_comm, eq_div_iff hsA.ne']
    exact Real.mul_self_sqrt hA.le
  have hBB : B / Real.sqrt B = Real.sqrt B := by
    rw [eq_comm, eq_div_iff hsB.ne']
    exact Real.mul_self_sqrt hB.le
  have hAc : A / c = s := by
    rw [hcdef, hsdef, div_div_eq_mul_div,
      show A * Real.sqrt B / Real.sqrt A = (A / Real.sqrt A) * Real.sqrt B by ring, hAA]
  have hBc : B * c = s := by
    rw [hcdef, hsdef,
      show B * (Real.sqrt A / Real.sqrt B) = (B / Real.sqrt B) * Real.sqrt A by ring, hBB]
    ring
  have hpt : ∀ v : ℝ, ENNReal.ofReal (c * Real.exp v)
        * ENNReal.ofReal ((c * Real.exp v) ^ (p - 1)
            * Real.exp (-(A / (c * Real.exp v) + B * (c * Real.exp v))))
      = ENNReal.ofReal (Real.exp (p * v)
          * (c ^ p * Real.exp (-(2 * s * Real.cosh v)))) := by
    intro v
    have hev : (0 : ℝ) < Real.exp v := Real.exp_pos v
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Real.mul_rpow hc.le hev.le, exp_rpow]
    have harg : A / (c * Real.exp v) + B * (c * Real.exp v) = 2 * s * Real.cosh v := by
      rw [show A / (c * Real.exp v) = (A / c) * Real.exp (-v) by
            rw [Real.exp_neg]; field_simp,
        show B * (c * Real.exp v) = (B * c) * Real.exp v by ring, hAc, hBc, Real.cosh_eq]
      ring
    rw [harg]
    have hcpow : c * c ^ (p - 1) = c ^ p := by
      nth_rewrite 1 [← Real.rpow_one c]
      rw [← Real.rpow_add hc]
      norm_num
    calc c * Real.exp v * (c ^ (p - 1) * Real.exp (v * (p - 1))
            * Real.exp (-(2 * s * Real.cosh v)))
        = (c * c ^ (p - 1)) * (Real.exp v * Real.exp (v * (p - 1)))
            * Real.exp (-(2 * s * Real.cosh v)) := by ring
      _ = c ^ p * Real.exp (p * v) * Real.exp (-(2 * s * Real.cosh v)) := by
          rw [hcpow, ← Real.exp_add, show v + v * (p - 1) = p * v by ring]
      _ = Real.exp (p * v) * (c ^ p * Real.exp (-(2 * s * Real.cosh v))) := by ring
  rw [lintegral_Ioi_comp_exp hc, funext hpt,
    lintegral_exp_mul_of_even (G := fun v => c ^ p * Real.exp (-(2 * s * Real.cosh v)))
      (by fun_prop) (fun v => by positivity) (fun v => by rw [Real.cosh_neg])]
  have hconst : ∀ v : ℝ, ENNReal.ofReal (Real.cosh (p * v)
        * (c ^ p * Real.exp (-(2 * s * Real.cosh v))))
      = ENNReal.ofReal (c ^ p)
        * ENNReal.ofReal (Real.cosh (p * v) * Real.exp (-(2 * s * Real.cosh v))) := by
    intro v
    rw [← ENNReal.ofReal_mul hcp.le]
    congr 1
    ring
  simp only [hconst]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← mul_assoc,
    mul_comm (2 : ℝ≥0∞) (ENNReal.ofReal (c ^ p)), mul_assoc]

/-- **The cosh-integral is `K_p`**, once it is known to be finite.

`besselK` is a Bochner integral and returns junk when its integrand is not integrable, so the
identification is stated with finiteness as a hypothesis; every consumer gets it by comparison
with a convergent integral.-/
theorem lintegral_cosh_exp_eq_besselK (p : ℝ) {z : ℝ}
    (hfin : (∫⁻ v in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.cosh (p * v) * Real.exp (-(z * Real.cosh v)))) ≠ ⊤) :
    (∫⁻ v in Ioi (0 : ℝ), ENNReal.ofReal (Real.cosh (p * v) * Real.exp (-(z * Real.cosh v))))
      = ENNReal.ofReal (besselK p z) := by
  have hb : besselK p z
      = (∫⁻ v in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.cosh (p * v) * Real.exp (-(z * Real.cosh v)))).toReal := by
    rw [besselK]
    have hcongr : (∫ u in Ioi (0 : ℝ), Real.exp (-(z * Real.cosh u)) * Real.cosh (p * u))
        = ∫ u in Ioi (0 : ℝ), Real.cosh (p * u) * Real.exp (-(z * Real.cosh u)) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      ring
    rw [hcongr]
    refine integral_eq_lintegral_of_nonneg_ae ?_ (by fun_prop)
    exact .of_forall fun u => by positivity
  rw [hb, ENNReal.ofReal_toReal hfin]

/-- `K_{-p} = K_p`: the defining integral is even in the order.-/
theorem besselK_neg (p z : ℝ) : besselK (-p) z = besselK p z := by
  rw [besselK, besselK]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [show -p * u = -(p * u) by ring, Real.cosh_neg]

theorem besselK_nonneg (p z : ℝ) : 0 ≤ besselK p z := by
  rw [besselK]
  refine setIntegral_nonneg measurableSet_Ioi fun u _ => ?_
  positivity

/-! ## The transform -/

end ScaleSpace
