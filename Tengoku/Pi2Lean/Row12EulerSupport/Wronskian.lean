import Tengoku.Pi2Lean.Row12.GaussQuadratic
import Tengoku.Pi2Lean.Row12EulerSupport.Endpoint
import Tengoku.Seed.Analysis.Calculus.MeanValue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12EulerSupport.gaussScaledWronskian_hasDerivAt_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.gaussScaledWronskian_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.gaussScaledWronskian_eq_of_limit` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.gaussScaledWronskian_tendsto_of_endpoints` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.gaussReflected_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.gaussNativeWronskian_eq_scaled` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.gaussScaledWronskian_tendsto` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.gaussScaledWronskian_normalized` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.gaussWronskian_normalized` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12EulerSupport.gaussNativeWronskian` (it only prints; the queue checks the axioms of every declaration). -/

open Filter Set
open scoped Topology

namespace Row12EulerSupport

/-- The Abel-scaled Wronskian of the actual Gauss series and its reflection.-/
noncomputable def gaussScaledWronskian (p : ℝ) : ℝ :=
  p * (1 - p) *
    (Row12.gaussA p * (-deriv Row12.gaussA (1 - p)) -
      Row12.gaussA (1 - p) * deriv Row12.gaussA p)

/--
@isnad1 id=hasderiv.2h1v.s5.b16077b9e393 from=translated src=- shape=a1b846c6 vocab=02b6ed78
-/
theorem gaussScaledWronskian_hasDerivAt_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt gaussScaledWronskian 0 p := by
  have hp : ‖p‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hp0] using hp1
  have hpr : ‖1 - p‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 - p)]
    linarith
  have ha := (Row12.gaussA_analyticAt p hp).differentiableAt.hasDerivAt
  have hda := (Row12.gaussA_analyticAt p hp).deriv.differentiableAt.hasDerivAt
  have hb : HasDerivAt (fun x : ℝ => Row12.gaussA (1 - x))
      (-deriv Row12.gaussA (1 - p)) p := by
    simpa only [Function.comp_def, zero_sub, id_eq, mul_neg_one] using
      ((Row12.gaussA_analyticAt (1 - p) hpr).differentiableAt.hasDerivAt).comp p
        ((hasDerivAt_id p).const_sub 1)
  have hdb : HasDerivAt (fun x : ℝ => -deriv Row12.gaussA (1 - x))
      (deriv (deriv Row12.gaussA) (1 - p)) p := by
    have hd := (((Row12.gaussA_analyticAt (1 - p) hpr).deriv.differentiableAt.hasDerivAt).comp p
      ((hasDerivAt_id p).const_sub 1)).neg
    have he : -(deriv (deriv Row12.gaussA) (1 - p) * (-1)) =
        deriv (deriv Row12.gaussA) (1 - p) := by ring
    convert! hd.congr_deriv he using 1
  have ht : HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * p) p := by
    have hd := (hasDerivAt_id p).mul ((hasDerivAt_id p).const_sub 1)
    have he : 1 * (1 - id p) + id p * (-1) = 1 - 2 * p := by
      simp only [id_eq]
      ring
    convert! hd.congr_deriv he using 1
  have hw : HasDerivAt
      (fun x : ℝ => Row12.gaussA x * (-deriv Row12.gaussA (1 - x)) -
        Row12.gaussA (1 - x) * deriv Row12.gaussA x)
      (Row12.gaussA p * deriv (deriv Row12.gaussA) (1 - p) -
        Row12.gaussA (1 - p) * deriv (deriv Row12.gaussA) p) p := by
    apply ((ha.mul hdb).sub (hb.mul hda)).congr_deriv
    ring
  have hd := ht.mul hw
  have he := Row12.gaussA_equation p hp
  have her := Row12.gaussA_equation (1 - p) hpr
  apply hd.congr_deriv
  linear_combination Row12.gaussA p * her - Row12.gaussA (1 - p) * he

/--
@isnad1 id=eq.4h2v.s5.558092e8a932 from=translated src=- shape=2dd859db vocab=60f9fd9b
-/
theorem gaussScaledWronskian_eq (p r : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) (hr0 : 0 < r) (hr1 : r < 1) :
    gaussScaledWronskian p = gaussScaledWronskian r := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun x hx => (gaussScaledWronskian_hasDerivAt_zero x hx.1 hx.2).differentiableAt.differentiableWithinAt)
    (fun x hx => (gaussScaledWronskian_hasDerivAt_zero x hx.1 hx.2).deriv)
    ⟨hp0, hp1⟩ ⟨hr0, hr1⟩

/-- A calculus helper. Its limit premise is discharged by the actual endpoint proofs.
@isnad1 id=eq.3h2v.s6.9308ea22e8fa from=translated src=- shape=3eb6ac61 vocab=04372217
-/
theorem gaussScaledWronskian_eq_of_limit (p K : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hl : Tendsto gaussScaledWronskian (𝓝[>] (0 : ℝ)) (𝓝 K)) :
    gaussScaledWronskian p = K := by
  have he : gaussScaledWronskian =ᶠ[𝓝[>] (0 : ℝ)]
      (fun _ => gaussScaledWronskian p) := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with x hx0 hx1
    exact gaussScaledWronskian_eq x p hx0 hx1 hp0 hp1
  have hc : Tendsto gaussScaledWronskian (𝓝[>] (0 : ℝ))
      (𝓝 (gaussScaledWronskian p)) := tendsto_const_nhds.congr' he.symm
  exact tendsto_nhds_unique hc hl

/-- A conditional endpoint assembly helper; this is not the final normalized theorem.
@isnad1 id=tendsto.2h1v.s7.ac1c1523be71 from=translated src=- shape=9978d1e7 vocab=ca530e01
-/
theorem gaussScaledWronskian_tendsto_of_endpoints (K : ℝ)
    (hd : Tendsto (fun p : ℝ => -p * deriv Row12.gaussA (1 - p))
      (𝓝[>] (0 : ℝ)) (𝓝 K))
    (hf : Tendsto (fun p : ℝ => p * Row12.gaussA (1 - p))
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto gaussScaledWronskian (𝓝[>] (0 : ℝ)) (𝓝 K) := by
  have hi : Tendsto (fun p : ℝ => p) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id'.2 nhdsWithin_le_nhds
  have h1 : Tendsto (fun p : ℝ => 1 - p) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hi
  have ha : Tendsto (Row12.gaussA : ℝ → ℝ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Row12.gaussA_zero] using
      (Row12.gaussA_analyticAt (0 : ℝ) (by simp)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hda : Tendsto (deriv (Row12.gaussA : ℝ → ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 (5 / 36)) := by
    simpa only [Row12.gaussA_deriv_zero] using
      (Row12.gaussA_analyticAt (0 : ℝ) (by simp)).deriv.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have ht := ((h1.mul ha).mul hd).sub ((h1.mul hda).mul hf)
  have he : (fun p : ℝ =>
      ((1 - p) * Row12.gaussA p) * (-p * deriv Row12.gaussA (1 - p)) -
      ((1 - p) * deriv Row12.gaussA p) * (p * Row12.gaussA (1 - p))) =
      gaussScaledWronskian := by
    funext p
    dsimp only [gaussScaledWronskian]
    ring
  simpa only [he, one_mul, mul_zero, sub_zero] using ht

/-- The remaining native-coordinate chain rule, without a normalization premise.
@isnad1 id=hasderiv.2h1v.s7.eb3ff731b9b9 from=translated src=- shape=ec2afb12 vocab=6065d7e9
-/
theorem gaussReflected_hasDerivAt (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun x : ℝ => Row12.gaussA (1 - Row12.gaussP x))
      (-deriv Row12.gaussA (1 - Row12.gaussP q) / (4 * Real.sqrt (1 - q))) q := by
  have hs0 : 0 < Real.sqrt (1 - q) := Real.sqrt_pos.2 (by linarith)
  have hs2 : Real.sqrt (1 - q) ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  have hs1 : Real.sqrt (1 - q) < 1 := by nlinarith
  have hp0 : 0 < Row12.gaussP q := by dsimp [Row12.gaussP]; linarith
  have hp1 : Row12.gaussP q < 1 := by dsimp [Row12.gaussP]; linarith
  have hpr : ‖1 - Row12.gaussP q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 - Row12.gaussP q)]
    linarith
  have hd := ((Row12.gaussA_analyticAt (1 - Row12.gaussP q) hpr).differentiableAt.hasDerivAt).comp q
    ((Row12.gaussP_hasDerivAt q hq1).const_sub 1)
  apply hd.congr_deriv
  ring

/--
@isnad1 id=eq.2h1v.s6.51bb254e0fc5 from=translated src=- shape=03dbe084 vocab=f0664da5
-/
theorem gaussNativeWronskian_eq_scaled (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    Row12.gaussG q * Row12.nativeTheta
      (fun x => Row12.gaussA (1 - Row12.gaussP x)) q -
      Row12.gaussA (1 - Row12.gaussP q) * Row12.nativeTheta Row12.gaussG q =
    gaussScaledWronskian (Row12.gaussP q) / Real.sqrt (1 - q) := by
  have hs : Real.sqrt (1 - q) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by linarith))
  dsimp only [Row12.nativeTheta]
  rw [(gaussReflected_hasDerivAt q hq0 hq1).deriv,
    Row12.gaussG_deriv q (by linarith) hq1]
  dsimp only [Row12.gaussG, gaussScaledWronskian]
  rw [Row12.gaussP_quadratic q hq1]
  field_simp [hs]

/--
@isnad1 id=tendsto.0h0v.s6.6e693e6f2c77 from=translated src=- shape=e4ca2e4a vocab=b8c35c5a
-/
theorem gaussScaledWronskian_tendsto :
    Tendsto gaussScaledWronskian (𝓝[>] (0 : ℝ)) (𝓝 (-1 / (2 * Real.pi))) :=
  gaussScaledWronskian_tendsto_of_endpoints (-1 / (2 * Real.pi))
    derivativeEndpoint functionEndpoint

/--
@isnad1 id=eq.2h1v.s5.a815e71d9016 from=translated src=- shape=bcace877 vocab=2cb935a0
-/
theorem gaussScaledWronskian_normalized (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    gaussScaledWronskian p = -1 / (2 * Real.pi) :=
  gaussScaledWronskian_eq_of_limit p (-1 / (2 * Real.pi)) hp0 hp1
    gaussScaledWronskian_tendsto

/--
@isnad1 id=eq.2h1v.s7.98ae2024b6e9 from=translated src=- shape=2abe9351 vocab=84725d4b
-/
theorem gaussWronskian_normalized (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    Row12.gaussA p * (-deriv Row12.gaussA (1 - p)) -
      Row12.gaussA (1 - p) * deriv Row12.gaussA p =
    -1 / (2 * Real.pi * p * (1 - p)) := by
  have hp : p * (1 - p) ≠ 0 :=
    mul_ne_zero (ne_of_gt hp0) (ne_of_gt (by linarith : 0 < 1 - p))
  have h := congrArg (fun z : ℝ => z / (p * (1 - p)))
    (gaussScaledWronskian_normalized p hp0 hp1)
  simp only [gaussScaledWronskian, mul_div_cancel_left₀ _ hp] at h
  simpa only [div_div, mul_assoc] using h

/-- The literal native Gauss Wronskian, normalized by the actual differentiated endpoints.
@isnad1 id=eq.2h1v.s7.d89b7f89654e from=translated src=- shape=8047726b vocab=893d643b
-/
theorem gaussNativeWronskian (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    Row12.gaussG q * Row12.nativeTheta
      (fun x => Row12.gaussA (1 - Row12.gaussP x)) q -
      Row12.gaussA (1 - Row12.gaussP q) * Row12.nativeTheta Row12.gaussG q =
    -1 / (2 * Real.pi * Real.sqrt (1 - q)) := by
  have hs0 : 0 < Real.sqrt (1 - q) := Real.sqrt_pos.2 (by linarith)
  have hs2 : Real.sqrt (1 - q) ^ 2 = 1 - q := Real.sq_sqrt (by linarith)
  have hs1 : Real.sqrt (1 - q) < 1 := by nlinarith
  have hp0 : 0 < Row12.gaussP q := by dsimp [Row12.gaussP]; linarith
  have hp1 : Row12.gaussP q < 1 := by dsimp [Row12.gaussP]; linarith
  rw [gaussNativeWronskian_eq_scaled q hq0 hq1,
    gaussScaledWronskian_normalized (Row12.gaussP q) hp0 hp1, div_div]

end Row12EulerSupport

