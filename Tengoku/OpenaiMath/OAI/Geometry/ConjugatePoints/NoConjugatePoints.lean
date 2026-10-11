import Tengoku.OpenaiMath.OAI.Geometry.ConjugatePoints.Passages

namespace OAI

noncomputable section

/-!
# Countable passage assembly and the uniform no-conjugate-points theorem.
-/

section
open Set Filter Topology MeasureTheory Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.ReturningPassage
open Neck Cometric Turning ReturningCoefficients PassageDynamics SupportExtension

lemma normalDensity_zero (P Q A B : TMat) (T : Vec) : normalDensity P Q A B T 0 0 = 0 := by
  simp [normalDensity, gamma, curvatureJet, gammaPrime, metric, pairing]

end ThreeManifold.ReturningPassage
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage

lemma coordinateCometric_end_third (right : Bool) {δ t : ℝ} (ht : t < 1/3) :
    coordinateCometric right δ t = !![1+δ*A t,0;0,1+δ*A 1] := by
  cases right
  · have hc := χ_eq_zero (show t ≤ 5/12 by linarith)
    have hA := A_plateau (show 2/3 ≤ 1-t by linarith) (show (2/3:ℝ) ≤ 1 by norm_num)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coordinateCometric,P,d₁,d₂,shear,hc,hA]
  · have hc := χ_eq_one (show 7/12 ≤ 1-t by linarith)
    have hA := A_plateau (show 2/3 ≤ 1-t by linarith) (show (2/3:ℝ) ≤ 1 by norm_num)
    have he : 1-(1-t) = t := by ring
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinateCometric,PEnd,C₂,P,d₁,d₂,shear,hc,hA,he,
        Matrix.mul_apply,Fin.sum_univ_two,Matrix.transpose_apply] <;> ring

lemma metricInverse_end_warped (right : Bool) {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (ht : t ∈ Ioo (-1/4:ℝ) (1/3)) :
    metricInverse right δ t = WarpedCurvature.Q (Collar.ell δ) (Collar.ell δ 1) t := by
  unfold metricInverse
  rw [coordinateCometric_end_third right ht.2]
  apply Matrix.inv_eq_left_inv
  have h0 := Collar.squared_end_constant ⟨hδ.1.le,hδ.2⟩ ht.1
  have h1 := Collar.squared_end_constant ⟨hδ.1.le,hδ.2⟩ (by norm_num : (-1/4:ℝ) < 1)
  change (Collar.ell δ t)^2 * (1+δ*A t) = 1 at h0
  change (Collar.ell δ 1)^2 * (1+δ*A 1) = 1 at h1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WarpedCurvature.Q,WarpedCurvature.diag,Matrix.mul_apply,Fin.sum_univ_two,h0,h1]

lemma ell_convex_nonnegative {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (ht : 0 ≤ t) :
    0 ≤ deriv (deriv (Collar.ell δ)) t := by
  have he : Collar.k δ =ᶠ[𝓝 t] Collar.rate δ := by
    filter_upwards [Ioi_mem_nhds (show (-1/4:ℝ) < t by linarith)] with u hu
    exact Collar.k_eq_rate hu.le
  have hk : deriv (Collar.k δ) t ≤ 0 := by
    rw [he.deriv_eq,(Collar.rate_hasDerivAt ⟨hδ.1.le,hδ.2⟩ (by linarith : -1 ≤ t)).deriv]
    apply div_nonpos_of_nonpos_of_nonneg
    · apply mul_nonpos_of_nonneg_of_nonpos hδ.1.le
      have hd := Collar.denom_pos ⟨hδ.1.le,hδ.2⟩ (by linarith : -1 ≤ t)
      have ha := mul_nonpos_of_nonpos_of_nonneg (a_deriv_nonpos t) hd.le
      have hq := mul_nonneg hδ.1.le (sq_nonneg (a t))
      linarith
    · positivity
  rw [Collar.ell_second ⟨hδ.1.le,hδ.2⟩]
  exact mul_nonneg (sub_nonneg.mpr (hk.trans (sq_nonneg _))) (Collar.ell_pos δ t).le

lemma framed_neck_shallow_nonpositive (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {x : E3} (hx : x 0 ∈ Icc (0:ℝ) (1/4)) : NonpositiveAt (framedNeck right hδ) x := by
  have he : metricMatrix (framedNeck right hδ) (OpenPartialHomeomorph.refl E3) =ᶠ[𝓝 x]
      fun y => blockMatrix (WarpedCurvature.Q (Collar.ell δ) (Collar.ell δ 1) (y 0)) := by
    filter_upwards [framedNeck_matrix_germ right hδ ⟨hx.1,by linarith [hx.2]⟩,
      ((continuous_apply 0).continuousAt.preimage_mem_nhds
        (isOpen_Ioo.mem_nhds (show x 0 ∈ Ioo (-1/4:ℝ) (1/3) from ⟨by linarith [hx.1],by linarith [hx.2]⟩)))] with y hy ht
    rw [hy,metricInverse_end_warped right hδ ht]
  apply nonpositiveAt_of_chart _ (d := OpenPartialHomeomorph.refl E3) (by simp) (mem_univ x)
  intro u v
  exact WarpedCurvature.warped_nonpositive _ _ (Collar.ell_smooth ⟨hδ.1.le,hδ.2⟩)
    (Collar.ell_pos δ) (Collar.ell_pos δ 1).ne' he (ell_convex_nonnegative hδ hx.1) u v

lemma framed_shallow_index (right : Bool) {δ a b : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ J : ℝ → E3} (hab : a ≤ b)
    (hγ : ∀ s ∈ Icc a b, ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s)
    (ht : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) (1/4)) :
    0 ≤ ∫ s in a..b, indexPairDensity (framedNeck right hδ) γ J J s := by
  apply intervalIntegral.integral_nonneg hab
  intro s hs
  exact indexPairDensity_nonneg_of_nonpositiveAt _ J (hγ s hs) (framed_neck_shallow_nonpositive right hδ (ht s hs))
end ThreeManifold.CompactMetric

namespace ThreeManifold.PassageDynamics
end ThreeManifold.PassageDynamics
namespace ThreeManifold.CompactMetric

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end

section
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage
lemma framed_boundary_hasDerivAt (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ J : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    {s : ℝ} (hs : s ∈ U) (ht : γ s 0 ∈ Icc (0:ℝ) 1) (hJ : DifferentiableAt ℝ J s) :
    HasDerivAt (fun r => boundaryTerm (deriv (metricInverse right δ) (γ r 0))
      (splitVector (deriv γ r)) (splitVector (J r)))
      (boundaryJet (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (deriv (deriv (metricInverse right δ)) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (J s)) (splitVector (deriv J s))) s := by
  have hvel := framed_velocity_equation right hδ hU hγ hs ht
  have hfield := TorusNeck.splitVector_hasDerivAt hJ.hasDerivAt
  have hv : HasDerivAt (fun r => (splitVector (deriv γ r)).1)
      ((1/2:ℝ)*pairing (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)).2 (splitVector (deriv γ s)).2) s := by
    have h := (ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hvel
    change HasDerivAt (fun r => (splitVector (deriv γ r)).1)
      (-gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))).1 s at h
    convert h using 1
    simp only [gamma,Prod.fst_neg]
    ring
  have hu : HasDerivAt (fun r => (splitVector (deriv γ r)).2)
      (-(splitVector (deriv γ s)).1 • (coordinateCometric right δ (γ s 0) *ᵥ
        (deriv (metricInverse right δ) (γ s 0) *ᵥ (splitVector (deriv γ s)).2))) s := by
    have h := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hvel
    change HasDerivAt (fun r => (splitVector (deriv γ r)).2)
      (-gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))).2 s at h
    convert h using 1
    ext i
    simp only [gamma,Prod.snd_neg,Pi.neg_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul]
    ring
  exact boundaryTerm_hasDerivAt (coordinateCometric_transpose right δ _)
    (metricInverse_deriv_transpose right δ _) (metricInverse_second_transpose right δ _)
    (((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ ht)).derivWithin (m := ∞)
      (by simp)).differentiableAt (by simp)).hasDerivAt
    (hasDerivAt_pi.mp (((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds hs)).differentiableAt (by simp)).hasDerivAt 0)
    hv hu ((ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hfield)
      ((ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hfield)

lemma framed_index_energy (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {γ J : ℝ → E3}
    {s : ℝ} (ht : γ s 0 ∈ Icc (0:ℝ) 1) :
    indexPairDensity (framedNeck right hδ) γ J J s =
      coordinateEnergyDensity (metricInverse right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (deriv (deriv (metricInverse right δ)) (γ s 0)) (splitVector (deriv γ s))
        (splitVector (J s)) (splitVector (deriv J s)) -
      boundaryJet (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (deriv (deriv (metricInverse right δ)) (γ s 0)) (splitVector (deriv γ s))
        (splitVector (J s)) (splitVector (deriv J s)) := by
  rw [framedNeck_index_density right hδ ht]
  unfold normalDensity
  rw [index_density_identity (frame_QP right ⟨hδ.1.le,hδ.2⟩ ht)
    (metricInverse_transpose right δ _) (coordinateCometric_transpose right δ _)
    (metricInverse_deriv_transpose right δ _) (metricInverse_second_transpose right δ _)]
  rw [euclidean_velocity,framedNeck_covariant right hδ γ J ht,
    framedNeck_bilin right hδ ⟨by linarith [ht.1],by linarith [ht.2]⟩,
    TorusNeck.split_add,split_join]
  ring

lemma framed_energy_nonneg (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {t : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) {p : TVec}
    (hc : 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) t) p)
    (v : ℝ) (V D : Vec) :
    0 ≤ coordinateEnergyDensity (metricInverse right δ t) (deriv (metricInverse right δ) t)
      (deriv (deriv (metricInverse right δ)) t) (v,coordinateCometric right δ t *ᵥ p) V D := by
  rw [metricInverse_first (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ ht),
    metricInverse_second (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ ht),
    energy_cometric_identity (frame_QP right ⟨hδ.1.le,hδ.2⟩ ht)
      (coordinateCometric_transpose right δ _) (metricInverse_transpose right δ _)
      (symmetric_total_deriv (coordinateCometric_transpose right δ) t)]
  have hp := (coordinateCometric_posDef (fun q => (frame_elliptic right ⟨hδ.1.le,hδ.2⟩ ht q).1)).inv.posSemidef
  have hh := hp.dotProduct_mulVec_nonneg (D.2-V.1 • (deriv (coordinateCometric right δ) t *ᵥ p))
  simp only [star_trivial] at hh
  change 0 ≤ pairing (metricInverse right δ t) _ _ at hh
  have hc' : pairing (deriv (deriv (coordinateCometric right δ)) t) p p ≤ 0 := by
    change 0 ≤ pairing (-deriv (deriv (coordinateCometric right δ)) t) p p at hc
    rw [pairing_matrix_neg] at hc
    linarith
  have hn := mul_nonpos_of_nonpos_of_nonneg hc' (sq_nonneg V.1)
  nlinarith [sq_nonneg D.1]
end

open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck
lemma framed_coordinate_index_integral (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ J : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hJ : ContDiffOn ℝ ∞ J U) {a b : ℝ} (hab : uIcc a b ⊆ U)
    (htr : ∀ s ∈ uIcc a b, γ s 0 ∈ Icc (0:ℝ) 1) :
    (∫ s in a..b, indexPairDensity (framedNeck right hδ) γ J J s) =
    (∫ s in a..b, coordinateEnergyDensity (metricInverse right δ (γ s 0))
      (deriv (metricInverse right δ) (γ s 0)) (deriv (deriv (metricInverse right δ)) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (J s)) (splitVector (deriv J s))) -
    (boundaryTerm (deriv (metricInverse right δ) (γ b 0)) (splitVector (deriv γ b)) (splitVector (J b)) -
      boundaryTerm (deriv (metricInverse right δ) (γ a 0)) (splitVector (deriv γ a)) (splitVector (J a))) := by
  let t := fun s => γ s 0
  let T := fun s => splitVector (deriv γ s)
  let V := fun s => splitVector (J s)
  let D := fun s => splitVector (deriv J s)
  have ht : ∀ s ∈ uIcc a b, ContinuousAt t s :=
    fun s hs => (hasDerivAt_pi.mp (((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hab hs))).differentiableAt (by simp)).hasDerivAt 0).continuousAt
  have hP : ContinuousOn (coordinateCometric right δ ∘ t) (uIcc a b) := by
    intro s hs
    exact ((coordinateCometric_smooth right δ).continuous.continuousAt.comp (ht s hs)).continuousWithinAt
  have hQ : ContinuousOn (metricInverse right δ ∘ t) (uIcc a b) := by
    intro s hs
    have hr := htr s hs
    have hc : ContinuousAt (metricInverse right δ) (t s) := (metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ hr)).continuousAt
    exact (hc.comp (ht s hs)).continuousWithinAt
  have hA : ContinuousOn (deriv (metricInverse right δ) ∘ t) (uIcc a b) := by
    intro s hs
    have hr := htr s hs
    have hc : ContinuousAt (deriv (metricInverse right δ)) (t s) :=
      ((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ hr)).derivWithin (m := ∞) (by simp)).continuousAt
    exact (hc.comp (ht s hs)).continuousWithinAt
  have hB : ContinuousOn (deriv (deriv (metricInverse right δ)) ∘ t) (uIcc a b) := by
    intro s hs
    have hr := htr s hs
    have hc : ContinuousAt (deriv (deriv (metricInverse right δ))) (t s) :=
      (((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ hr)).derivWithin (m := ∞) (by simp)).derivWithin
        (m := ∞) (by simp)).continuousAt
    exact (hc.comp (ht s hs)).continuousWithinAt
  have hT : ContinuousOn T (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp
      (((euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hab hs))).derivWithin (m := ∞) (by simp)).continuousAt).continuousWithinAt
  have hV : ContinuousOn V (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp
      (hJ.contDiffAt (hU.mem_nhds (hab hs))).continuousAt).continuousWithinAt
  have hD : ContinuousOn D (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp
      ((hJ.contDiffAt (hU.mem_nhds (hab hs))).derivWithin (m := ∞) (by simp)).continuousAt).continuousWithinAt
  let E := fun s => coordinateEnergyDensity (metricInverse right δ (t s)) (deriv (metricInverse right δ) (t s))
    (deriv (deriv (metricInverse right δ)) (t s)) (T s) (V s) (D s)
  let B := fun s => boundaryJet (coordinateCometric right δ (t s)) (deriv (metricInverse right δ) (t s))
    (deriv (deriv (metricInverse right δ)) (t s)) (T s) (V s) (D s)
  have he : ContinuousOn E (uIcc a b) := continuousOn_energy hQ hA hB hT hV hD
  have hb : ContinuousOn B (uIcc a b) := continuousOn_boundaryJet hP hA hB hT hV hD
  have hderiv : ∀ s ∈ uIcc a b,
      HasDerivAt (fun r => boundaryTerm (deriv (metricInverse right δ) (t r)) (T r) (V r)) (B s) s := by
    intro s hs
    exact framed_boundary_hasDerivAt right hδ hU hγ (hab hs) (htr s hs)
      ((hJ.contDiffAt (hU.mem_nhds (hab hs))).differentiableAt (by simp))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hb.intervalIntegrable
  calc
    _ = ∫ s in a..b, E s - B s := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact framed_index_energy right hδ (htr s hs)
    _ = (∫ s in a..b, E s) - ∫ s in a..b, B s :=
      intervalIntegral.integral_sub he.intervalIntegrable hb.intervalIntegrable
    _ = _ := by rw [hFTC]

lemma framed_zero_endpoints_index (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (hc : ∀ t ∈ Icc (0:ℝ) 1, ∀ p, 0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) t) p)
    {γ J : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hJ : ContDiffOn ℝ ∞ J U) {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U)
    (htr : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1) (hJa : J a = 0) (hJb : J b = 0) :
    0 ≤ ∫ s in a..b, indexPairDensity (framedNeck right hδ) γ J J s := by
  rw [framed_coordinate_index_integral right hδ hU hγ hJ
    (by simpa only [uIcc_of_le hab] using hsub) (by simpa only [uIcc_of_le hab] using htr)]
  have hb0 (s : ℝ) (hJs : J s = 0) :
      boundaryTerm (deriv (metricInverse right δ) (γ s 0)) (splitVector (deriv γ s)) (splitVector (J s)) = 0 := by
    simp [hJs, splitVector, boundaryTerm, pairing]
  rw [hb0 b hJb,hb0 a hJa,sub_self,sub_zero]
  apply intervalIntegral.integral_nonneg hab
  intro s hs
  let p := metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2
  have hu := framed_velocity_torus right hδ (htr s hs) (show metricInverse right δ (γ s 0) *ᵥ
    (splitVector (deriv γ s)).2 = p from rfl)
  have hT : splitVector (deriv γ s) = ((splitVector (deriv γ s)).1,coordinateCometric right δ (γ s 0) *ᵥ p) := by
    rw [← hu]
  rw [hT]
  exact framed_energy_nonneg right hδ (htr s hs) (hc _ (htr s hs) p) _ _ _

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Neck
open Turning ReturningPassage ReturningCoefficients

lemma zeroHeight_covariant_pair {P Q : TMat} (hQP : Q * P = 1) (hQ : Qᵀ = Q)
    (A : TMat) (v : ℝ) (u z zd : TVec) :
    metric Q ((0,zd) + gamma P A (v,u) (0,z)) (v,u) = pairing Q zd u := by
  rw [metric_add_left,metric_symm hQ (gamma P A (v,u) (0,z)),metric_gamma hQP]
  simp only [metric]
  ring

lemma zeroHeight_normalDensity {P Q A B : TMat} (hQP : Q * P = 1)
    (hQ : Qᵀ = Q) (hP : Pᵀ = P) (hA : Aᵀ = A) (hB : Bᵀ = B)
    (v : ℝ) (u z zd : TVec) :
    normalDensity P Q A B (v,u) (0,z) (0,zd) =
      pairing Q zd zd - (pairing Q zd u)^2 - boundaryJet P A B (v,u) (0,z) (0,zd) := by
  unfold normalDensity
  rw [index_density_identity hQP hQ hP hA hB,zeroHeight_covariant_pair hQP hQ]
  simp only [coordinateEnergyDensity]
  ring

lemma transverse_energy_nonneg {Q : TMat} (hQ : Qᵀ = Q)
    (hpos : ∀ z, 0 ≤ pairing Q z z) {v : ℝ} {u : TVec}
    (hu : metric Q (v,u) (v,u) = 1) (z : TVec) :
    0 ≤ pairing Q z z - (pairing Q z u)^2 := by
  have hc := psd_cauchy hQ hpos z u
  have hp := mul_nonneg (hpos z) (sq_nonneg v)
  change v * v + pairing Q u u = 1 at hu
  nlinarith

lemma zeroHeight_index_nonnegative
    {P Q A B : ℝ → TMat} {t v : ℝ → ℝ} {u z zd : ℝ → TVec} {a b : ℝ}
    (hab : a ≤ b)
    (hP : ContinuousOn (P ∘ t) (uIcc a b)) (hQ : ContinuousOn (Q ∘ t) (uIcc a b))
    (hA : ContinuousOn (A ∘ t) (uIcc a b)) (hB : ContinuousOn (B ∘ t) (uIcc a b))
    (hv : ContinuousOn v (uIcc a b)) (hu : ContinuousOn u (uIcc a b))
    (hz : ContinuousOn z (uIcc a b)) (hzd : ContinuousOn zd (uIcc a b))
    (hQP : ∀ s ∈ uIcc a b, Q (t s) * P (t s) = 1)
    (hQs : ∀ s ∈ uIcc a b, (Q (t s))ᵀ = Q (t s))
    (hPs : ∀ s ∈ uIcc a b, (P (t s))ᵀ = P (t s))
    (hAs : ∀ s ∈ uIcc a b, (A (t s))ᵀ = A (t s))
    (hBs : ∀ s ∈ uIcc a b, (B (t s))ᵀ = B (t s))
    (hpos : ∀ s ∈ uIcc a b, ∀ q, 0 ≤ pairing (Q (t s)) q q)
    (hunit : ∀ s ∈ uIcc a b, metric (Q (t s)) (v s,u s) (v s,u s) = 1)
    (ht : ∀ s ∈ uIcc a b, HasDerivAt t (v s) s)
    (hvd : ∀ s ∈ uIcc a b, HasDerivAt v ((1/2:ℝ)*pairing (A (t s)) (u s) (u s)) s)
    (hud : ∀ s ∈ uIcc a b, HasDerivAt u (-v s • (P (t s) *ᵥ (A (t s) *ᵥ u s))) s)
    (hAd : ∀ s ∈ uIcc a b, HasDerivAt A (B (t s)) (t s))
    (hzd' : ∀ s ∈ uIcc a b, HasDerivAt z (zd s) s)
    (hboundary : boundaryTerm (A (t b)) (v b,u b) (0,z b) ≤
      boundaryTerm (A (t a)) (v a,u a) (0,z a)) :
    0 ≤ ∫ s in a..b, normalDensity (P (t s)) (Q (t s)) (A (t s)) (B (t s))
      (v s,u s) (0,z s) (0,zd s) := by
  let e := fun s => pairing (Q (t s)) (zd s) (zd s) - (pairing (Q (t s)) (zd s) (u s))^2
  let j := fun s => boundaryJet (P (t s)) (A (t s)) (B (t s)) (v s,u s) (0,z s) (0,zd s)
  have he : ContinuousOn e (uIcc a b) :=
    (continuousOn_pairing hQ hzd hzd).sub ((continuousOn_pairing hQ hzd hu).pow 2)
  have hj : ContinuousOn j (uIcc a b) := continuousOn_boundaryJet hP hA hB
    (hv.prodMk hu) (continuousOn_const.prodMk hz) (continuousOn_const.prodMk hzd)
  have hd : ∀ s ∈ uIcc a b, HasDerivAt
      (fun r => boundaryTerm (A (t r)) (v r,u r) (0,z r)) (j s) s := by
    intro s hs
    exact boundaryTerm_hasDerivAt (hPs s hs) (hAs s hs) (hBs s hs)
      (hAd s hs) (ht s hs) (hvd s hs) (hud s hs) (hasDerivAt_const s 0) (hzd' s hs)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hj.intervalIntegrable
  have heq : (∫ s in a..b, normalDensity (P (t s)) (Q (t s)) (A (t s)) (B (t s))
      (v s,u s) (0,z s) (0,zd s)) = (∫ s in a..b, e s) - (∫ s in a..b, j s) := by
    rw [← intervalIntegral.integral_sub he.intervalIntegrable hj.intervalIntegrable]
    apply intervalIntegral.integral_congr
    intro s hs
    exact zeroHeight_normalDensity (hQP s hs) (hQs s hs) (hPs s hs) (hAs s hs) (hBs s hs) _ _ _ _
  rw [heq,hFTC]
  have hen : 0 ≤ ∫ s in a..b, e s := by
    apply intervalIntegral.integral_nonneg hab
    intro s hs
    have hs' : s ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hs
    exact transverse_energy_nonneg (hQs s hs') (hpos s hs') (hunit s hs') _
  linarith
end ThreeManifold.Neck
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric

lemma euclidean_covariant (g : SmoothMetric E3) (γ J : ℝ → E3) (s : ℝ) :
    covariantDerivative g γ J s = deriv J s + connectionTerm g (OpenPartialHomeomorph.refl E3)
      (γ s) (deriv γ s) (J s) := by
  unfold covariantDerivative
  change mfderiv I3 I3 (id : E3 → E3) (γ s)
    (alongDerivative _ (OpenPartialHomeomorph.refl E3) γ
      (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3)) s) = _
  rw [mfderiv_eq_fderiv,fderiv_id,euclidean_fieldCoordinates]
  rfl
lemma euclidean_curvature (g : SmoothMetric E3) (γ J : ℝ → E3) (s : ℝ) :
    curvatureAlong g γ J s = curvatureTerm g (OpenPartialHomeomorph.refl E3) (γ s)
      (J s) (deriv γ s) (deriv γ s) := by
  unfold curvatureAlong
  change mfderiv I3 I3 (id : E3 → E3) (γ s)
    (curvatureTerm _ (OpenPartialHomeomorph.refl E3) (γ s)
      (fieldCoordinates γ J (OpenPartialHomeomorph.refl E3) s) (deriv γ s) (deriv γ s)) = _
  rw [mfderiv_eq_fderiv,fderiv_id,euclidean_fieldCoordinates]
  rfl
lemma euclidean_smoothField {γ J : ℝ → E3} {U : Set ℝ} (hJ : ContDiffOn ℝ ∞ J U) :
    SmoothFieldOn γ J U := by
  intro c hc
  have he := chartedSpaceSelf_atlas.mp hc
  subst c
  rw [euclidean_fieldCoordinates]
  exact hJ.mono inter_subset_left

lemma affine_hasDerivAt {f : ℝ → E3} {a k s : ℝ} (hf : DifferentiableAt ℝ f (a+k*s)) :
    HasDerivAt (fun r => f (a+k*r)) (k • deriv f (a+k*s)) s := by
  convert hf.hasDerivAt.scomp s (((hasDerivAt_id s).const_mul k).const_add a) using 1 <;> first | rfl | simp

lemma affine_deriv {f : ℝ → E3} {a k s : ℝ} (hf : DifferentiableAt ℝ f (a+k*s)) :
    deriv (fun r => f (a+k*r)) s = k • deriv f (a+k*s) := (affine_hasDerivAt hf).deriv

lemma connection_smul_left (g : SmoothMetric E3) (x u v : E3) (k : ℝ) :
    connectionTerm g (OpenPartialHomeomorph.refl E3) x (k • u) v =
      k • connectionTerm g (OpenPartialHomeomorph.refl E3) x u v := by
  simp only [← connectionBilin_apply,map_smul,_root_.smul_apply]
lemma connection_smul_right (g : SmoothMetric E3) (x u v : E3) (k : ℝ) :
    connectionTerm g (OpenPartialHomeomorph.refl E3) x u (k • v) =
      k • connectionTerm g (OpenPartialHomeomorph.refl E3) x u v := by
  simp only [← connectionBilin_apply,map_smul]

lemma euclidean_affine_geodesic (g : SmoothMetric E3) {γ : ℝ → E3} {U : Set ℝ}
    (hU : IsOpen U) (hγ : IsGeodesicOn g γ U) (a k : ℝ) :
    IsGeodesicOn g (fun s => γ (a+k*s)) ((fun s : ℝ => a+k*s) ⁻¹' U) := by
  have hgc := euclidean_curve_smooth hγ.1
  have hf : ContDiff ℝ ∞ (fun s : ℝ => a+k*s) := contDiff_const.add (contDiff_const.mul contDiff_id)
  refine ⟨contMDiffOn_iff_contDiffOn.mpr (hgc.comp hf.contDiffOn (fun _ hs => hs)),?_⟩
  intro c hc s hs _
  have he := chartedSpaceSelf_atlas.mp hc
  subst c
  change deriv (deriv (fun r => γ (a+k*r))) s + connectionTerm g (OpenPartialHomeomorph.refl E3)
    (γ (a+k*s)) (deriv (fun r => γ (a+k*r)) s) (deriv (fun r => γ (a+k*r)) s) = 0
  have hg : ContDiffAt ℝ ∞ γ (a+k*s) := hgc.contDiffAt (hU.mem_nhds hs)
  have hgd : DifferentiableAt ℝ (deriv γ) (a+k*s) :=
    (hg.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)
  have hev : deriv (fun r => γ (a+k*r)) =ᶠ[nhds s] (fun r => k • deriv γ (a+k*r)) := by
    filter_upwards [hf.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hs)] with r hr
    exact affine_deriv ((hgc.contDiffAt (hU.mem_nhds hr)).differentiableAt (by simp))
  have hd : deriv (fun r => k • deriv γ (a+k*r)) s = k • (k • deriv (deriv γ) (a+k*s)) :=
    ((affine_hasDerivAt hgd).const_smul k).deriv
  rw [hev.deriv_eq, hd,
    affine_deriv (hg.differentiableAt (by simp)),connection_smul_left,connection_smul_right]
  have hz := hγ.2 (OpenPartialHomeomorph.refl E3) (chart_mem_atlas E3 (0:E3)) (a+k*s) hs (mem_univ _)
  change deriv (deriv γ) (a+k*s) + connectionTerm g (OpenPartialHomeomorph.refl E3)
    (γ (a+k*s)) (deriv γ (a+k*s)) (deriv γ (a+k*s)) = 0 at hz
  rw [← smul_add,← smul_add,hz,smul_zero,smul_zero]

lemma euclidean_affine_covariant (g : SmoothMetric E3) {γ J : ℝ → E3} {s a k : ℝ}
    (hγ : DifferentiableAt ℝ γ (a+k*s)) (hJ : DifferentiableAt ℝ J (a+k*s)) :
    covariantDerivative g (fun r => γ (a+k*r)) (fun r => J (a+k*r)) s =
      k • covariantDerivative g γ J (a+k*s) := by
  rw [euclidean_covariant,euclidean_covariant,affine_deriv hγ,affine_deriv hJ,connection_smul_left]
  change (k • deriv J (a+k*s) + k • connectionTerm g (OpenPartialHomeomorph.refl E3)
    (γ (a+k*s)) (deriv γ (a+k*s)) (J (a+k*s)) : E3) = k • _
  exact (smul_add k _ _).symm

lemma curvature_smul_velocity (g : SmoothMetric E3) (x J T : E3) (k : ℝ) :
    curvatureTerm g (OpenPartialHomeomorph.refl E3) x J (k • T) (k • T) =
      (k*k) • curvatureTerm g (OpenPartialHomeomorph.refl E3) x J T T := by
  ext l
  simp only [curvatureTerm,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro h _
  ring

lemma euclidean_affine_index (g : SmoothMetric E3) {γ J : ℝ → E3} {s a k : ℝ}
    (hγ : DifferentiableAt ℝ γ (a+k*s)) (hJ : DifferentiableAt ℝ J (a+k*s)) :
    indexPairDensity g (fun r => γ (a+k*r)) (fun r => J (a+k*r)) (fun r => J (a+k*r)) s =
      k^2 * indexPairDensity g γ J J (a+k*s) := by
  unfold indexPairDensity
  rw [euclidean_affine_covariant g hγ hJ,euclidean_curvature,euclidean_curvature,
    affine_deriv hγ,curvature_smul_velocity]
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner (γ (a+k*s))
  let D : E3 := covariantDerivative g γ J (a+k*s)
  change B (k • D) (k • D) -
    B ((k*k) • curvatureTerm g (OpenPartialHomeomorph.refl E3) (γ (a+k*s)) (J (a+k*s))
      (deriv γ (a+k*s)) (deriv γ (a+k*s))) (J (a+k*s)) =
    k^2 * (B D D -
      B (curvatureTerm g (OpenPartialHomeomorph.refl E3) (γ (a+k*s)) (J (a+k*s))
        (deriv γ (a+k*s)) (deriv γ (a+k*s))) (J (a+k*s)))
  simp only [map_smul,_root_.smul_apply,smul_eq_mul]
  ring
end ThreeManifold.RiemannianCoordinates
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage TorusNeck

lemma framed_metric_velocity_equations (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    {s : ℝ} (hs : s ∈ U) (htr : γ s 0 ∈ Icc (0:ℝ) 1) :
    HasDerivAt (fun r => deriv γ r 0)
      ((1/2:ℝ)*pairing (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)).2 (splitVector (deriv γ s)).2) s ∧
    HasDerivAt (fun r => (splitVector (deriv γ r)).2)
      (-deriv γ s 0 • (coordinateCometric right δ (γ s 0) *ᵥ
        (deriv (metricInverse right δ) (γ s 0) *ᵥ (splitVector (deriv γ s)).2))) s := by
  have hvel := framed_velocity_equation right hδ hU hγ hs htr
  constructor
  · have h := (ContinuousLinearMap.fst ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hvel
    change HasDerivAt (fun r => deriv γ r 0)
      (-gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))).1 s at h
    convert h using 1
    simp only [gamma,Prod.fst_neg]
    ring
  · have h := (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s hvel
    change HasDerivAt (fun r => (splitVector (deriv γ r)).2)
      (-gamma (coordinateCometric right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
        (splitVector (deriv γ s)) (splitVector (deriv γ s))).2 s at h
    convert h using 1
    ext i
    simp only [gamma,Prod.snd_neg,Pi.neg_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul,splitVector]
    ring

lemma framed_zeroheight_normal_nonnegative (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ W : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    (hW : ContDiffOn ℝ ∞ W U) (hW0 : ∀ s ∈ U, W s 0 = 0)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U)
    (htr : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1)
    (hunit : ∀ s ∈ Icc a b, (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1)
    (hboundary : boundaryTerm (deriv (metricInverse right δ) (γ b 0))
      (splitVector (deriv γ b)) (splitVector (W b)) ≤
      boundaryTerm (deriv (metricInverse right δ) (γ a 0)) (splitVector (deriv γ a)) (splitVector (W a))) :
    0 ≤ ∫ s in a..b, normalDensity (coordinateCometric right δ (γ s 0))
      (metricInverse right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
      (deriv (deriv (metricInverse right δ)) (γ s 0))
      (splitVector (deriv γ s)) (splitVector (W s)) (splitVector (deriv W s)) := by
  let t := fun s => γ s 0
  let v := fun s => deriv γ s 0
  let u := fun s => (splitVector (deriv γ s)).2
  let z := fun s => (splitVector (W s)).2
  let zd := fun s => (splitVector (deriv W s)).2
  have hsubs : uIcc a b ⊆ U := by rwa [uIcc_of_le hab]
  have htrs : ∀ s ∈ uIcc a b, γ s 0 ∈ Icc (0:ℝ) 1 := by rwa [uIcc_of_le hab]
  have hgc (s : ℝ) (hs : s ∈ uIcc a b) := (euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds (hsubs hs))
  have hwc (s : ℝ) (hs : s ∈ uIcc a b) := hW.contDiffAt (hU.mem_nhds (hsubs hs))
  have ht (s : ℝ) (hs : s ∈ uIcc a b) : HasDerivAt t (v s) s :=
    hasDerivAt_pi.mp ((hgc s hs).differentiableAt (by simp)).hasDerivAt 0
  have hP : ContinuousOn (coordinateCometric right δ ∘ t) (uIcc a b) :=
    fun s hs => ((coordinateCometric_smooth right δ).continuous.continuousAt.comp (ht s hs).continuousAt).continuousWithinAt
  have hQ : ContinuousOn (metricInverse right δ ∘ t) (uIcc a b) := by
    intro s hs
    have hh : ContinuousAt (metricInverse right δ) (t s) := (metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))).continuousAt
    exact (hh.comp (ht s hs).continuousAt).continuousWithinAt
  have hA : ContinuousOn (deriv (metricInverse right δ) ∘ t) (uIcc a b) := by
    intro s hs
    have hh : ContinuousAt (deriv (metricInverse right δ)) (t s) := ((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))).derivWithin (m := ∞) (by simp)).continuousAt
    exact (hh.comp (ht s hs).continuousAt).continuousWithinAt
  have hB : ContinuousOn (deriv (deriv (metricInverse right δ)) ∘ t) (uIcc a b) := by
    intro s hs
    have hh : ContinuousAt (deriv (deriv (metricInverse right δ))) (t s) := (((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))).derivWithin (m := ∞) (by simp)).derivWithin (m := ∞) (by simp)).continuousAt
    exact (hh.comp (ht s hs).continuousAt).continuousWithinAt
  have hTc : ContinuousOn (fun s => splitVector (deriv γ s)) (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp ((hgc s hs).derivWithin (m := ∞) (by simp)).continuousAt).continuousWithinAt
  have hWc : ContinuousOn (fun s => splitVector (W s)) (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp (hwc s hs).continuousAt).continuousWithinAt
  have hDc : ContinuousOn (fun s => splitVector (deriv W s)) (uIcc a b) := by
    intro s hs
    exact (splitVector_smooth.continuous.continuousAt.comp ((hwc s hs).derivWithin (m := ∞) (by simp)).continuousAt).continuousWithinAt
  have hw0 (s : ℝ) (hs : s ∈ uIcc a b) : splitVector (W s) = (0,z s) := by
    change (W s 0,z s) = _
    rw [hW0 s (hsubs hs)]
  have hd0 (s : ℝ) (hs : s ∈ uIcc a b) : splitVector (deriv W s) = (0,zd s) := by
    have hgerm : (fun r => W r 0) =ᶠ[nhds s] (fun _ => (0:ℝ)) := by
      filter_upwards [hU.mem_nhds (hsubs hs)] with r hr
      exact hW0 r hr
    have hh := hasDerivAt_pi.mp ((hwc s hs).differentiableAt (by simp)).hasDerivAt 0
    have hd : deriv W s 0 = 0 := hh.deriv.symm.trans (hgerm.deriv_eq.trans (deriv_const s 0))
    change (deriv W s 0,zd s) = _
    rw [hd]
  have hbnd : boundaryTerm (deriv (metricInverse right δ) (t b)) (v b,u b) (0,z b) ≤
      boundaryTerm (deriv (metricInverse right δ) (t a)) (v a,u a) (0,z a) := by
    rw [hw0 a left_mem_uIcc,hw0 b right_mem_uIcc] at hboundary
    exact hboundary
  have hbound := zeroHeight_index_nonnegative hab hP hQ hA hB hTc.fst hTc.snd hWc.snd hDc.snd
    (fun s hs => frame_QP right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))
    (fun s _ => metricInverse_transpose right δ (t s))
    (fun s _ => coordinateCometric_transpose right δ (t s))
    (fun s _ => metricInverse_deriv_transpose right δ (t s))
    (fun s _ => metricInverse_second_transpose right δ (t s))
    (fun s hs q => ?_) (fun s hs => ?_) ht
    (fun s hs => (framed_metric_velocity_equations right hδ hU hγ (hsubs hs) (htrs s hs)).1)
    (fun s hs => (framed_metric_velocity_equations right hδ hU hγ (hsubs hs) (htrs s hs)).2)
    (fun s hs => (((metricInverse_smoothAt (frame_det_ne right ⟨hδ.1.le,hδ.2⟩ (htrs s hs))).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt)
    (fun s hs => (ContinuousLinearMap.snd ℝ ℝ TVec).hasFDerivAt.comp_hasDerivAt s
      (splitVector_hasDerivAt ((hwc s hs).differentiableAt (by simp)).hasDerivAt)) hbnd
  · convert hbound using 1
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [hw0 s hs,hd0 s hs]
  · have hp := (coordinateCometric_posDef (fun q => (frame_elliptic right ⟨hδ.1.le,hδ.2⟩ (htrs s hs) q).1)).inv.posSemidef
    have hh := hp.dotProduct_mulVec_nonneg q
    simp only [star_trivial] at hh
    change 0 ≤ pairing (metricInverse right δ (γ s 0)) q q at hh
    exact hh
  · have hh := hunit s (by simpa only [uIcc_of_le hab] using hs)
    rw [euclidean_velocity,framedNeck_bilin right hδ ⟨by linarith [(htrs s hs).1],by linarith [(htrs s hs).2]⟩] at hh
    exact hh

lemma framed_gauge_index_nonnegative (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ J : ℝ → E3} {h : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsGeodesicOn (framedNeck right hδ) γ U) (hJ : ContDiffOn ℝ ∞ J U)
    (hh : ContDiffOn ℝ ∞ h U)
    (hzero : ∀ s ∈ U, (J s + h s • deriv γ s) 0 = 0)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U)
    (htr : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1)
    (hunit : ∀ s ∈ Icc a b, (framedNeck right hδ).inner (γ s) (velocity γ s) (velocity γ s) = 1)
    (hboundary : boundaryTerm (deriv (metricInverse right δ) (γ b 0))
      (splitVector (deriv γ b)) (splitVector (J b + h b • deriv γ b)) ≤
      boundaryTerm (deriv (metricInverse right δ) (γ a 0)) (splitVector (deriv γ a))
        (splitVector (J a + h a • deriv γ a))) :
    0 ≤ ∫ s in a..b, indexPairDensity (framedNeck right hδ) γ J J s := by
  let W : ℝ → E3 := fun s => J s + h s • deriv γ s
  have hgc (s : ℝ) (hs : s ∈ U) := (euclidean_curve_smooth hγ.1).contDiffAt (hU.mem_nhds hs)
  have hJc (s : ℝ) (hs : s ∈ U) := hJ.contDiffAt (hU.mem_nhds hs)
  have hhc (s : ℝ) (hs : s ∈ U) := hh.contDiffAt (hU.mem_nhds hs)
  have hWc (s : ℝ) (hs : s ∈ U) : ContDiffAt ℝ ∞ W s :=
    (hJc s hs).add ((hhc s hs).smul ((hgc s hs).derivWithin (m := ∞) (by simp)))
  have hWs : ContDiffOn ℝ ∞ W U := fun s hs => (hWc s hs).contDiffWithinAt
  have hb := framed_zeroheight_normal_nonnegative right hδ hU hγ hWs hzero hab hsub htr hunit hboundary
  let N := fun s => normalDensity (coordinateCometric right δ (γ s 0))
    (metricInverse right δ (γ s 0)) (deriv (metricInverse right δ) (γ s 0))
    (deriv (deriv (metricInverse right δ)) (γ s 0))
    (splitVector (deriv γ s)) (splitVector (W s)) (splitVector (deriv W s))
  let f := indexPairDensity (framedNeck right hδ) γ J J
  let q := fun s => ((framedNeck right hδ).inner (γ s)
    (covariantDerivative (framedNeck right hδ) γ J s) (velocity γ s))^2
  have hfi : IntervalIntegrable f volume a b :=
    ((indexPairDensity_smooth _ hU hγ.1 (euclidean_smoothField hJ) (euclidean_smoothField hJ)).continuousOn.mono hsub).intervalIntegrable_of_Icc hab
  have hqi : IntervalIntegrable q volume a b :=
    (((intrinsic_pairing_smooth _ hU hγ.1 (covariantDerivative_smooth _ hU hγ.1 (euclidean_smoothField hJ))
      (velocity_smooth hU hγ.1)).pow 2).continuousOn.mono hsub).intervalIntegrable_of_Icc hab
  have heq : (∫ s in a..b, N s) = ∫ s in a..b, (f s - q s) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab]
    intro s hs
    have hunit' : metric (metricInverse right δ (γ s 0)) (splitVector (deriv γ s)) (splitVector (deriv γ s)) = 1 := by
      have hm := hunit s hs
      rwa [euclidean_velocity,framedNeck_bilin right hδ ⟨by linarith [(htr s hs).1],by linarith [(htr s hs).2]⟩] at hm
    have hG := normalDensity_deriv_gauge (frame_QP right ⟨hδ.1.le,hδ.2⟩ (htr s hs))
      (metricInverse_transpose right δ _) (coordinateCometric_transpose right δ _)
      (metricInverse_deriv_transpose right δ _) (metricInverse_second_transpose right δ (γ s 0)) hunit'
      (splitVector_hasDerivAt ((hJc s (hsub hs)).differentiableAt (by simp)).hasDerivAt)
      (framed_velocity_equation right hδ hU hγ (hsub hs) (htr s hs))
      ((hhc s (hsub hs)).differentiableAt (by simp)).hasDerivAt
    have hfun : (fun r => splitVector (J r) + h r • splitVector (deriv γ r)) = (fun r => splitVector (W r)) := by
      funext r
      rw [show W r = J r + h r • deriv γ r from rfl,split_add]
      congr 1
      apply Prod.ext
      · rfl
      · ext i
        fin_cases i <;> rfl
    rw [hfun,(splitVector_hasDerivAt ((hWc s (hsub hs)).differentiableAt (by simp)).hasDerivAt).deriv] at hG
    have hWs : splitVector (J s) + h s • splitVector (deriv γ s) = splitVector (W s) := congrFun hfun s
    rw [hWs] at hG
    have hi := framedNeck_index_density right hδ (J := J) (htr s hs)
    change N s = f s - q s
    change N s = _ at hG
    rw [hG]
    exact eq_sub_of_add_eq hi.symm
  rw [heq,intervalIntegral.integral_sub hfi hqi] at hb
  have hq : 0 ≤ ∫ s in a..b, q s := intervalIntegral.integral_nonneg hab (fun s _ => sq_nonneg _)
  linarith
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates

def regularGauge (γ J : ℝ → E3) (s : ℝ) : ℝ := -J s 0 / deriv γ s 0

def gaugeField (γ J : ℝ → E3) (s : ℝ) : E3 := J s + regularGauge γ J s • deriv γ s

lemma regularGauge_zero_germ {γ J : ℝ → E3} {s : ℝ} (hz : J =ᶠ[𝓝 s] 0) :
    regularGauge γ J =ᶠ[𝓝 s] 0 := by
  filter_upwards [hz] with r hr
  simp [regularGauge,hr]
lemma gaugeField_zero_germ {γ J : ℝ → E3} {s : ℝ} (hz : J =ᶠ[𝓝 s] 0) :
    gaugeField γ J =ᶠ[𝓝 s] 0 := by
  filter_upwards [hz,regularGauge_zero_germ (γ := γ) hz] with r hr hg
  simp [gaugeField,hr,hg]

lemma regular_gauge_neighborhood {γ J : ℝ → E3} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContDiffOn ℝ ∞ γ U) (hJ : ContDiffOn ℝ ∞ J U) {a b : ℝ}
    (hsub : Icc a b ⊆ U)
    (hreg : ∀ s ∈ Icc a b, deriv γ s 0 ≠ 0 ∨ J =ᶠ[𝓝 s] 0) :
    ∃ V : Set ℝ, IsOpen V ∧ Icc a b ⊆ V ∧ V ⊆ U ∧
      ContDiffOn ℝ ∞ (regularGauge γ J) V ∧ ∀ s ∈ V, gaugeField γ J s 0 = 0 := by
  let Z := interior {s | J s = 0}
  let D := U ∩ (fun s => deriv γ s 0) ⁻¹' {r : ℝ | r ≠ 0}
  have hv (s : ℝ) (hs : s ∈ U) : ContDiffAt ℝ ∞ (fun r => deriv γ r 0) s :=
    (contDiff_apply ℝ ℝ (0:Fin 3)).contDiffAt.comp s ((hγ.contDiffAt (hU.mem_nhds hs)).derivWithin (m := ∞) (by simp))
  have hD : IsOpen D := by
    apply (show ContinuousOn (fun s => deriv γ s 0) U from fun s hs => (hv s hs).continuousAt.continuousWithinAt).isOpen_inter_preimage hU
    exact isClosed_singleton.isOpen_compl
  let V := D ∪ (U ∩ Z)
  have hVU : V ⊆ U := by intro s hs; exact hs.elim And.left And.left
  have hsV (s : ℝ) (hs : s ∈ V) : deriv γ s 0 ≠ 0 ∨ J =ᶠ[𝓝 s] 0 := by
    rcases hs with hs | hs
    · exact Or.inl hs.2
    · exact Or.inr (mem_interior_iff_mem_nhds.mp hs.2)
  refine ⟨V,hD.union (hU.inter isOpen_interior),?_,hVU,?_,?_⟩
  · intro s hs
    rcases hreg s hs with hv | hz
    · exact Or.inl ⟨hsub hs,hv⟩
    · exact Or.inr ⟨hsub hs,mem_interior_iff_mem_nhds.mpr hz⟩
  · intro s hs
    apply ContDiffAt.contDiffWithinAt
    rcases hsV s hs with hn | hz
    · exact (((contDiff_apply ℝ ℝ (0:Fin 3)).contDiffAt.comp s
        (hJ.contDiffAt (hU.mem_nhds (hVU hs)))).neg.div (hv s (hVU hs)) hn)
    · exact contDiffAt_const.congr_of_eventuallyEq (regularGauge_zero_germ hz)
  · intro s hs
    rcases hsV s hs with hn | hz
    · dsimp [gaugeField,regularGauge]
      rw [div_mul_cancel₀ _ hn]
      ring
    · simpa using congrFun (gaugeField_zero_germ (γ := γ) hz).eq_of_nhds 0
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

lemma increasing_boundary_derivative {t v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (_hv : ContinuousOn v (Icc a b)) (hm : AntitoneOn v (Icc a b))
    (hp : t a < t b) : 0 < v a := by
  obtain ⟨c,hc,he⟩ := exists_hasDerivAt_eq_slope t v hab
    (fun s hs => (ht s hs).continuousAt.continuousWithinAt)
    (fun s hs => ht s (Ioo_subset_Icc_self hs))
  have hpv : 0 < v c := by rw [he]; exact div_pos (sub_pos.mpr hp) (sub_pos.mpr hab)
  exact hpv.trans_le (hm (left_mem_Icc.mpr hab.le) (Ioo_subset_Icc_self hc) hc.1.le)

lemma scalar_enter_transverse {t v F : ℝ → ℝ} {a b r : ℝ} (hab : a < b)
    (hr : 0 < r) (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-F (t s)/2) s)
    (ha : t a = 0) (hpos : ∀ s ∈ Ioo a b, 0 < t s)
    (hF : ∀ x < r, 0 ≤ F x) : 0 < v a := by
  have haI : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hn : {s | t s < r} ∈ 𝓝 a := (ht a haI).continuousAt (Iio_mem_nhds (by simpa [ha] using hr))
  obtain ⟨l,c,⟨hl,hac⟩,hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  obtain ⟨d,had,hdb⟩ := exists_between (lt_min hab hac)
  have hdb' : d < b := hdb.trans_le (min_le_left _ _)
  have hdc : d < c := hdb.trans_le (min_le_right _ _)
  have hsubab : Icc a d ⊆ Icc a b := Icc_subset_Icc le_rfl hdb'.le
  have hm : AntitoneOn v (Icc a d) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a d)
    · exact fun s hs => (hv s (hsubab hs)).continuousAt.continuousWithinAt
    · exact fun s hs => (hv s (hsubab (interior_subset hs))).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [(hv s (hsubab (interior_subset hs))).deriv]
      have hh := hF (t s) (hsub ⟨hl.trans_le (interior_subset hs).1,(interior_subset hs).2.trans_lt hdc⟩)
      linarith
  exact increasing_boundary_derivative had (fun s hs => ht s (hsubab hs))
    (fun s hs => (hv s (hsubab hs)).continuousAt.continuousWithinAt) hm
    (by rw [ha]; exact hpos d ⟨had,hdb'⟩)

lemma force_end_nonnegative (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ) (p : TVec)
    {x : ℝ} (hx : x < 1/4) : 0 ≤ force right δ p x := by
  unfold force
  rw [coordinateCometric_end_deriv hx]
  have ha : 0 ≤ a x := a_nonneg x
  simp only [pairing,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,mul_zero,zero_mul,add_zero]
  nlinarith [mul_nonneg (mul_nonneg hδ ha) (sq_nonneg (p 0))]

lemma neck_enter_transverse (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ) {p : TVec}
    {t v : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (ht : ∀ s ∈ Icc a b, HasDerivAt t (v s) s)
    (hv : ∀ s ∈ Icc a b, HasDerivAt v (-force right δ p (t s)/2) s)
    (ha : t a = 0) (hpos : ∀ s ∈ Ioo a b, 0 < t s) : 0 < v a :=
  scalar_enter_transverse hab (by norm_num : (0:ℝ) < 1/4) ht hv ha hpos
    (fun _ hx => force_end_nonnegative right hδ p hx)
end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Matrix
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.Cometric
open Neck ReturningPassage

def flipFrame (right : Bool) (δ : ℝ) : TMat := if right then C₂ δ else T₂ δ

lemma coordinateCometric_flip (right : Bool) (δ t : ℝ) :
    coordinateCometric right δ t = flipFrame right δ * coordinateCometric (!right) δ (1-t) * (flipFrame right δ)ᵀ := by
  cases right with
  | true => simp [coordinateCometric,flipFrame,PEnd]
  | false =>
    simp only [coordinateCometric,flipFrame,Bool.false_eq_true,↓reduceIte,Bool.not_false]
    unfold PEnd
    rw [show 1-(1-t) = t by ring]
    simp only [← Matrix.mul_assoc,(frame_inverse δ).2,Matrix.one_mul]
    rw [Matrix.mul_assoc,← Matrix.transpose_mul,(frame_inverse δ).2,Matrix.transpose_one,Matrix.mul_one]

lemma coordinateCometric_flip_deriv (right : Bool) (δ t : ℝ) :
    deriv (coordinateCometric right δ) t = -(flipFrame right δ *
      deriv (coordinateCometric (!right) δ) (1-t) * (flipFrame right δ)ᵀ) := by
  have hd := ((coordinateCometric_smooth (!right) δ).differentiable (by simp) (1-t)).hasDerivAt.scomp t
    ((hasDerivAt_id t).const_sub 1)
  have he := (congruenceCLM (flipFrame right δ)).hasFDerivAt.comp_hasDerivAt t hd
  have hf : (fun r => (congruenceCLM (flipFrame right δ)) (coordinateCometric (!right) δ (1-r))) =
      coordinateCometric right δ := by
    funext r
    exact (coordinateCometric_flip right δ r).symm
  dsimp only [Function.comp_def] at he
  rw [hf] at he
  have he' := he.deriv
  change deriv (coordinateCometric right δ) t = flipFrame right δ * ((-1:ℝ) • deriv (coordinateCometric (!right) δ) (1-t)) * (flipFrame right δ)ᵀ at he'
  simpa only [zero_sub,neg_smul,one_smul,Matrix.mul_neg,Matrix.neg_mul] using he'

lemma force_far_end_nonpositive (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ) (p : TVec)
    {x : ℝ} (hx : 3/4 < x) : force right δ p x ≤ 0 := by
  unfold force
  rw [coordinateCometric_flip_deriv,pairing_matrix_neg]
  change -qform (flipFrame right δ * deriv (coordinateCometric (!right) δ) (1-x) * (flipFrame right δ)ᵀ) p ≤ 0
  rw [qform_congruence]
  have hh := PassageDynamics.force_end_nonnegative (!right) hδ ((flipFrame right δ)ᵀ *ᵥ p) (by linarith : 1-x < 1/4)
  unfold force at hh
  exact neg_nonpos.mpr hh

lemma inverse_jet_zero_nonpositive (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : (coordinateCometric right δ 0).det ≠ 0) (z : TVec) :
    pairing (deriv (metricInverse right δ) 0) z z ≤ 0 := by
  rw [metricInverse_endpoint_deriv hd]
  have ha := a_nonneg (0:ℝ)
  simp only [pairing,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,mul_zero,zero_mul,add_zero]
  nlinarith [mul_nonneg (mul_nonneg hδ ha) (sq_nonneg (z 0))]

lemma inverse_jet_one_nonnegative (right : Bool) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : (coordinateCometric right δ 1).det ≠ 0) (z : TVec) :
    0 ≤ pairing (deriv (metricInverse right δ) 1) z z := by
  rw [metricInverse_first hd]
  simp only [Matrix.neg_mul,pairing_matrix_neg]
  have he := qform_congruence (metricInverse right δ 1) (deriv (coordinateCometric right δ) 1) z
  rw [metricInverse_transpose] at he
  change 0 ≤ -qform (metricInverse right δ 1 * deriv (coordinateCometric right δ) 1 * metricInverse right δ 1) z
  rw [he]
  exact neg_nonneg.mpr (force_far_end_nonpositive right hδ (metricInverse right δ 1 *ᵥ z) (x := 1) (by norm_num))

lemma zeroheight_boundary_nonnegative (right : Bool) {δ t v : ℝ} {u z : TVec}
    (hδ : 0 ≤ δ) (hd : (coordinateCometric right δ t).det ≠ 0)
    (ht : (t = 0 ∧ 0 ≤ v) ∨ (t = 1 ∧ v ≤ 0)) :
    0 ≤ boundaryTerm (deriv (metricInverse right δ) t) (v,u) (0,z) := by
  simp only [boundaryTerm,zero_mul,add_zero]
  rw [show -(1/2:ℝ)*v*pairing (deriv (metricInverse right δ) t) z z = -(v/2*pairing (deriv (metricInverse right δ) t) z z) by ring]
  rcases ht with ⟨rfl,hv⟩ | ⟨rfl,hv⟩
  · exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) (inverse_jet_zero_nonpositive right hδ hd z))
  · exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (inverse_jet_one_nonnegative right hδ hd z))

lemma zeroheight_boundary_nonpositive (right : Bool) {δ t v : ℝ} {u z : TVec}
    (hδ : 0 ≤ δ) (hd : (coordinateCometric right δ t).det ≠ 0)
    (ht : (t = 0 ∧ v ≤ 0) ∨ (t = 1 ∧ 0 ≤ v)) :
    boundaryTerm (deriv (metricInverse right δ) t) (v,u) (0,z) ≤ 0 := by
  simp only [boundaryTerm,zero_mul,add_zero]
  rw [show -(1/2:ℝ)*v*pairing (deriv (metricInverse right δ) t) z z = -(v/2*pairing (deriv (metricInverse right δ) t) z z) by ring]
  rcases ht with ⟨rfl,hv⟩ | ⟨rfl,hv⟩
  · exact neg_nonpos.mpr (mul_nonneg_of_nonpos_of_nonpos (by linarith) (inverse_jet_zero_nonpositive right hδ hd z))
  · exact neg_nonpos.mpr (mul_nonneg (by positivity) (inverse_jet_one_nonnegative right hδ hd z))
end ThreeManifold.Cometric
end

section
open Set Filter Topology
namespace ThreeManifold.PassageDynamics
open Cometric Neck ReturningPassage

end ThreeManifold.PassageDynamics
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage PassageDynamics

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates

def toRight (δ : ℝ) (x : E3) : E3 := (fromRightLinear δ).symm (x - ![1,0,0])
lemma fromRight_toRight (δ : ℝ) (x : E3) : fromRight δ (toRight δ x) = x := by
  change fromRightLinear δ ((fromRightLinear δ).symm (x - ![1,0,0])) + ![1,0,0] = x
  rw [ContinuousLinearEquiv.apply_symm_apply,sub_add_cancel]
lemma toRight_height (δ : ℝ) (x : E3) : toRight δ x 0 = 1-x 0 := by
  change -(x 0-1) = 1-x 0
  ring
lemma toRight_smooth (δ : ℝ) : ContDiff ℝ ∞ (toRight δ) :=
  (fromRightLinear δ).symm.contDiff.comp (contDiff_id.sub contDiff_const)

theorem right_frame_lift {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) {U : Set ℝ}
    (hU : IsOpen U) {γ J : ℝ → E3}
    (hγ : IsGeodesicOn (normalizedNeck hδ) γ U) (hJ : SmoothFieldOn γ J U) :
    ∃ η V : ℝ → E3, IsGeodesicOn (framedNeck true hδ) η U ∧ SmoothFieldOn η V U ∧
      (∀ s, η s 0 = 1-γ s 0) ∧
      (∀ s ∈ U, indexPairDensity (framedNeck true hδ) η V V s =
        indexPairDensity (normalizedNeck hδ) γ J J s) ∧
      (∀ s, J s = 0 → V s = 0) ∧
      (∀ s ∈ U, (framedNeck true hδ).inner (η s) (velocity η s) (velocity η s) =
        (normalizedNeck hδ).inner (γ s) (velocity γ s) (velocity γ s)) := by
  let R := fromRightIsometry hδ
  let η := toRight δ ∘ γ
  have he : fromRight δ ∘ η = γ := by funext s; exact fromRight_toRight δ (γ s)
  have hη : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ η U :=
    contMDiffOn_iff_contDiffOn.mpr ((toRight_smooth δ).comp_contDiffOn (euclidean_curve_smooth hγ.1))
  have hηR : MapsTo η U R.domain := fun _ _ => mem_univ _
  have hg : IsGeodesicOn (normalizedRight hδ) η U :=
    R.geodesic_reflect hU hη hηR (by simpa only [he] using hγ)
  have hf : SmoothFieldOn (fromRight δ ∘ η) J U :=
    smoothField_curve_congrOn hU hγ.1 (fun s _ => (congrFun he s).symm) (fun _ _ => rfl) hJ
  let V := R.unmapField η J
  have hV := R.unmapField_smooth hU hη hηR hf
  refine ⟨η,V,hg,hV,fun s => toRight_height δ (γ s),?_,?_,?_⟩
  · intro s hs
    have hm : R.mapField η V = J := by funext r; exact R.map_unmap J (mem_univ _)
    have h := R.indexPairDensity_map hU hη hηR hV hV hs
    rw [he,hm] at h
    exact h.symm
  · intro s hs
    exact (congrArg (mfderiv I3 I3 (fromRight δ) (η s)).inverse hs).trans
      ((mfderiv I3 I3 (fromRight δ) (η s)).inverse.map_zero)
  · intro s hs
    have hv := R.velocity_map (hη.contMDiffAt (hU.mem_nhds hs)) (hηR hs)
    rw [he] at hv
    change (normalizedRight hδ).inner (η s) (velocity η s) (velocity η s) = _
    rw [hv,← congrFun he s]
    exact (R.metric (η s) (hηR hs) (velocity η s) (velocity η s)).symm
end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff Matrix.Norms.Elementwise
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

def PassageBounds (C δ : ℝ) : Prop :=
  ∀ right : Bool, ∀ u ∈ Icc (0:ℝ) 1, ∀ q : TVec,
    (sqnorm q/9 ≤ qform (coordinateCometric right δ u) q ∧ qform (coordinateCometric right δ u) q ≤ 18*sqnorm q) ∧
    sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C ^ 2 * δ ^ 2 * sqnorm q ∧
    0 ≤ qform (-deriv (deriv (coordinateCometric right δ)) u) q ∧
    sqnorm (deriv (coordinateCometric right δ) u *ᵥ q) ≤ C * δ * qform (-deriv (deriv (coordinateCometric right δ)) u) q

lemma const_on_closed_of_deriv_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ → V} {a b : ℝ} (hab : a ≤ b) (hf : ∀ s ∈ Icc a b, HasDerivAt f 0 s) :
    ∀ s ∈ Icc a b, f s = f a := by
  intro s hs
  have hn := (convex_Icc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => (hf r hr).hasDerivWithinAt) (C := 0) (by simp) (left_mem_Icc.mpr hab) hs
  simpa only [zero_mul,norm_le_zero_iff,sub_eq_zero] using hn

lemma framed_closed_momentum (right : Bool) {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {γ : ℝ → E3} {U : Set ℝ} (hU : IsOpen U) (hγ : IsGeodesicOn (framedNeck right hδ) γ U)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ U)
    (ht : ∀ s ∈ Icc a b, γ s 0 ∈ Icc (0:ℝ) 1) :
    ∃ p : TVec, ∀ s ∈ Icc a b, metricInverse right δ (γ s 0) *ᵥ (splitVector (deriv γ s)).2 = p :=
  ⟨_,const_on_closed_of_deriv_zero hab
    (fun s hs => framed_momentum_hasDerivAt right hδ hU hγ (hsub hs) (ht s hs))⟩

end ThreeManifold.CompactMetric
end

section
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
lemma euclidean_affine_smoothField {γ J : ℝ → E3} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hJ : SmoothFieldOn γ J U) (a k : ℝ) :
    SmoothFieldOn (fun s => γ (a+k*s)) (fun s => J (a+k*s)) ((fun s : ℝ => a+k*s) ⁻¹' U) :=
  euclidean_smoothField ((euclidean_field_smooth hU hγ hJ).comp
    (contDiff_const.add (contDiff_const.mul contDiff_id)).contDiffOn (fun _ hs => hs))
lemma affine_zero_germ {J : ℝ → E3} {a k s : ℝ} (hz : J =ᶠ[𝓝 (a+k*s)] 0) :
    (fun r => J (a+k*r)) =ᶠ[𝓝 s] 0 :=
  hz.comp_tendsto ((continuous_const.add (continuous_const.mul continuous_id)).tendsto s)
lemma euclidean_affine_speed (g : SmoothMetric E3) {γ : ℝ → E3} {a k s : ℝ}
    (hγ : DifferentiableAt ℝ γ (a+k*s)) :
    g.inner (γ (a+k*s)) (velocity (fun r => γ (a+k*r)) s) (velocity (fun r => γ (a+k*r)) s) =
      k^2 * g.inner (γ (a+k*s)) (velocity γ (a+k*s)) (velocity γ (a+k*s)) := by
  rw [euclidean_velocity,euclidean_velocity,affine_deriv hγ]
  let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner (γ (a+k*s))
  change B (k • deriv γ (a+k*s)) (k • deriv γ (a+k*s)) = k^2 * B (deriv γ (a+k*s)) (deriv γ (a+k*s))
  simp only [map_smul,_root_.smul_apply,smul_eq_mul]
  ring
lemma euclidean_affine_index_integral (g : SmoothMetric E3) {γ J : ℝ → E3}
    {U : Set ℝ} (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hJ : SmoothFieldOn γ J U) {a k u v : ℝ} (hk : k ≠ 0)
    (hd : ∀ s ∈ uIcc u v, a+k*s ∈ U) :
    (∫ s in u..v, indexPairDensity g (fun r => γ (a+k*r))
      (fun r => J (a+k*r)) (fun r => J (a+k*r)) s) =
      k * ∫ s in (a+k*u)..(a+k*v), indexPairDensity g γ J J s := by
  calc
    _ = ∫ s in u..v, k^2 * indexPairDensity g γ J J (a+k*s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact euclidean_affine_index g
        (((euclidean_curve_smooth hγ).contDiffAt (hU.mem_nhds (hd s hs))).differentiableAt (by simp))
        (((euclidean_field_smooth hU hγ hJ).contDiffAt (hU.mem_nhds (hd s hs))).differentiableAt (by simp))
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_add_mul _ hk a]
      simp only [smul_eq_mul]
      field_simp
end ThreeManifold.RiemannianCoordinates

namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric

namespace ThreeManifold.RiemannianCoordinates
open CompactMetric
lemma euclidean_index_nonnegative_zero_velocity (g : SmoothMetric E3) (γ J : ℝ → E3) (s : ℝ)
    (hv : velocity γ s = 0) : 0 ≤ indexPairDensity g γ J J s := by
  rw [euclidean_velocity] at hv
  have hc : curvatureAlong g γ J s = 0 := by
    rw [euclidean_curvature,hv]
    change curvatureTerm g (OpenPartialHomeomorph.refl E3) (γ s) (J s) 0 0 = (0:E3)
    ext i
    simp [curvatureTerm]
  unfold indexPairDensity
  rw [hc]
  have hz : g.inner (γ s) (0 : TangentSpace I3 (γ s)) (J s) = 0 := by
    let B : E3 →L[ℝ] E3 →L[ℝ] ℝ := g.inner (γ s)
    exact congrArg (fun L : E3 →L[ℝ] ℝ => L (J s)) (map_zero B)
  rw [hz,sub_zero]
  exact inner_self_nonneg g _ _
end ThreeManifold.RiemannianCoordinates
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

end ThreeManifold.CompactMetric
end

open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory
open scoped ContDiff
namespace ThreeManifold.CompactMetric
open RiemannianCoordinates Cometric Neck LocalNeck ReturningPassage Turning ReturningCoefficients

lemma compact_interval_window {K U : Set ℝ} (hK : IsCompact K) (hKn : K.Nonempty)
    (hU : IsOpen U) (hUc : OrdConnected U) (hKU : K ⊆ U) :
    ∃ A B : ℝ, A < B ∧ K ⊆ Ioo A B ∧ Icc A B ⊆ U := by
  obtain ⟨a,ha⟩ := hK.exists_isLeast hKn
  obtain ⟨b,hb⟩ := hK.exists_isGreatest hKn
  obtain ⟨A,B,hAa,hbB,hAB⟩ := IndexForm.interval_enlargement hU hUc (hKU ha.1) (hKU hb.1)
  exact ⟨A,B,hAa.trans_le ((ha.2 hb.1).trans hbB.le),fun s hs => ⟨hAa.trans_le (ha.2 hs),(hb.2 hs).trans_lt hbB⟩,hAB⟩

end ThreeManifold.CompactMetric

end

end OAI
