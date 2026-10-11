import Tengoku.OpenaiMath.OAI.Geometry.ProjectionBodies.ShadowSlices

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

/-- The strict scalar inequality in the slice transport proof of
Brunn--Minkowski. The variables `p,q` are the positive slice-volume roots. -/
lemma transport_scalar {m : ℕ} (hm : 0 < m) {a b p q : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) (hp : 0 < p) (hq : 0 < q) :
    1 ≤ (a*p+b*q)^m*(a/(p^m)+b/(q^m)) ∧
      ((a*p+b*q)^m*(a/(p^m)+b/(q^m))=1 ↔ p=q) := by
  let D := p^a*q^b
  have hD : 0 < D := mul_pos (Real.rpow_pos_of_pos hp _) (Real.rpow_pos_of_pos hq _)
  have hX : D ≤ a*p+b*q := Real.geom_mean_le_arith_mean2_weighted ha.le hb.le hp.le hq.le hab
  have hXi : D < a*p+b*q ↔ p ≠ q :=
    Real.geom_mean_lt_arith_mean2_weighted_iff_of_pos ha hb hp.le hq.le hab
  have hY : (D^m)⁻¹ ≤ a/(p^m)+b/(q^m) := by
    have hh := Real.geom_mean_le_arith_mean2_weighted ha.le hb.le
      (inv_nonneg.mpr (pow_nonneg hp.le m)) (inv_nonneg.mpr (pow_nonneg hq.le m)) hab
    convert hh using 1
    · dsimp [D]
      rw [mul_pow,mul_inv,Real.inv_rpow (pow_nonneg hp.le m),
        Real.inv_rpow (pow_nonneg hq.le m)]
      rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_mul hp.le,
        ← Real.rpow_mul hq.le]
      rw [← Real.rpow_natCast,← Real.rpow_natCast,← Real.rpow_mul hp.le,
        ← Real.rpow_mul hq.le]
      simp only [mul_comm]
    · simp only [div_eq_mul_inv]
  have hYP : 0 < a/(p^m)+b/(q^m) := by positivity
  have hX0 : 0 < a*p+b*q := by positivity
  have hle : 1 ≤ (a*p+b*q)^m*(a/(p^m)+b/(q^m)) := by
    calc
      1 = D^m*(D^m)⁻¹ := (mul_inv_cancel₀ (pow_ne_zero _ hD.ne')).symm
      _ ≤ (a*p+b*q)^m*(a/(p^m)+b/(q^m)) :=
        mul_le_mul (pow_le_pow_left₀ hD.le hX m) hY (inv_nonneg.mpr (pow_nonneg hD.le _))
          (pow_nonneg hX0.le _)
  refine ⟨hle,⟨fun he => ?_,fun he => ?_⟩⟩
  · by_contra hn
    have hlt : D^m < (a*p+b*q)^m := pow_lt_pow_left₀ (hXi.mpr hn) hD.le hm.ne'
    have hh : 1 < (a*p+b*q)^m*(a/(p^m)+b/(q^m)) := calc
      1 = D^m*(D^m)⁻¹ := (mul_inv_cancel₀ (pow_ne_zero _ hD.ne')).symm
      _ ≤ D^m*(a/(p^m)+b/(q^m)) := mul_le_mul_of_nonneg_left hY (pow_nonneg hD.le _)
      _ < _ := mul_lt_mul_of_pos_right hlt hYP
    linarith
  · subst q
    rw [← add_mul,hab,one_mul,← add_div,hab]
    exact mul_one_div_cancel (pow_ne_zero _ hp.ne')

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

end PettyProjection
end

noncomputable section
open Set MeasureTheory Metric Filter Topology Function
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

def horizontalSlice (K : Set (E × ℝ)) (s : ℝ) : Set E := (fun y => (y,s)) ⁻¹' K

omit [NormedSpace ℝ E] in
lemma horizontalSlice_compact {K : Set (E × ℝ)} (hK : IsCompact K) (s : ℝ) :
    IsCompact (horizontalSlice K s) :=
  (IsClosedEmbedding.of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft s)
    (isClosedMap_prodMk_right s)).isCompact_preimage hK

lemma horizontalSlice_convex {K : Set (E × ℝ)} (hK : Convex ℝ K) (s : ℝ) :
    Convex ℝ (horizontalSlice K s) := by
  intro x hx y hy a b ha hb hab
  have h := hK hx hy ha hb hab
  change (a • x+b • y,s) ∈ K
  simpa only [Prod.smul_mk,Prod.mk_add_mk,← add_smul,hab,one_smul] using h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma horizontalSlice_nonempty_iff {K : Set (E × ℝ)} {s : ℝ} :
    (horizontalSlice K s).Nonempty ↔ s ∈ Prod.snd '' K := by
  constructor
  · rintro ⟨x,hx⟩; exact ⟨(x,s),hx,rfl⟩
  · rintro ⟨⟨x,t⟩,hx,rfl⟩; exact ⟨x,hx⟩

lemma horizontalSlice_minkowski_subset (K M : Set (E × ℝ)) (a b s t : ℝ) :
    a • horizontalSlice K s+b • horizontalSlice M t ⊆
      horizontalSlice (a • K+b • M) (a*s+b*t) := by
  rintro _ ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩
  exact ⟨a • (x,s),smul_mem_smul_set hx,b • (y,t),smul_mem_smul_set hy,rfl⟩

lemma horizontalSlice_combo_subset {K : Set (E × ℝ)} (hK : Convex ℝ K)
    {a b : ℝ} (ha : 0≤a) (hb : 0≤b) (hab : a+b=1) (s t : ℝ) :
    a • horizontalSlice K s+b • horizontalSlice K t ⊆
      horizontalSlice K (a*s+b*t) := by
  rintro _ ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩
  exact hK hx hy ha hb hab

omit [NormedSpace ℝ E] in
lemma interior_slice_of_interior {K : Set (E × ℝ)} {x : E} {s : ℝ}
    (hx : (x,s) ∈ interior K) : x ∈ interior (horizontalSlice K s) :=
  preimage_interior_subset_interior_preimage (by fun_prop) hx

/-- A projection point strictly between two attained heights is a height of an
interior point. No smoothness of the convex body is imposed. -/
lemma interior_point_at_height {K : Set (E × ℝ)} (hK : Convex ℝ K)
    (hi : (interior K).Nonempty) {l r s : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) (hs : s ∈ Ioo l r) :
    ∃ x : E, (x,s) ∈ interior K := by
  obtain ⟨⟨x0,s0⟩,h0⟩ := hi
  obtain ⟨⟨xl,sl⟩,hxl,hl⟩ := hl
  obtain ⟨⟨xr,sr⟩,hxr,hr⟩ := hr
  change sl=l at hl
  change sr=r at hr
  subst sl; subst sr
  obtain h | h | h := lt_trichotomy s s0
  · let t := (s0-s)/(s0-l)
    have hd : 0<s0-l := by linarith [hs.1]
    have ht0 : 0≤t := (div_pos (by linarith) hd).le
    have ht1 : t<1 := (div_lt_one hd).mpr (by linarith [hs.1])
    have hc := hK.combo_interior_self_mem_interior h0 hxl (by linarith : 0<1-t) ht0 (by ring : (1-t)+t=1)
    refine ⟨(1-t) • x0+t • xl,?_⟩
    convert hc using 1
    ext
    · rfl
    · dsimp [t]
      field_simp
      ring
  · subst s
    exact ⟨x0,h0⟩
  · let t := (s-s0)/(r-s0)
    have hd : 0<r-s0 := by linarith [hs.2]
    have ht0 : 0≤t := (div_pos (by linarith) hd).le
    have ht1 : t<1 := (div_lt_one hd).mpr (by linarith [hs.2])
    have hc := hK.combo_interior_self_mem_interior h0 hxr (by linarith : 0<1-t) ht0 (by ring : (1-t)+t=1)
    refine ⟨(1-t) • x0+t • xr,?_⟩
    convert hc using 1
    ext
    · rfl
    · dsimp [t]
      field_simp
      ring

lemma horizontalSlice_interior_nonempty {K : Set (E × ℝ)} (hK : Convex ℝ K)
    (hi : (interior K).Nonempty) {l r s : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) (hs : s ∈ Ioo l r) :
    (interior (horizontalSlice K s)).Nonempty := by
  obtain ⟨x,hx⟩ := interior_point_at_height hK hi hl hr hs
  exact ⟨x,interior_slice_of_interior hx⟩

lemma vertical_projection_interval {K : Set (E × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    ∃ l r : ℝ, l<r ∧ Prod.snd '' K=Icc l r := by
  have hn : K.Nonempty := hi.mono interior_subset
  refine ⟨sInf (Prod.snd '' K),sSup (Prod.snd '' K),?_,
    compact_convex_real_interval (hK.image continuous_snd)
      (hc.linear_image (LinearMap.snd ℝ E ℝ)) (hn.image _)⟩
  have hInt : (interior (Prod.snd '' K)).Nonempty :=
    (hi.image Prod.snd).mono (isOpenMap_snd.image_interior_subset K)
  rw [compact_convex_real_interval (hK.image continuous_snd)
    (hc.linear_image (LinearMap.snd ℝ E ℝ)) (hn.image _),interior_Icc] at hInt
  exact nonempty_Ioo.mp hInt

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology Function
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

def sliceDensity (K : Set (E × ℝ)) (s : ℝ) : ℝ := volume.real (horizontalSlice K s)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
lemma sliceDensity_nonneg (K : Set (E × ℝ)) (s : ℝ) : 0 ≤ sliceDensity K s := measureReal_nonneg

omit [FiniteDimensional ℝ E] [BorelSpace E] in
lemma sliceDensity_pos {K : Set (E × ℝ)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hi : (interior K).Nonempty) {l r s : ℝ}
    (hl : l ∈ Prod.snd '' K) (hr : r ∈ Prod.snd '' K) (hs : s ∈ Ioo l r) :
    0 < sliceDensity K s := by
  apply ENNReal.toReal_pos (ne_of_gt ?_) (horizontalSlice_compact hK s).measure_ne_top
  exact lt_of_lt_of_le (isOpen_interior.measure_pos volume
    (horizontalSlice_interior_nonempty hc hi hl hr hs)) (measure_mono interior_subset)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
lemma sliceDensity_zero_of_notMem {K : Set (E × ℝ)} {s : ℝ}
    (hs : s ∉ Prod.snd '' K) : sliceDensity K s=0 := by
  have he : horizontalSlice K s=∅ := not_nonempty_iff_eq_empty.mp
    (fun h => hs (horizontalSlice_nonempty_iff.mp h))
  simp [sliceDensity,he]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Measure.IsAddHaarMeasure (volume : Measure E)] in
lemma sliceDensity_indicator_integral {K : Set (E × ℝ)} (hK : IsCompact K) (s : ℝ) :
    (∫ x : E, K.indicator (fun _ => (1:ℝ)) (x,s))=sliceDensity K s := by
  have he : (fun x : E => K.indicator (fun _ => (1:ℝ)) (x,s)) =
      (horizontalSlice K s).indicator (fun _ => (1:ℝ)) := by
    funext x
    by_cases hx : (x,s) ∈ K
    · rw [Set.indicator_of_mem hx,Set.indicator_of_mem (show x ∈ horizontalSlice K s from hx)]
    · rw [Set.indicator_of_notMem hx,Set.indicator_of_notMem (show x ∉ horizontalSlice K s from hx)]
  rw [he,integral_indicator (horizontalSlice_compact hK s).measurableSet,setIntegral_const]
  simp only [smul_eq_mul,mul_one,sliceDensity]

lemma sliceDensity_integrable {K : Set (E × ℝ)} (hK : IsCompact K) :
    Integrable (sliceDensity K) := by
  have hi : Integrable (K.indicator (fun _ => (1:ℝ))) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
  exact hi.integral_prod_right.congr (Eventually.of_forall fun s => sliceDensity_indicator_integral hK s)

lemma sliceDensity_integral {K : Set (E × ℝ)} (hK : IsCompact K) :
    (∫ s, sliceDensity K s)=volume.real K := by
  have hi : Integrable (K.indicator (fun _ => (1:ℝ))) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (integrableOn_const hK.measure_ne_top).integrable_indicator hK.measurableSet
  have he := integral_prod_symm (K.indicator (fun _ => (1:ℝ))) hi
  simp_rw [sliceDensity_indicator_integral hK] at he
  rw [← he,← Measure.volume_eq_prod,integral_indicator hK.measurableSet,setIntegral_const]
  simp only [smul_eq_mul,mul_one]

lemma sliceDensity_interval_integral {K : Set (E × ℝ)} (hK : IsCompact K) {l r : ℝ}
    (hlr : l≤r) (hp : Prod.snd '' K ⊆ Icc l r) :
    (∫ s in l..r, sliceDensity K s)=volume.real K := by
  rw [intervalIntegral.integral_of_le hlr,← integral_Icc_eq_integral_Ioc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact sliceDensity_integral hK
  · intro s hs
    exact sliceDensity_zero_of_notMem (fun h => hs (hp h))

end
end PettyProjection
end

end OAI
