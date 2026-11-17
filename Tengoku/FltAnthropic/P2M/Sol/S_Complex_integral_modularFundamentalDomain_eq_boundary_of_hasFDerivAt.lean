import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Complex_integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Complex_integral_modularFundamentalDomain_eq_boundary_of_hasFDerivAt

open MeasureTheory Set Filter Topology

noncomputable section

namespace Complex
export _root_.Complex (re sqrt sin_pi_div_two real_smul hasDerivAt_cos im ofRealCLM mk_eq_add_mul_I sin measurableEquivRealProd_symm_apply norm_def sin_pi_sub volume_preserving_equiv_real_prod norm_I cos_pi_sub exp sin_sq cos_sq' exp_ofReal_mul_I_im integral_boundary_rect_of_hasFDerivAt_real_off_countable measurableEquivRealProd exp_ofReal_mul_I_re normSq_mk hasDerivAt_sin continuous_ofReal ext I continuous_sin I_mul_I cos continuous_cos)
namespace GreenFD
open _root_.Complex

def D : Set ℂ := {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im}

def h (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)

def T : Set (ℝ × ℝ) := {p | |p.1| ≤ 1 / 2 ∧ h p.1 ≤ p.2}

/--
@isnad1 id=le.1h1v.s6.62640b4d6674 from=translated src=- shape=34d473cc vocab=6ca68f6c
-/
lemma three_quarters_le {x : ℝ} (hx : |x| ≤ 1 / 2) : 3 / 4 ≤ 1 - x ^ 2 := by
  have h1 : x ^ 2 ≤ (1 / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  linarith

/--
@isnad1 id=eq.0h0v.s6.cbdc91105e05 from=translated src=- shape=1f61e7f3 vocab=71b5db76
-/
lemma sqrt3_sq : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num

/--
@isnad1 id=lt.0h0v.s5.5a3784fa0485 from=translated src=- shape=41e5e22b vocab=01c0b07d
-/
lemma sqrt3_pos : 0 < Real.sqrt 3 / 2 := by positivity

/--
@isnad1 id=lt.0h0v.s5.0ba9d777495f from=translated src=- shape=54ba2212 vocab=01c0b07d
-/
lemma sqrt3_lt_one : Real.sqrt 3 / 2 < 1 := by
  rw [div_lt_one two_pos, Real.sqrt_lt' two_pos]; norm_num

/--
@isnad1 id=le.1h1v.s6.c73d819cceb9 from=translated src=- shape=7bb074c7 vocab=4d8118eb
-/
lemma sqrt3_le_h {x : ℝ} (hx : |x| ≤ 1 / 2) : Real.sqrt 3 / 2 ≤ h x := by
  unfold h
  rw [Real.le_sqrt' sqrt3_pos, sqrt3_sq]
  exact three_quarters_le hx

/--
@isnad1 id=lt.1h1v.s5.321cee908922 from=translated src=- shape=c77dc571 vocab=4b337329
-/
lemma h_pos {x : ℝ} (hx : |x| ≤ 1 / 2) : 0 < h x := lt_of_lt_of_le sqrt3_pos (sqrt3_le_h hx)

/--
@isnad1 id=le.0h1v.s3.a70479908a74 from=translated src=- shape=b14ee516 vocab=29c5866f
-/
lemma h_le_one (x : ℝ) : h x ≤ 1 := by
  unfold h
  rw [Real.sqrt_le_left zero_le_one]
  nlinarith [sq_nonneg x]

/--
@isnad1 id=iff.0h2v.s5.f2f26f6fc52b from=translated src=- shape=0d358ca4 vocab=6a4d3698
-/
lemma mem_D_iff {x y : ℝ} : (⟨x, y⟩ : ℂ) ∈ D ↔ |x| ≤ 1 / 2 ∧ h x ≤ y := by
  simp only [D, mem_ofPred_eq, Complex.norm_def, Complex.normSq_mk, Real.one_le_sqrt]
  constructor
  · rintro ⟨hx, hn, hy⟩
    refine ⟨hx, ?_⟩
    unfold h
    rw [Real.sqrt_le_iff]
    exact ⟨hy.le, by nlinarith⟩
  · rintro ⟨hx, hy⟩
    have hpos := h_pos hx
    have hy' := hy
    unfold h at hy'
    rw [Real.sqrt_le_iff] at hy'
    exact ⟨hx, by nlinarith [hy'.2], lt_of_lt_of_le hpos hy⟩

/--
@isnad1 id=mem.2h2v.s5.ab1dfe5e41e3 from=translated src=- shape=c775cf19 vocab=6a4d3698
-/
lemma mk_mem_D {x y : ℝ} (hx : |x| ≤ 1 / 2) (hy : h x ≤ y) : (⟨x, y⟩ : ℂ) ∈ D :=
  mem_D_iff.mpr ⟨hx, hy⟩

/--
@isnad1 id=eq.0h0v.s6.e998dafe9620 from=translated src=- shape=fab12cd3 vocab=1706fecb
-/
lemma preimage_D : (measurableEquivRealProd.symm : ℝ × ℝ → ℂ) ⁻¹' D = T := by
  ext ⟨x, y⟩
  simp only [mem_preimage, measurableEquivRealProd_symm_apply, T, mem_ofPred_eq]
  exact mem_D_iff

/--
@isnad1 id=isclosed.0h0v.s4.bd7eb3812eaa from=translated src=- shape=0b0a4f6e vocab=7dcf2f0a
-/
lemma isClosed_T : IsClosed T := by
  have h1 : IsClosed {p : ℝ × ℝ | |p.1| ≤ 1 / 2} :=
    isClosed_le (continuous_abs.comp continuous_fst) continuous_const
  have h2 : IsClosed {p : ℝ × ℝ | h p.1 ≤ p.2} := by
    refine isClosed_le ?_ continuous_snd
    exact (Real.continuous_sqrt.comp (continuous_const.sub (continuous_fst.pow 2)))
  simpa [T, ofPred_and] using h1.inter h2

/--
@isnad1 id=measurab.0h0v.s3.6186f3e46054 from=translated src=- shape=0b0a4f6e vocab=99bf4fc5
-/
lemma measurableSet_T : MeasurableSet T := isClosed_T.measurableSet

/--
@isnad1 id=le.0h0v.s6.78cce6848a44 from=translated src=- shape=e668af9e vocab=69553ba5
-/
lemma T_subset_prod : T ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioi (0 : ℝ) := by
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  exact ⟨abs_le.mp hx, lt_of_lt_of_le (h_pos hx) hy⟩

/--
@isnad1 id=eq.0h1v.s6.0830547aeed3 from=translated src=- shape=b11dd0f2 vocab=0bcf5994
-/
lemma setIntegral_D (G : ℂ → ℂ) : ∫ z in D, G z = ∫ p in T, G ⟨p.1, p.2⟩ := by
  rw [← preimage_D]
  exact ((Complex.volume_preserving_equiv_real_prod.symm _).setIntegral_preimage_emb
    measurableEquivRealProd.symm.measurableEmbedding G D).symm

/--
@isnad1 id=integrab.3h3v.s7.513633b57cfa from=translated src=- shape=5a3c4bcb vocab=71475018
-/
lemma integrableOn_T_of_bound {G : ℝ × ℝ → ℂ} {C δ : ℝ} (hδ : 0 < δ)
    (hG : ContinuousOn G T) (hb : ∀ p ∈ T, ‖G p‖ ≤ C * Real.exp (-δ * p.2)) :
    IntegrableOn G T := by
  have hdom : IntegrableOn (fun p : ℝ × ℝ => (C : ℝ) * Real.exp (-δ * p.2))
      (Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ioi (0 : ℝ)) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    have h1 : Integrable (fun _ : ℝ => (C : ℝ)) (volume.restrict (Icc (-(1 / 2 : ℝ)) (1 / 2))) :=
      integrable_const _
    have h2 : Integrable (fun y : ℝ => Real.exp (-δ * y)) (volume.restrict (Ioi (0 : ℝ))) :=
      exp_neg_integrableOn_Ioi 0 hδ
    exact h1.mul_prod h2
  refine Integrable.mono' (hdom.mono_set T_subset_prod)
    (hG.aestronglyMeasurable measurableSet_T) ?_
  exact (ae_restrict_iff' measurableSet_T).mpr (Eventually.of_forall hb)

/--
@isnad1 id=eq.1h1v.s7.1773c323dc3b from=translated src=- shape=6522bf9a vocab=1d75c5e9
-/
lemma setIntegral_T_eq_x_y {G : ℝ × ℝ → ℂ} (hG : IntegrableOn G T) :
    ∫ p in T, G p = ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), ∫ y in Ici (h x), G (x, y) := by
  have hi : Integrable (T.indicator G) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hG.integrable_indicator measurableSet_T
  rw [← integral_indicator measurableSet_T, Measure.volume_eq_prod, integral_prod _ hi]
  have hS : {x : ℝ | |x| ≤ 1 / 2} = Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    ext x; simp [abs_le]
  rw [← hS, ← integral_indicator (measurableSet_le continuous_abs.measurable measurable_const)]
  congr 1 with x
  by_cases hx : |x| ≤ 1 / 2
  · rw [indicator_of_mem (by exact hx), ← integral_indicator measurableSet_Ici]
    congr 1 with y
    by_cases hy : h x ≤ y
    · rw [indicator_of_mem (show (x, y) ∈ T from ⟨hx, hy⟩), indicator_of_mem (by exact hy)]
    · rw [indicator_of_notMem (show (x, y) ∉ T from fun hm => hy hm.2),
        indicator_of_notMem (by exact hy)]
  · rw [indicator_of_notMem (by exact hx)]
    have : ∀ y, T.indicator G (x, y) = 0 := fun y =>
      indicator_of_notMem (show (x, y) ∉ T from fun hm => hx hm.1) _
    simp [this]

/--
@isnad1 id=eq.1h1v.s7.0932f9b8989f from=translated src=- shape=60280314 vocab=f27063d9
-/
lemma setIntegral_T_eq_y_x {G : ℝ × ℝ → ℂ} (hG : IntegrableOn G T) :
    ∫ p in T, G p = ∫ y, ∫ x in {x | |x| ≤ 1 / 2 ∧ h x ≤ y}, G (x, y) := by
  have hi : Integrable (T.indicator G) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]; exact hG.integrable_indicator measurableSet_T
  rw [← integral_indicator measurableSet_T, Measure.volume_eq_prod, integral_prod_symm _ hi]
  congr 1 with y
  have hm : MeasurableSet {x : ℝ | |x| ≤ 1 / 2 ∧ h x ≤ y} := by
    have : IsClosed {x : ℝ | |x| ≤ 1 / 2 ∧ h x ≤ y} := by
      rw [ofPred_and]
      exact (isClosed_le continuous_abs continuous_const).inter
        (isClosed_le (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2)))
          continuous_const)
    exact this.measurableSet
  rw [← integral_indicator hm]
  congr 1 with x

section Hyp

variable (Φ : ℂ → ℂ) (Φ' : ℂ → ℂ →L[ℝ] ℂ) (U : Set ℂ) (δ : ℝ) (hδ : 0 < δ) (hU : IsOpen U)
  (hDU : D ⊆ U) (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) (hc : ContinuousOn Φ' U)
  (hΦ : ∃ C : ℝ, ∀ z ∈ U, ‖Φ z‖ ≤ C * Real.exp (-δ * z.im))
  (hΦ' : ∃ C : ℝ, ∀ z ∈ U, ‖Φ' z‖ ≤ C * Real.exp (-δ * z.im))

/--
@isnad1 id=eq.0h2v.s4.75528f14e0de from=translated src=- shape=60689d7d vocab=8ee53555
-/
lemma mk_eq (x y : ℝ) : (⟨x, y⟩ : ℂ) = (x : ℂ) + (y : ℂ) * I := Complex.mk_eq_add_mul_I x y

/--
@isnad1 id=hasderiv.2h5v.s9.8debe530b5a1 from=translated src=- shape=d4729743 vocab=f6277194
-/
lemma hasDerivAt_vert {x y : ℝ} (hz : (⟨x, y⟩ : ℂ) ∈ U)
    (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) :
    HasDerivAt (fun t : ℝ => Φ ⟨x, t⟩) (Φ' ⟨x, y⟩ I) y := by
  have h1 : HasDerivAt (fun t : ℝ => (x : ℂ) + (t : ℂ) * I) I y := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).const_add (x : ℂ)
  have h2 : (fun t : ℝ => Φ ⟨x, t⟩) = Φ ∘ fun t : ℝ => (x : ℂ) + (t : ℂ) * I := by
    ext t; simp [mk_eq]
  rw [h2]
  have hz' : (x : ℂ) + (y : ℂ) * I ∈ U := by rwa [← mk_eq]
  have := (hd _ hz').comp_hasDerivAt y h1
  rwa [← mk_eq] at this

/--
@isnad1 id=hasderiv.2h5v.s9.0570a4961d7f from=translated src=- shape=f2ac3546 vocab=a32d1193
-/
lemma hasDerivAt_horiz {x y : ℝ} (hz : (⟨x, y⟩ : ℂ) ∈ U)
    (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) :
    HasDerivAt (fun t : ℝ => Φ ⟨t, y⟩) (Φ' ⟨x, y⟩ 1) x := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) + (y : ℂ) * I) 1 x := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).add_const ((y : ℂ) * I)
  have h2 : (fun t : ℝ => Φ ⟨t, y⟩) = Φ ∘ fun t : ℝ => (t : ℂ) + (y : ℂ) * I := by
    ext t; simp [mk_eq]
  rw [h2]
  have hz' : (x : ℂ) + (y : ℂ) * I ∈ U := by rwa [← mk_eq]
  have := (hd _ hz').comp_hasDerivAt x h1
  rwa [← mk_eq] at this

/--
@isnad1 id=continuo.0h1v.s4.2a9e68197d06 from=translated src=- shape=4827ab61 vocab=3a04ec19
-/
lemma continuous_mk_left (x : ℝ) : Continuous fun t : ℝ => (⟨x, t⟩ : ℂ) := by
  simp [mk_eq]
  exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))

/--
@isnad1 id=continuo.0h1v.s4.5d4147fda5c0 from=translated src=- shape=a4c439d3 vocab=3a04ec19
-/
lemma continuous_mk_right (y : ℝ) : Continuous fun t : ℝ => (⟨t, y⟩ : ℂ) := by
  simp [mk_eq]
  exact (Complex.continuous_ofReal.add continuous_const)

/--
@isnad1 id=tendsto.1h2v.s5.f0f1d3107eee from=translated src=- shape=ad6bdb01 vocab=c366e2e9
-/
lemma tendsto_const_mul_exp {δ : ℝ} (hδ : 0 < δ) (C : ℝ) :
    Tendsto (fun t : ℝ => C * Real.exp (-δ * t)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => Real.exp (-δ * t)) atTop (𝓝 0) := by
    refine Real.tendsto_exp_comp_nhds_zero.mpr ?_
    exact (tendsto_id (α := ℝ) (x := atTop)).const_mul_atTop_of_neg (neg_lt_zero.mpr hδ)
  simpa using h1.const_mul C

include hδ hDU hd hc hΦ hΦ' in

/--
@isnad1 id=eq.7h5v.s10.d9ee63690d40 from=translated src=- shape=d7633c6b vocab=e74e3fe1
-/
lemma integral_vert {x : ℝ} (hx : |x| ≤ 1 / 2) :
    ∫ y in Ioi (h x), Φ' ⟨x, y⟩ I = -Φ ⟨x, h x⟩ := by
  obtain ⟨C, hC⟩ := hΦ
  obtain ⟨C', hC'⟩ := hΦ'
  have hmem : ∀ t ∈ Ici (h x), (⟨x, t⟩ : ℂ) ∈ U := fun t ht => hDU (mk_mem_D hx ht)
  have hderiv : ∀ t ∈ Ici (h x), HasDerivAt (fun t : ℝ => Φ ⟨x, t⟩) (Φ' ⟨x, t⟩ I) t :=
    fun t ht => hasDerivAt_vert Φ Φ' U (hmem t ht) hd
  have hcont : ContinuousOn (fun t : ℝ => Φ' ⟨x, t⟩ I) (Ici (h x)) := by
    have h1 : ContinuousOn (fun t : ℝ => Φ' ⟨x, t⟩) (Ici (h x)) :=
      hc.comp (continuous_mk_left x).continuousOn hmem
    exact h1.clm_apply continuousOn_const
  have hint : IntegrableOn (fun t : ℝ => Φ' ⟨x, t⟩ I) (Ioi (h x)) := by
    have hdom : IntegrableOn (fun t : ℝ => C' * Real.exp (-δ * t)) (Ioi (h x)) :=
      (exp_neg_integrableOn_Ioi _ hδ).const_mul C'
    refine Integrable.mono' hdom
      ((hcont.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    calc ‖Φ' ⟨x, t⟩ I‖ ≤ ‖Φ' ⟨x, t⟩‖ * ‖I‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖Φ' ⟨x, t⟩‖ := by rw [Complex.norm_I, mul_one]
      _ ≤ C' * Real.exp (-δ * t) := hC' _ (hmem t (mem_Ici.mpr (le_of_lt ht)))
  have hlim : Tendsto (fun t : ℝ => Φ ⟨x, t⟩) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_mul_exp hδ C)
    filter_upwards [Ici_mem_atTop (h x)] with t ht
    exact hC _ (hmem t ht)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim, zero_sub]

include hd in

/--
@isnad1 id=eq.4h6v.s9.6b766df0b35e from=translated src=- shape=af008f27 vocab=5872afb9
-/
lemma integral_horiz {a b y : ℝ} (hab : a ≤ b) (hmem : ∀ t ∈ Icc a b, (⟨t, y⟩ : ℂ) ∈ U)
    (hc : ContinuousOn Φ' U) :
    ∫ t in a..b, Φ' ⟨t, y⟩ 1 = Φ ⟨b, y⟩ - Φ ⟨a, y⟩ := by
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt (fun t : ℝ => Φ ⟨t, y⟩) (Φ' ⟨t, y⟩ 1) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    exact hasDerivAt_horiz Φ Φ' U (hmem t ht) hd
  have hcont : ContinuousOn (fun t : ℝ => Φ' ⟨t, y⟩ 1) (uIcc a b) := by
    rw [uIcc_of_le hab]
    have h1 : ContinuousOn (fun t : ℝ => Φ' ⟨t, y⟩) (Icc a b) :=
      hc.comp (continuous_mk_right y).continuousOn hmem
    exact h1.clm_apply continuousOn_const
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)

def r (y : ℝ) : ℝ := Real.sqrt (1 - y ^ 2)

/--
@isnad1 id=le.0h1v.s3.8a26b404081b from=translated src=- shape=8a62b088 vocab=b6a32830
-/
lemma r_nonneg (y : ℝ) : 0 ≤ r y := Real.sqrt_nonneg _

/--
@isnad1 id=eq.0h0v.s3.cd548b8057f8 from=translated src=- shape=3c26ae4f vocab=98c0ba60
-/
lemma r_one : r 1 = 0 := by simp [r]

/--
@isnad1 id=lt.2h1v.s5.4b6d49e5f88f from=translated src=- shape=536e06c9 vocab=d6352aba
-/
lemma r_pos {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 1) : 0 < r y := by
  unfold r; apply Real.sqrt_pos.mpr; nlinarith

/--
@isnad1 id=le.1h1v.s5.5a160c2e7559 from=translated src=- shape=a2daaf09 vocab=428cdb42
-/
lemma r_le_half {y : ℝ} (hy : Real.sqrt 3 / 2 ≤ y) : r y ≤ 1 / 2 := by
  unfold r
  rw [Real.sqrt_le_left (by norm_num)]
  have := sqrt3_sq
  nlinarith [sqrt3_pos]

/--
@isnad1 id=lt.1h1v.s5.d0ce74d64b34 from=translated src=- shape=a2daaf09 vocab=658f6a64
-/
lemma r_lt_half {y : ℝ} (hy : Real.sqrt 3 / 2 < y) : r y < 1 / 2 := by
  unfold r
  rw [Real.sqrt_lt' (by norm_num)]
  have := sqrt3_sq
  nlinarith [sqrt3_pos]

/--
@isnad1 id=eq.0h0v.s5.800c24ace441 from=translated src=- shape=9ef1c5e0 vocab=e92766d3
-/
lemma h_half : h (1 / 2) = Real.sqrt 3 / 2 := by
  unfold h
  rw [show (1 : ℝ) - (1 / 2) ^ 2 = (Real.sqrt 3 / 2) ^ 2 by rw [sqrt3_sq]; norm_num,
    Real.sqrt_sq sqrt3_pos.le]

/--
@isnad1 id=eq.0h1v.s3.00e4d49f05e1 from=translated src=- shape=cd419dad vocab=f7f2c85e
-/
lemma h_neg (x : ℝ) : h (-x) = h x := by simp [h]

/--
@isnad1 id=eq.2h1v.s4.714d539d8f34 from=translated src=- shape=80704693 vocab=2e48313e
-/
lemma h_r {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : h (r y) = y := by
  unfold h r
  rw [Real.sq_sqrt (by nlinarith), sub_sub_cancel, Real.sqrt_sq hy0]

/--
@isnad1 id=iff.1h2v.s5.285dddef6e44 from=translated src=- shape=bf13c750 vocab=ca756c4f
-/
lemma h_le_iff {x y : ℝ} (hy : 0 ≤ y) : h x ≤ y ↔ r y ≤ |x| := by
  unfold h r
  rw [Real.sqrt_le_left hy, Real.sqrt_le_left (abs_nonneg x), sq_abs]
  constructor <;> intro h <;> linarith

/--
@isnad1 id=eq.1h1v.s6.5f6f9c3a1d6a from=translated src=- shape=d50ee7da vocab=307fe840
-/
lemma slice_of_one_le {y : ℝ} (hy : 1 ≤ y) :
    {x : ℝ | |x| ≤ 1 / 2 ∧ h x ≤ y} = Icc (-(1 / 2)) (1 / 2) := by
  ext x
  simp only [mem_ofPred_eq, mem_Icc, abs_le]
  exact ⟨fun h => h.1, fun h => ⟨h, (h_le_one x).trans hy⟩⟩

/--
@isnad1 id=eq.2h1v.s7.d47e6e8e5013 from=translated src=- shape=4a510ce1 vocab=1ab50f1a
-/
lemma slice_of_lt_one {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 1) :
    {x : ℝ | |x| ≤ 1 / 2 ∧ h x ≤ y} = Icc (-(1 / 2)) (-r y) ∪ Icc (r y) (1 / 2) := by
  have hr := r_pos hy0 hy
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_Icc, h_le_iff hy0, abs_le, le_abs']
  constructor
  · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
    · exact Or.inl ⟨h1, h3⟩
    · exact Or.inr ⟨h3, h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨⟨h1, by linarith⟩, Or.inl h2⟩
    · exact ⟨⟨by linarith, h2⟩, Or.inr h1⟩

/--
@isnad1 id=eq.1h1v.s6.26f89dcde306 from=translated src=- shape=be4534a3 vocab=2165692f
-/
lemma slice_of_lt {y : ℝ} (hy : y < Real.sqrt 3 / 2) : {x : ℝ | |x| ≤ 1 / 2 ∧ h x ≤ y} = ∅ := by
  ext x
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
  exact fun hx => lt_of_lt_of_le hy (sqrt3_le_h hx)

/--
@isnad1 id=mem.2h1v.s5.d8262c38553a from=translated src=- shape=95429902 vocab=d0b34d58
-/
lemma mem_D_r {y : ℝ} (hy : Real.sqrt 3 / 2 ≤ y) (hy1 : y ≤ 1) : (⟨r y, y⟩ : ℂ) ∈ D := by
  have hy0 : 0 ≤ y := sqrt3_pos.le.trans hy
  refine mk_mem_D ?_ (h_r hy0 hy1).le
  rw [abs_of_nonneg (r_nonneg y)]; exact r_le_half hy

/--
@isnad1 id=mem.2h1v.s5.9c8db4af8e95 from=translated src=- shape=b41b229b vocab=179774a5
-/
lemma mem_D_neg_r {y : ℝ} (hy : Real.sqrt 3 / 2 ≤ y) (hy1 : y ≤ 1) : (⟨-r y, y⟩ : ℂ) ∈ D := by
  have hy0 : 0 ≤ y := sqrt3_pos.le.trans hy
  refine mk_mem_D ?_ (by rw [h_neg]; exact (h_r hy0 hy1).le)
  rw [abs_neg, abs_of_nonneg (r_nonneg y)]; exact r_le_half hy

/--
@isnad1 id=continuo.0h0v.s3.cfa27841f906 from=translated src=- shape=e3d48bcb vocab=3a5d9d01
-/
lemma continuous_r : Continuous r := Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))

/--
@isnad1 id=continuo.0h0v.s5.b4005bb35a7a from=translated src=- shape=e37279c3 vocab=1bb69a95
-/
lemma continuous_mk2 : Continuous fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ) := by
  simp [mk_eq]
  exact ((Complex.continuous_ofReal.comp continuous_fst).add
    ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))

def corr (y : ℝ) : ℂ := Φ ⟨-r y, y⟩ - Φ ⟨r y, y⟩

include hd hDU in
/--
@isnad1 id=continuo.2h3v.s8.5f13c1066e19 from=translated src=- shape=fbc78f29 vocab=885ab8b8
-/
lemma continuousOn_corr : ContinuousOn (corr Φ) (Icc (Real.sqrt 3 / 2) 1) := by
  have hΦc : ContinuousOn Φ U := fun z hz => (hd z hz).continuousAt.continuousWithinAt
  apply ContinuousOn.sub
  · refine hΦc.comp (continuous_mk2.comp (continuous_r.neg.prodMk continuous_id)).continuousOn ?_
    exact fun y hy => hDU (mem_D_neg_r hy.1 hy.2)
  · refine hΦc.comp (continuous_mk2.comp (continuous_r.prodMk continuous_id)).continuousOn ?_
    exact fun y hy => hDU (mem_D_r hy.1 hy.2)

include hδ hd hDU hΦ in

/--
@isnad1 id=integrab.5h5v.s8.114f3edcd868 from=translated src=- shape=9062e5ef vocab=02af0147
-/
lemma integrableOn_vert {x : ℝ} (hx : |x| ≤ 1 / 2) :
    IntegrableOn (fun y : ℝ => Φ ⟨x, y⟩) (Ioi (h x)) := by
  obtain ⟨C, hC⟩ := hΦ
  have hΦc : ContinuousOn Φ U := fun z hz => (hd z hz).continuousAt.continuousWithinAt
  have hmem : ∀ t ∈ Ioi (h x), (⟨x, t⟩ : ℂ) ∈ U := fun t ht => hDU (mk_mem_D hx (le_of_lt ht))
  have hcont : ContinuousOn (fun t : ℝ => Φ ⟨x, t⟩) (Ioi (h x)) :=
    hΦc.comp (continuous_mk_left x).continuousOn hmem
  have hdom : IntegrableOn (fun t : ℝ => C * Real.exp (-δ * t)) (Ioi (h x)) :=
    (exp_neg_integrableOn_Ioi _ hδ).const_mul C
  refine Integrable.mono' hdom (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => hC _ (hmem t ht))

include hd hDU hc in

/--
@isnad1 id=eq.4h4v.s9.f1a8d1bb9db8 from=translated src=- shape=4cf36392 vocab=fd8f989f
-/
lemma sliceIntegral {y : ℝ} (hy : Real.sqrt 3 / 2 < y) :
    ∫ x in {x : ℝ | |x| ≤ 1 / 2 ∧ h x ≤ y}, Φ' ⟨x, y⟩ 1 =
      (Φ ⟨1 / 2, y⟩ - Φ ⟨-(1 / 2), y⟩) + (Iic (1 : ℝ)).indicator (corr Φ) y := by
  have hy0 : 0 ≤ y := sqrt3_pos.le.trans hy.le
  rcases lt_or_ge y 1 with hy1 | hy1
  · rw [indicator_of_mem (show y ∈ Iic (1 : ℝ) from hy1.le), slice_of_lt_one hy0 hy1]
    have hr := r_pos hy0 hy1
    have hr' := r_lt_half hy
    have hmem : ∀ t : ℝ, |t| ≤ 1 / 2 → r y ≤ |t| → (⟨t, y⟩ : ℂ) ∈ U :=
      fun t ht ht' => hDU (mk_mem_D ht ((h_le_iff hy0).mpr ht'))
    have hmem₁ : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (-r y), (⟨t, y⟩ : ℂ) ∈ U := fun t ht =>
      hmem t (abs_le.mpr ⟨ht.1, by linarith [ht.2]⟩) (le_abs'.mpr (Or.inl ht.2))
    have hmem₂ : ∀ t ∈ Icc (r y) (1 / 2 : ℝ), (⟨t, y⟩ : ℂ) ∈ U := fun t ht =>
      hmem t (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩) (le_abs'.mpr (Or.inr ht.1))
    have hcont : ∀ s : Set ℝ, (∀ t ∈ s, (⟨t, y⟩ : ℂ) ∈ U) →
        ContinuousOn (fun t : ℝ => Φ' ⟨t, y⟩ 1) s := fun s hs =>
      (hc.comp (continuous_mk_right y).continuousOn hs).clm_apply continuousOn_const
    rw [setIntegral_union (Set.disjoint_iff.mpr ?_) measurableSet_Icc
      ((hcont _ hmem₁).integrableOn_Icc) ((hcont _ hmem₂).integrableOn_Icc),
      integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith), ← intervalIntegral.integral_of_le hr'.le,
      integral_horiz Φ Φ' U hd (by linarith) hmem₁ hc, integral_horiz Φ Φ' U hd hr'.le hmem₂ hc]
    · simp only [corr]; ring
    · rintro t ⟨⟨-, h1⟩, ⟨h2, -⟩⟩; exact absurd (h2.trans h1) (by linarith)
  · rw [slice_of_one_le hy1, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num)]
    have hmem : ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), (⟨t, y⟩ : ℂ) ∈ U := fun t ht =>
      hDU (mk_mem_D (abs_le.mpr ⟨ht.1, ht.2⟩) ((h_le_one t).trans hy1))
    rw [integral_horiz Φ Φ' U hd (by norm_num) hmem hc]
    rcases hy1.lt_or_eq with hy1 | rfl
    · rw [indicator_of_notMem (show y ∉ Iic (1 : ℝ) from not_le.mpr hy1), add_zero]
    · simp [corr, r_one]

include hδ hDU hd hc hΦ hΦ' in

/--
@isnad1 id=eq.6h4v.s10.0201bb9d0299 from=translated src=- shape=1bc27bb6 vocab=f1defc89
-/
lemma integral_T_horiz :
    ∫ p in T, Φ' ⟨p.1, p.2⟩ 1 =
      ((∫ y in Ioi (Real.sqrt 3 / 2), Φ ⟨1 / 2, y⟩) - ∫ y in Ioi (Real.sqrt 3 / 2), Φ ⟨-(1 / 2), y⟩)
        + ∫ y in (Real.sqrt 3 / 2)..1, corr Φ y := by
  obtain ⟨C', hC'⟩ := hΦ'
  have hG : IntegrableOn (fun p : ℝ × ℝ => Φ' ⟨p.1, p.2⟩ 1) T := by
    refine integrableOn_T_of_bound hδ ?_ (C := C') fun p hp => ?_
    · refine (hc.comp continuous_mk2.continuousOn fun p hp => hDU (mk_mem_D hp.1 hp.2)).clm_apply
        continuousOn_const
    · calc ‖Φ' ⟨p.1, p.2⟩ 1‖ ≤ ‖Φ' ⟨p.1, p.2⟩‖ * ‖(1 : ℂ)‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖Φ' ⟨p.1, p.2⟩‖ := by rw [norm_one, mul_one]
        _ ≤ C' * Real.exp (-δ * p.2) := hC' _ (hDU (mk_mem_D hp.1 hp.2))
  rw [setIntegral_T_eq_y_x hG]

  have hae : (fun y => ∫ x in {x : ℝ | |x| ≤ 1 / 2 ∧ h x ≤ y}, Φ' ⟨x, y⟩ 1) =ᵐ[volume]
      (Ioi (Real.sqrt 3 / 2)).indicator fun y =>
        (Φ ⟨1 / 2, y⟩ - Φ ⟨-(1 / 2), y⟩) + (Iic (1 : ℝ)).indicator (corr Φ) y := by
    have : ∀ᵐ y : ℝ ∂volume, y ∉ ({Real.sqrt 3 / 2} : Set ℝ) :=
      measure_eq_zero_iff_ae_notMem.mp Real.volume_singleton
    filter_upwards [this] with y hy
    rcases lt_or_gt_of_ne (fun h : y = Real.sqrt 3 / 2 => hy h) with hy | hy
    · rw [indicator_of_notMem (show y ∉ Ioi (Real.sqrt 3 / 2) from not_lt.mpr hy.le),
        slice_of_lt hy, Measure.restrict_empty, integral_zero_measure]
    · rw [indicator_of_mem (show y ∈ Ioi (Real.sqrt 3 / 2) from hy)]
      exact sliceIntegral Φ Φ' U hDU hd hc hy
  rw [integral_congr_ae hae, integral_indicator measurableSet_Ioi]
  have h1 : IntegrableOn (fun y : ℝ => Φ ⟨1 / 2, y⟩) (Ioi (Real.sqrt 3 / 2)) := by
    have := integrableOn_vert Φ Φ' U δ hδ hDU hd hΦ (x := 1 / 2) (by rw [abs_of_pos (by norm_num)])
    rwa [h_half] at this
  have h2 : IntegrableOn (fun y : ℝ => Φ ⟨-(1 / 2), y⟩) (Ioi (Real.sqrt 3 / 2)) := by
    have := integrableOn_vert Φ Φ' U δ hδ hDU hd hΦ (x := -(1 / 2))
      (by rw [abs_neg, abs_of_pos (by norm_num)])
    rwa [h_neg, h_half] at this
  have h3 : IntegrableOn ((Iic (1 : ℝ)).indicator (corr Φ)) (Ioi (Real.sqrt 3 / 2)) := by
    rw [IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic,
      show Iic (1 : ℝ) ∩ Ioi (Real.sqrt 3 / 2) = Ioc (Real.sqrt 3 / 2) 1 by
        rw [inter_comm, Ioi_inter_Iic]]
    exact ((continuousOn_corr Φ Φ' U hDU hd).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h12 : IntegrableOn (fun y : ℝ => Φ ⟨1 / 2, y⟩ - Φ ⟨-(1 / 2), y⟩) (Ioi (Real.sqrt 3 / 2)) :=
    h1.sub h2
  rw [integral_add h12 h3, integral_sub h1 h2, setIntegral_indicator measurableSet_Iic,
    Ioi_inter_Iic, intervalIntegral.integral_of_le sqrt3_lt_one.le]

include hδ hDU hc hΦ' in
/--
@isnad1 id=integrab.4h4v.s9.0b8ca1a64809 from=translated src=- shape=a2765c59 vocab=c7ae66e8
-/
lemma integrableOn_T_apply (v : ℂ) : IntegrableOn (fun p : ℝ × ℝ => Φ' ⟨p.1, p.2⟩ v) T := by
  obtain ⟨C', hC'⟩ := hΦ'
  refine integrableOn_T_of_bound hδ ?_ (C := C' * ‖v‖) fun p hp => ?_
  · exact (hc.comp continuous_mk2.continuousOn fun p hp => hDU (mk_mem_D hp.1 hp.2)).clm_apply
      continuousOn_const
  · calc ‖Φ' ⟨p.1, p.2⟩ v‖ ≤ ‖Φ' ⟨p.1, p.2⟩‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C' * Real.exp (-δ * p.2) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (hC' _ (hDU (mk_mem_D hp.1 hp.2))) (norm_nonneg _)
      _ = C' * ‖v‖ * Real.exp (-δ * p.2) := by ring

include hδ hDU hd hc hΦ hΦ' in

/--
@isnad1 id=eq.6h4v.s10.19a48191e437 from=translated src=- shape=9c368da0 vocab=a6c6b1ec
-/
lemma integral_T_vert :
    ∫ p in T, Φ' ⟨p.1, p.2⟩ I = -∫ x in (-(1 / 2 : ℝ))..(1 / 2), Φ ⟨x, h x⟩ := by
  rw [setIntegral_T_eq_x_y (integrableOn_T_apply Φ' U δ hδ hDU hc hΦ' I),
    intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
  have hx' : |x| ≤ 1 / 2 := abs_le.mpr ⟨hx.1, hx.2⟩
  rw [integral_Ici_eq_integral_Ioi]
  exact integral_vert Φ Φ' U δ hδ hDU hd hc hΦ hΦ' hx'

def γ (θ : ℝ) : ℂ := ⟨Real.cos θ, Real.sin θ⟩

/--
@isnad1 id=eq.0h1v.s4.5787fff38b48 from=translated src=- shape=17710795 vocab=d92b33e3
-/
lemma exp_mul_I_eq (θ : ℝ) : Complex.exp (θ * I) = γ θ :=
  Complex.ext (Complex.exp_ofReal_mul_I_re θ) (Complex.exp_ofReal_mul_I_im θ)

/--
@isnad1 id=continuo.0h0v.s4.c199eb29f210 from=translated src=- shape=54c8eceb vocab=4c670b2e
-/
lemma continuous_γ : Continuous γ :=
  continuous_mk2.comp (Real.continuous_cos.prodMk Real.continuous_sin)

/--
@isnad1 id=eq.0h0v.s5.f498d50c454f from=translated src=- shape=5290897d vocab=7cca8a66
-/
lemma cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -(1 / 2) := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]

/--
@isnad1 id=eq.0h0v.s5.121fde849775 from=translated src=- shape=44273b4f vocab=1eba1935
-/
lemma sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]

/--
@isnad1 id=le.0h0v.s5.1885e241cab6 from=translated src=- shape=e6f052ef vocab=4e693cc6
-/
lemma pi_div_three_le : Real.pi / 3 ≤ 2 * Real.pi / 3 := by linarith [Real.pi_pos]

/--
@isnad1 id=le.1h1v.s6.80c05ee8694e from=translated src=- shape=bd10823d vocab=50ac21a1
-/
lemma abs_cos_le {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 3) (2 * Real.pi / 3)) :
    |Real.cos θ| ≤ 1 / 2 := by
  have hπ := Real.pi_pos
  rw [abs_le]
  constructor
  · have := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [hθ.1]) (by linarith) hθ.2
    rw [cos_two_pi_div_three] at this
    exact this
  · have := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) (by linarith [hθ.2]) hθ.1
    rwa [Real.cos_pi_div_three] at this

/--
@isnad1 id=le.1h1v.s6.22e9b02d6e13 from=translated src=- shape=76823355 vocab=a47843df
-/
lemma sin_nonneg_arc {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 3) (2 * Real.pi / 3)) : 0 ≤ Real.sin θ :=
  Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1, Real.pi_pos])
    (by linarith [hθ.2, Real.pi_pos])

/--
@isnad1 id=eq.1h1v.s6.f02004ca7f1a from=translated src=- shape=be1f46f1 vocab=06d1e7f1
-/
lemma h_cos {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 3) (2 * Real.pi / 3)) :
    h (Real.cos θ) = Real.sin θ := by
  unfold h
  rw [← Real.sin_sq θ, Real.sqrt_sq (sin_nonneg_arc hθ)]

/--
@isnad1 id=eq.0h1v.s3.fb7c3699aeb1 from=translated src=- shape=176da496 vocab=508fc470
-/
lemma r_sin (θ : ℝ) : r (Real.sin θ) = |Real.cos θ| := by
  unfold r
  rw [← Real.cos_sq' θ, Real.sqrt_sq_eq_abs]

/--
@isnad1 id=mem.1h1v.s6.1fcaab519b90 from=translated src=- shape=80baab2a vocab=b387c694
-/
lemma γ_mem_D {θ : ℝ} (hθ : θ ∈ Icc (Real.pi / 3) (2 * Real.pi / 3)) : γ θ ∈ D :=
  mk_mem_D (abs_cos_le hθ) (h_cos hθ).le

/--
@isnad1 id=continuo.1h3v.s8.e409039da368 from=translated src=- shape=2812832c vocab=65a4b2df
-/
lemma continuousOn_Φ (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) : ContinuousOn Φ U :=
  fun z hz => (hd z hz).continuousAt.continuousWithinAt

include hd hDU in
/--
@isnad1 id=continuo.2h3v.s8.f5249142acfb from=translated src=- shape=5057678d vocab=38fafe2c
-/
lemma continuousOn_arc : ContinuousOn (fun θ => Φ (γ θ)) (Icc (Real.pi / 3) (2 * Real.pi / 3)) :=
  (continuousOn_Φ Φ Φ' U hd).comp continuous_γ.continuousOn fun _ hθ => hDU (γ_mem_D hθ)

/--
@isnad1 id=eq.0h1v.s7.2c99dce116b6 from=translated src=- shape=1c9ae3fa vocab=60d65a51
-/
lemma arc_sin :
    ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.sin θ • Φ (γ θ) =
      ∫ x in (-(1 / 2 : ℝ))..(1 / 2), Φ ⟨x, h x⟩ := by
  have hab := pi_div_three_le
  have key : ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
      (-Real.sin θ) • ((fun x : ℝ => Φ ⟨x, h x⟩) ∘ Real.cos) θ =
        -∫ x in (-(1 / 2 : ℝ))..(1 / 2), Φ ⟨x, h x⟩ := by
    rw [intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos Real.continuous_cos.continuousOn
      (fun θ _ => Real.hasDerivAt_cos θ) (fun θ hθ => ?_), Real.cos_pi_div_three,
      cos_two_pi_div_three, intervalIntegral.integral_symm]
    rw [min_eq_left hab, max_eq_right hab] at hθ
    exact neg_nonpos.mpr (sin_nonneg_arc (Ioo_subset_Icc_self hθ))
  calc ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.sin θ • Φ (γ θ)
      = ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
          -((-Real.sin θ) • ((fun x : ℝ => Φ ⟨x, h x⟩) ∘ Real.cos) θ) := by
        refine intervalIntegral.integral_congr fun θ hθ => ?_
        rw [uIcc_of_le hab] at hθ
        simp only [Function.comp_apply, neg_smul, neg_neg, h_cos hθ, γ]
    _ = _ := by rw [intervalIntegral.integral_neg, key, neg_neg]

include hd hDU in

/--
@isnad1 id=eq.2h3v.s8.7b183b0babe5 from=translated src=- shape=f4bc6afc vocab=4297fc67
-/
lemma arc_cos :
    ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.cos θ • Φ (γ θ) =
      -∫ y in (Real.sqrt 3 / 2)..1, corr Φ y := by
  have hπ := Real.pi_pos
  have h1 : Real.pi / 3 ≤ Real.pi / 2 := by linarith
  have h2 : Real.pi / 2 ≤ 2 * Real.pi / 3 := by linarith
  have hΦc := continuousOn_Φ Φ Φ' U hd
  have hcont : ContinuousOn (fun θ => Real.cos θ • Φ (γ θ)) (Icc (Real.pi / 3) (2 * Real.pi / 3)) :=
    Real.continuous_cos.continuousOn.smul (continuousOn_arc Φ Φ' U hDU hd)
  have hi1 : IntervalIntegrable (fun θ => Real.cos θ • Φ (γ θ)) volume (Real.pi / 3) (Real.pi / 2) :=
    (hcont.mono (by rw [uIcc_of_le h1]; exact Icc_subset_Icc_right h2)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun θ => Real.cos θ • Φ (γ θ)) volume (Real.pi / 2)
      (2 * Real.pi / 3) :=
    (hcont.mono (by rw [uIcc_of_le h2]; exact Icc_subset_Icc_left h1)).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]

  have k1 : ∫ θ in (Real.pi / 3)..(Real.pi / 2), Real.cos θ • Φ (γ θ) =
      ∫ y in (Real.sqrt 3 / 2)..1, Φ ⟨r y, y⟩ := by
    rw [← Real.sin_pi_div_three, ← Real.sin_pi_div_two,
      ← intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (g := fun y : ℝ => Φ ⟨r y, y⟩)
        Real.continuous_sin.continuousOn (fun θ _ => Real.hasDerivAt_sin θ) (fun θ hθ => ?_)]
    · refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [uIcc_of_le h1] at hθ
      have hc0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩
      simp only [Function.comp_apply, γ, r_sin, abs_of_nonneg hc0]
    · rw [min_eq_left h1, max_eq_right h1] at hθ
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2.le⟩

  have k2 : ∫ θ in (Real.pi / 2)..(2 * Real.pi / 3), Real.cos θ • Φ (γ θ) =
      -∫ y in (Real.sqrt 3 / 2)..1, Φ ⟨-r y, y⟩ := by
    rw [← sin_two_pi_div_three, ← Real.sin_pi_div_two,
      ← intervalIntegral.integral_symm (Real.sin (2 * Real.pi / 3)) (Real.sin (Real.pi / 2)),
      ← intervalIntegral.integral_deriv_smul_comp_of_deriv_nonpos (g := fun y : ℝ => Φ ⟨-r y, y⟩)
        Real.continuous_sin.continuousOn (fun θ _ => Real.hasDerivAt_sin θ) (fun θ hθ => ?_)]
    · refine intervalIntegral.integral_congr fun θ hθ => ?_
      rw [uIcc_of_le h2] at hθ
      have hc0 : Real.cos θ ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 (by linarith [hθ.2])
      simp only [Function.comp_apply, γ, r_sin, abs_of_nonpos hc0, neg_neg]
    · rw [min_eq_left h2, max_eq_right h2] at hθ
      exact Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1.le (by linarith [hθ.2])
  have hg1 : IntervalIntegrable (fun y : ℝ => Φ ⟨r y, y⟩) volume (Real.sqrt 3 / 2) 1 := by
    refine (ContinuousOn.mono ?_ (by rw [uIcc_of_le sqrt3_lt_one.le])).intervalIntegrable
    exact hΦc.comp (continuous_mk2.comp (continuous_r.prodMk continuous_id)).continuousOn
      fun y hy => hDU (mem_D_r hy.1 hy.2)
  have hg2 : IntervalIntegrable (fun y : ℝ => Φ ⟨-r y, y⟩) volume (Real.sqrt 3 / 2) 1 := by
    refine (ContinuousOn.mono ?_ (by rw [uIcc_of_le sqrt3_lt_one.le])).intervalIntegrable
    exact hΦc.comp (continuous_mk2.comp (continuous_r.neg.prodMk continuous_id)).continuousOn
      fun y hy => hDU (mem_D_neg_r hy.1 hy.2)
  rw [k1, k2, show (corr Φ) = fun y => Φ ⟨-r y, y⟩ - Φ ⟨r y, y⟩ from rfl,
    intervalIntegral.integral_sub hg2 hg1]
  ring

/--
@isnad1 id=eq.0h2v.s7.071eae5b043d from=translated src=- shape=e9c2ce53 vocab=a56bf970
-/
lemma arc_integrand (θ : ℝ) :
    Φ (Complex.exp (θ * I)) * (I * Complex.exp (θ * I)) =
      -(Real.sin θ • Φ (γ θ)) + I * (Real.cos θ • Φ (γ θ)) := by
  rw [exp_mul_I_eq, Complex.real_smul, Complex.real_smul]
  have e : (γ θ : ℂ) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := mk_eq _ _
  generalize Φ (γ θ) = w
  rw [e]
  linear_combination ((Real.sin θ : ℂ) * w) * Complex.I_mul_I

include hd hDU in
/--
@isnad1 id=eq.2h3v.s9.7d831283b39f from=translated src=- shape=e4d29f05 vocab=f405abb2
-/
lemma arc_split :
    ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Φ (Complex.exp (θ * I)) * (I * Complex.exp (θ * I)) =
      -(∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.sin θ • Φ (γ θ)) +
        I * ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3), Real.cos θ • Φ (γ θ) := by
  have hab := pi_div_three_le
  have harc := continuousOn_arc Φ Φ' U hDU hd
  have hi1 : IntervalIntegrable (fun θ => Real.sin θ • Φ (γ θ)) volume (Real.pi / 3)
      (2 * Real.pi / 3) := by
    refine (ContinuousOn.mono ?_ (by rw [uIcc_of_le hab])).intervalIntegrable
    exact Real.continuous_sin.continuousOn.smul harc
  have hi2 : IntervalIntegrable (fun θ => Real.cos θ • Φ (γ θ)) volume (Real.pi / 3)
      (2 * Real.pi / 3) := by
    refine (ContinuousOn.mono ?_ (by rw [uIcc_of_le hab])).intervalIntegrable
    exact Real.continuous_cos.continuousOn.smul harc
  have hi1' : IntervalIntegrable (fun θ => -(Real.sin θ • Φ (γ θ))) volume (Real.pi / 3)
      (2 * Real.pi / 3) := hi1.neg
  have hi2' : IntervalIntegrable (fun θ => I * (Real.cos θ • Φ (γ θ))) volume (Real.pi / 3)
      (2 * Real.pi / 3) := hi2.const_mul I
  rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add hi1' hi2']
  exact intervalIntegral.integral_congr fun θ _ => arc_integrand Φ θ

include hδ hDU hd hc hΦ hΦ' in

/--
@isnad1 id=eq.6h4v.s10.5a80846550be from=translated src=- shape=6ca40abf vocab=dc50d320
-/
theorem main :
    (∫ z in D, (I • Φ' z 1 - Φ' z I)) =
      I • (∫ y in Ioi (Real.sqrt 3 / 2), Φ (1 / 2 + y * I))
        - I • (∫ y in Ioi (Real.sqrt 3 / 2), Φ (-(1 / 2) + y * I))
        - ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
            Φ (Complex.exp (θ * I)) * (I * Complex.exp (θ * I)) := by
  have hT := setIntegral_D (fun z => I • Φ' z 1 - Φ' z I)
  beta_reduce at hT
  rw [hT]
  have hA : Integrable (fun p : ℝ × ℝ => Φ' ⟨p.1, p.2⟩ I) (volume.restrict T) :=
    integrableOn_T_apply Φ' U δ hδ hDU hc hΦ' I
  have hB : Integrable (fun p : ℝ × ℝ => I • Φ' ⟨p.1, p.2⟩ 1) (volume.restrict T) :=
    (integrableOn_T_apply Φ' U δ hδ hDU hc hΦ' 1).smul I
  rw [integral_sub hB hA, integral_smul, integral_T_horiz Φ Φ' U δ hδ hDU hd hc hΦ hΦ',
    integral_T_vert Φ Φ' U δ hδ hDU hd hc hΦ hΦ', arc_split Φ Φ' U hDU hd,
    arc_sin Φ, arc_cos Φ Φ' U hDU hd]
  have e1 : ∀ y : ℝ, ((1 : ℂ) / 2 + y * I) = (⟨1 / 2, y⟩ : ℂ) := fun y =>
    Complex.ext (by simp) (by simp)
  have e2 : ∀ y : ℝ, (-((1 : ℂ) / 2) + y * I) = (⟨-(1 / 2), y⟩ : ℂ) := fun y =>
    Complex.ext (by simp) (by simp)
  simp_rw [e1, e2]
  simp only [smul_eq_mul]
  ring

end Hyp

end Complex.GreenFD

end

/--
@isnad1 id=eq.7h4v.s10.97c0ef9eadcf from=translated src=- shape=4731c67a vocab=90756ca4
-/
theorem solution
    (Φ : ℂ → ℂ) (Φ' : ℂ → ℂ →L[ℝ] ℂ) (U : Set ℂ) (δ : ℝ) (hδ : 0 < δ) (hU : IsOpen U)
    (hDU : {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im} ⊆ U)
    (hd : ∀ z ∈ U, HasFDerivAt Φ (Φ' z) z) (hc : ContinuousOn Φ' U)
    (hΦ : ∃ C : ℝ, ∀ z ∈ U, ‖Φ z‖ ≤ C * Real.exp (-δ * z.im))
    (hΦ' : ∃ C : ℝ, ∀ z ∈ U, ‖Φ' z‖ ≤ C * Real.exp (-δ * z.im)) :
    (∫ z in {z : ℂ | |z.re| ≤ 1 / 2 ∧ 1 ≤ ‖z‖ ∧ 0 < z.im}, (Complex.I • Φ' z 1 - Φ' z Complex.I)) =
      Complex.I • (∫ y in Set.Ioi (Real.sqrt 3 / 2), Φ (1 / 2 + y * Complex.I))
        - Complex.I • (∫ y in Set.Ioi (Real.sqrt 3 / 2), Φ (-(1 / 2) + y * Complex.I))
        - ∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
            Φ (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I)) :=
  Complex.GreenFD.main Φ Φ' U δ hδ hDU hd hc hΦ hΦ'
