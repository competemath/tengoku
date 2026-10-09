module

public import Tengoku.Carleson.Carleson.ToMathlib.MeasureTheory.Integral.Lebesgue

public section

open MeasureTheory NNReal ENNReal Set

noncomputable
instance NNReal.MeasureSpace : MeasureSpace ℝ≥0 := ⟨Measure.comap Subtype.val (volume : Measure ℝ)⟩

-- Upstreaming status:
-- The results in this file are generally worth having, but the proofs can be golfed
-- and refactored more (e.g., helper lemmas split out).

/--
@isnad1 id=eq.0h1v.s6.f38aeef1c87d from=translated src=- shape=331e75a7 vocab=caf90c12
-/
lemma NNReal.volume_val {s : Set ℝ≥0} : volume s = volume (Subtype.val '' s) := by
  apply comap_subtype_coe_apply measurableSet_Ici

-- sanity check: this measure is what you expect
example : volume (Ioo (3 : ℝ≥0) 5) = 2 := by
  erw [volume_val, NNReal.image_coe_Ioo, Real.volume_Ioo, ofReal_eq_ofNat]
  norm_num

-- integral over a function over NNReal equals the integral over the right set of real numbers

noncomputable
instance : MeasureSpace ℝ≥0∞ where
  volume := (volume : Measure ℝ≥0).map ENNReal.ofNNReal

--TODO: move these lemmas somewhere else?
/--
@isnad1 id=eq.0h1v.s4.808c8236b2f7 from=translated src=- shape=51af5cae vocab=9bb0d1f3
-/
lemma ENNReal.ofNNReal_preimage {s : Set ℝ≥0∞} :
    ENNReal.ofNNReal ⁻¹' s = ENNReal.toNNReal '' (s \ {⊤}) := by
  ext x
  simp only [mem_image, mem_sdiff, mem_singleton_iff, mem_preimage]
  constructor
  · intro h
    use ENNReal.ofNNReal x
    simpa
  · rintro ⟨y, hys, hyx⟩
    rw [← hyx, coe_toNNReal hys.2]
    exact hys.1

--TODO: move these lemmas somewhere else?
/--
@isnad1 id=eq.1h1v.s5.4afaceee4c0f from=translated src=- shape=23730a68 vocab=f334b041
-/
lemma ENNReal.map_toReal_eq_map_toReal_comap_ofReal {s : Set ℝ≥0∞} (h : ∞ ∉ s) :
    ENNReal.toReal '' s = NNReal.toReal '' (ENNReal.ofNNReal ⁻¹' s) := by
  rw [ofNNReal_preimage, image_image, sdiff_singleton_eq_self h]
  rfl

/--
@isnad1 id=eq.1h1v.s5.60799de2f7eb from=translated src=- shape=00167464 vocab=1777088d
-/
lemma ENNReal.map_toReal_eq_map_toReal_comap_ofReal' {s : Set ℝ≥0∞} (h : ∞ ∈ s) :
    ENNReal.toReal '' s = NNReal.toReal '' (ENNReal.ofNNReal ⁻¹' s) ∪ {0}:= by
  ext x
  simp only [mem_image]
  constructor
  · rintro ⟨y, hys, hyx⟩
    by_cases hy : y = ∞
    · rw [← hyx, hy]
      simp
    left
    use y.toNNReal
    simp only [mem_preimage]
    rw [coe_toNNReal hy]
    use hys
    rwa [coe_toNNReal_eq_toReal]
  · rintro (⟨y, hys, hyx⟩ | hx)
    · use ENNReal.ofNNReal y, hys, hyx
    · use ∞, h
      simp only [toReal_top, hx.symm]

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eventual.0h1v.s5.b8e8dcd3ed35 from=translated src=- shape=c1986ccb vocab=f3611e49
-/
lemma ENNReal.map_toReal_ae_eq_map_toReal_comap_ofReal {s : Set ℝ≥0∞} :
    ENNReal.toReal '' s =ᵐ[volume] NNReal.toReal '' (ENNReal.ofNNReal ⁻¹' s) := by
  by_cases h : ∞ ∈ s
  · rw [ENNReal.map_toReal_eq_map_toReal_comap_ofReal' h, union_singleton]
    apply insert_ae_eq_self
  rw [ENNReal.map_toReal_eq_map_toReal_comap_ofReal h]

/--
@isnad1 id=eq.1h1v.s5.8438ab08c41a from=translated src=- shape=278aa36e vocab=65ecf10f
-/
lemma ENNReal.volume_val {s : Set ℝ≥0∞} (hs : MeasurableSet s) :
    volume s = volume (ENNReal.toReal '' s) := by
  calc volume s
    _ = volume (ENNReal.ofNNReal ⁻¹' s) :=
      MeasureTheory.Measure.map_apply_of_aemeasurable (by fun_prop) hs
    _ = volume (NNReal.toReal '' (ENNReal.ofNNReal ⁻¹' s)) := NNReal.volume_val
    _ = volume (ENNReal.toReal '' s) := Eq.symm (measure_congr ENNReal.map_toReal_ae_eq_map_toReal_comap_ofReal)

instance : NullSingletonClass (@volume ℝ≥0∞ _) where
  measure_singleton := by
    intro x
    rw [ENNReal.volume_val (measurableSet_singleton _), image_singleton]
    simp

-- TODO: move this general result to an appropriate place
-- TODO: maybe generalize further to general measures restricted to a subtype
/--
@isnad1 id=nullsing.1h2v.s5.1a8331f2de90 from=translated src=- shape=deab02d2 vocab=cfad242e
-/
lemma Measure.Subtype.noAtoms {δ : Type*} [MeasureSpace δ] [NullSingletonClass (volume : Measure δ)]
    {p : δ → Prop} (hp : MeasurableSet p) :
    NullSingletonClass (Measure.Subtype.measureSpace.volume : Measure (Subtype p)) where
  measure_singleton := by
    intro x
    calc _
      _ = volume (Subtype.val '' {x}) := by
        apply comap_subtype_coe_apply hp volume
      _ = 0 := by
        simp

instance : NullSingletonClass (@volume ℝ≥0 _) := Measure.Subtype.noAtoms measurableSet_Ici

--TODO: move this general result to an appropriate place
--TODO: maybe generalize further to general measures restricted to a subtype
/--
@isnad1 id=sigmafin.1h2v.s5.e55fc6c09390 from=translated src=- shape=deab02d2 vocab=c32042a0
-/
lemma Measure.Subtype.sigmaFinite {δ : Type*} [MeasureSpace δ] [sf : SigmaFinite (@volume δ _)] {p : δ → Prop} (hp : MeasurableSet p) :
    SigmaFinite (Measure.Subtype.measureSpace.volume : Measure (Subtype p)) where
  out' := by
    refine Nonempty.intro ?_
    rw [sigmaFinite_iff] at sf
    rcases Classical.choice sf with ⟨set, set_mem, finite, spanning⟩
    set set' := fun n ↦ (Subtype.val ⁻¹' (set n))
    apply Measure.FiniteSpanningSetsIn.mk set'
    · simp
    · intro n
      calc _
        _ = volume (Subtype.val '' set' n) := by
          apply comap_subtype_coe_apply hp volume (set' n)
        _ ≤ volume (set n) := by
          apply measure_mono
          unfold set'
          exact image_preimage_subset Subtype.val (set n)
        _ < ⊤ := finite n
    · unfold set'
      rw [← preimage_iUnion]
      refine preimage_eq_univ_iff.mpr ?_
      rw [spanning]
      exact fun ⦃a⦄ a ↦ trivial

instance : SigmaFinite (@volume ℝ≥0 _) := Measure.Subtype.sigmaFinite measurableSet_Ici

--TODO: move?
/--
@isnad1 id=measurab.0h0v.s2.0c9622e3beca from=translated src=- shape=54c8eceb vocab=1d0743b4
-/
lemma measurableEmbedding_ofNNReal : MeasurableEmbedding ENNReal.ofNNReal := by
  apply MeasurableEmbedding.of_measurable_inverse (g := ENNReal.toNNReal)
    measurable_coe_nnreal_ennreal _ measurable_toNNReal
  · exact Function.RightInverse.leftInverse (congrFun rfl)
  · rw [range_coe']
    exact measurableSet_Iio

instance : SigmaFinite (@volume ℝ≥0∞ _) := measurableEmbedding_ofNNReal.sigmaFinite_map

/--
@isnad1 id=eq.1h1v.s5.e05ab702461e from=translated src=- shape=056c02be vocab=ebf33890
-/
lemma NNReal.volume_eq_volume_ennreal {s : Set ℝ≥0} (hs : MeasurableSet (ofNNReal '' s)) :
    volume s = volume (ENNReal.ofNNReal '' s) := by
  rw [ENNReal.volume_val hs, NNReal.volume_val]
  congr 1
  exact Eq.symm (image_image ENNReal.toReal ofNNReal s)

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.1h1v.s6.9c175fdd7ca2 from=translated src=- shape=68cd4398 vocab=fd0f9e99
-/
theorem NNReal.smul_map_volume_mul_left {a : ℝ≥0} (h : a ≠ 0) :
    a • Measure.map (a * ·) volume = volume := by
  ext s hs
  rw [NNReal.volume_val, ← Real.smul_map_volume_mul_left (a := a) (by simpa)]
  simp only [Measure.smul_apply, Measure.nnreal_smul_coe_apply, NNReal.abs_eq, ofReal_coe_nnreal,
    val_eq_coe, smul_eq_mul]
  congr 1
  rw [Measure.map_apply (by fun_prop) hs, Measure.map_apply (by fun_prop), NNReal.volume_val]
  rotate_left
  · exact (MeasurableEmbedding.subtype_coe measurableSet_Ici).measurableSet_image.mpr hs
  congr 1
  ext x
  simp only [val_eq_coe, mem_image, mem_preimage, Subtype.exists]
  simp_rw [← val_eq_coe, exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨hx, hax⟩
    apply Exists.intro
    · exact hax
    exact mul_nonneg (by simp) hx
  · rintro ⟨hx, hax⟩
    apply Exists.intro
    · exact hax
    rwa [mul_nonneg_iff_right_nonneg_of_pos] at hx
    simp only [val_eq_coe, coe_pos]
    exact h.pos

/--
@isnad1 id=eq.1h1v.s6.2389b91aa381 from=translated src=- shape=79ea0b1a vocab=19c02392
-/
theorem NNReal.map_volume_mul_left {a : ℝ≥0} (h : a ≠ 0) :
    Measure.map (a * ·) volume = a⁻¹ • volume := by
  conv_rhs =>
    rw [← NNReal.smul_map_volume_mul_left h,
      ← smul_assoc a⁻¹ a (Measure.map (fun x ↦ a * x) volume), smul_eq_mul, inv_mul_cancel₀ h]
  ext s hs
  simp

/--
@isnad1 id=eq.1h1v.s6.2b80ce1d0c0a from=translated src=- shape=d593f2c8 vocab=b864f8d7
-/
lemma ENNReal.volume_eq_volume_preimage {s : Set ℝ≥0∞} (hs : MeasurableSet s) :
    volume s = volume (ENNReal.ofReal ⁻¹' s ∩ Ici 0) := by
  rw [ENNReal.volume_val hs, measure_congr ENNReal.map_toReal_ae_eq_map_toReal_comap_ofReal]
  congr; ext x; simp only [mem_image, mem_preimage, mem_inter_iff, mem_Ici]
  constructor <;> intro h
  · obtain ⟨x', hx', rfl⟩ := h; simpa
  · lift x to ℝ≥0 using h.2; rw [ofReal_coe_nnreal] at h; use x, h.1

/--
@isnad1 id=eventual.0h0v.s5.1cae4c5a9e7c from=translated src=- shape=a48f1926 vocab=2e9c9287
-/
lemma Ioo_zero_top_ae_eq_univ : Ioo 0 ∞ =ᶠ[ae volume] Set.univ := by
    simp only [ae_eq_univ]
    rw [ENNReal.volume_val]
    · have : (Ioo 0 ⊤)ᶜ = {0, ∞} := by rw [@compl_def]; ext x; simp [pos_iff_ne_zero]; tauto
      rw [this]
      have : ENNReal.toReal '' {0, ⊤} = { 0 } := by simp [image]
      simp [this]
    · measurability

/--
@isnad1 id=eventual.0h0v.s5.eabe88fee762 from=translated src=- shape=55e5dd91 vocab=dff08b35
-/
lemma ae_in_Ioo_zero_top : ∀ᵐ x : ℝ≥0∞, x ∈ Ioo 0 ∞ := by
  filter_upwards [Ioo_zero_top_ae_eq_univ] with a ha
  simp only [eq_iff_iff] at ha; exact ha.mpr trivial

/--
@isnad1 id=eq.0h0v.s5.b8142b58d432 from=translated src=- shape=da3a405c vocab=e84f2d8c
-/
lemma map_restrict_Ioi_eq_restrict_Ioi :
    (volume.restrict (Ioi 0)).map ENNReal.ofReal = volume.restrict (Ioi 0) := by
  ext s hs
  rw [Measure.map_apply measurable_ofReal hs]
  simp only [measurableSet_Ioi, Measure.restrict_apply']
  rw [ENNReal.volume_eq_volume_preimage (by measurability)]
  congr 1
  ext x
  simp +contextual [LT.lt.le]

/--
@isnad1 id=eq.0h0v.s5.fd961572cb19 from=translated src=- shape=8c769b4c vocab=e84f2d8c
-/
lemma map_restrict_Ioi_eq_volume :
    (volume.restrict (Ioi 0)).map ENNReal.ofReal = volume := by
  refine Eq.trans map_restrict_Ioi_eq_restrict_Ioi ?_
  refine Measure.restrict_eq_self_of_ae_mem ?_
  filter_upwards [ae_in_Ioo_zero_top] with a ha using ha.1

--TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
/--
@isnad1 id=eq.0h1v.s4.56090284eb22 from=translated src=- shape=e778e200 vocab=6c77d9b1
-/
lemma NNReal.toReal_Iio_eq_Ico {b : ℝ≥0} :
    NNReal.toReal '' Set.Iio b = Set.Ico 0 b.toReal := by
  ext x
  simp only [mem_image, mem_Iio, mem_Ico]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← hyx]
    simpa
  · rintro hx
    use x.toNNReal, (Real.toNNReal_lt_iff_lt_coe hx.1).mpr hx.2
    simp [hx.1]

/--
@isnad1 id=eq.0h1v.s4.ad92c14c57c9 from=translated src=- shape=6930456a vocab=905655cc
-/
lemma NNReal.toReal_Ioi_eq_Ioi {b : ℝ≥0} :
    NNReal.toReal '' Set.Ioi b = Set.Ioi b.toReal := by
  ext x
  simp only [mem_image, mem_Ioi]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← hyx]
    simpa
  · rintro hx
    use x.toNNReal
    rw [Real.lt_toNNReal_iff_coe_lt]
    use hx
    simp only [Real.coe_toNNReal', sup_eq_left]
    exact (coe_nonneg b).trans hx.le

/--
@isnad1 id=eq.0h2v.s4.752dd4b52aa4 from=translated src=- shape=676b09d6 vocab=434d1a61
-/
lemma NNReal.toReal_Ioo_eq_Ioo {a b : ℝ≥0} :
    NNReal.toReal '' Set.Ioo a b = Set.Ioo a.toReal b.toReal := by
  ext x
  simp only [mem_image, mem_Ioo]
  refine ⟨fun ⟨y, hy, hyx⟩ ↦ ?_, fun h ↦ ?_⟩
  · rw [← hyx]
    simpa
  · have x_nonneg : 0 ≤ x := zero_le_coe.trans h.1.le
    refine ⟨x.toNNReal, ?_, Real.coe_toNNReal x (zero_le_coe.trans h.1.le)⟩
    rwa [Real.lt_toNNReal_iff_coe_lt, Real.toNNReal_lt_iff_lt_coe x_nonneg]

/--
@isnad1 id=eq.0h1v.s5.2ccc00294f9e from=translated src=- shape=9b77ed4e vocab=f26740db
-/
theorem NNReal.Ici_eq {a : ℝ≥0} :
  Ici (↑a) = (Real.toNNReal ⁻¹' Ici a ∩ Ici 0) := by
  ext x
  constructor
  · intro hx
    constructor
    · simp only [mem_preimage, mem_Ici]
      exact le_toNNReal_of_coe_le hx
    · apply zero_le_coe.trans hx
  · rintro ⟨hx1, hx2⟩
    simp only [mem_preimage, mem_Ici] at *
    rwa [← Real.le_toNNReal_iff_coe_le hx2]

/--
@isnad1 id=eq.0h1v.s5.a419bb359bbd from=translated src=- shape=fe1c1e7d vocab=8b8549f3
-/
lemma NNReal.volume_Iio {b : ℝ≥0} : volume (Set.Iio b) = b := by
  erw [volume_val, image_coe_Iio b, Real.volume_Ico, sub_zero, ofReal_coe_nnreal]

/--
@isnad1 id=eq.0h1v.s5.6547c678cfa1 from=translated src=- shape=6ff37786 vocab=633d25f3
-/
lemma NNReal.volume_Ioi {b : ℝ≥0} : volume (Set.Ioi b) = ⊤ := by
  erw [volume_val, image_coe_Ioi, Real.volume_Ioi]

/--
@isnad1 id=eq.0h2v.s5.57b68fb10155 from=translated src=- shape=fe5c1534 vocab=911cbd1c
-/
lemma NNReal.volume_Ioo {a b : ℝ≥0} : volume (Set.Ioo a b) = b - a:= by
  erw [volume_val, toReal_Ioo_eq_Ioo, Real.volume_Ioo, ofReal_sub (hq := by simp)]
  simp

-- TODO: the proofs in the following lemmas feel quite repetitive
-- extract helper lemma to re-use some of the argument!

-- TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
/--
@isnad1 id=eq.1h1v.s5.5e27b2d0eb49 from=translated src=- shape=45698cc9 vocab=a8e44165
-/
lemma ENNReal.toReal_Iio_eq_Ico {a : ℝ≥0∞} (ha : a ≠ ∞) :
    ENNReal.toReal '' Set.Iio a = Set.Ico 0 a.toReal := by
  ext x
  simp only [mem_image, mem_Iio, mem_Ico]
  constructor
  · rintro ⟨y, ⟨hy₁, hy₂⟩⟩
    rw [← hy₂]
    constructor
    · simp
    · exact (ENNReal.toReal_lt_toReal hy₁.ne_top ha).mpr hy₁
  · rintro ⟨zero_le_x, x_lt⟩
    use ENNReal.ofReal x
    constructor
    · exact (ENNReal.ofReal_lt_iff_lt_toReal zero_le_x ha).mpr x_lt
    · simpa

/--
@isnad1 id=eq.0h0v.s4.d7462a1bbb9d from=translated src=- shape=04e8b08b vocab=c9196651
-/
lemma ENNReal.toReal_Iio_top_eq_Ici :
    ENNReal.toReal '' Set.Iio ⊤ = Set.Ici 0 := by
  ext x
  simp only [mem_image, mem_Iio, mem_Ici]
  constructor
  · rintro ⟨y, ⟨hy₁, hy₂⟩⟩
    rw [← hy₂]
    simp
  · rintro zero_le_x
    use ENNReal.ofReal x
    simpa

-- TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
/--
@isnad1 id=eq.2h2v.s5.052b89a21881 from=translated src=- shape=b698bcae vocab=5a940294
-/
lemma ENNReal.toReal_Icc_eq_Icc {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    ENNReal.toReal '' Set.Icc a b = Set.Icc a.toReal b.toReal := by
  ext x
  simp only [mem_image, mem_Icc]
  constructor
  · rintro ⟨y, ⟨hy₁, hy₂⟩, hxy⟩
    rw [← hxy]
    constructor <;> gcongr
    · exact ne_top_of_le_ne_top hb hy₂
  · rintro hx
    use ENNReal.ofReal x
    constructor
    · rwa [le_ofReal_iff_toReal_le ha (le_trans toReal_nonneg hx.1), ofReal_le_iff_le_toReal hb]
    · rw [toReal_ofReal_eq_iff]
      exact (le_trans toReal_nonneg hx.1)

-- TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
/--
@isnad1 id=eq.2h2v.s5.e30cba1b5b50 from=translated src=- shape=b698bcae vocab=a1ecea98
-/
lemma ENNReal.toReal_Ioo_eq_Ioo {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) :
    ENNReal.toReal '' Set.Ioo a b = Set.Ioo a.toReal b.toReal := by
  ext x
  simp only [mem_image, mem_Ioo]
  constructor
  · rintro ⟨y, ⟨hy₁, hy₂⟩, hyx⟩
    rw [← hyx]
    constructor <;> gcongr
    · finiteness
  · rintro hx
    use ENNReal.ofReal x
    constructor
    · rwa [lt_ofReal_iff_toReal_lt ha, ofReal_lt_iff_lt_toReal (le_trans toReal_nonneg hx.1.le) hb]
    · rw [toReal_ofReal_eq_iff]
      exact (le_trans toReal_nonneg hx.1.le)

-- TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
/--
@isnad1 id=eq.1h1v.s4.176d63e14f75 from=translated src=- shape=b83ce3c6 vocab=c236c85c
-/
lemma ENNReal.toReal_Ioo_top_eq_Ioi {a : ℝ≥0∞} (ha : a ≠ ∞) :
    ENNReal.toReal '' Set.Ioo a ⊤ = Set.Ioi a.toReal := by
  ext x
  simp only [mem_image, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨y, ⟨hay, y_lt_top⟩, hyx⟩
    rwa [← hyx, toReal_lt_toReal ha y_lt_top.ne]
  · rintro hax
    use ENNReal.ofReal x
    refine ⟨⟨?_, by finiteness⟩, ?_⟩
    · rwa [lt_ofReal_iff_toReal_lt ha]
    · rw [toReal_ofReal_eq_iff]
      exact toReal_nonneg.trans hax.le

-- TODO: move somewhere else and add more lemmas for Ioo, Ico etc. ?
/--
@isnad1 id=eq.1h1v.s5.cc1700b54c9d from=translated src=- shape=37d4513a vocab=d028fcea
-/
lemma ENNReal.toReal_Ioi_eq_Ioi {a : ℝ≥0∞} (ha : a ≠ ∞) :
    ENNReal.toReal '' Set.Ioi a = Set.Ioi a.toReal ∪ {0} := by
  ext x
  simp only [mem_image, mem_Ioi, union_singleton, mem_insert_iff]
  constructor
  · rintro ⟨y, hy, hyx⟩
    by_cases h : y = ⊤
    · left
      rw [← hyx, h, ENNReal.toReal_top]
    right
    rw [← hyx]
    gcongr
  · rintro (x_zero | hxa)
    · exact ⟨⊤, by finiteness, by simp [x_zero]⟩
    use ENNReal.ofReal x
    simp only [toReal_ofReal_eq_iff]
    constructor
    · rwa [ENNReal.lt_ofReal_iff_toReal_lt ha]
    · exact (le_trans toReal_nonneg hxa.le)

/--
@isnad1 id=eq.0h2v.s6.f7575f880b04 from=translated src=- shape=80a381ef vocab=77f83cac
-/
lemma ENNReal.ofReal_Ioo_eq {a b : ℝ≥0∞} : ENNReal.ofReal ⁻¹' Set.Ioo a b
    = if a = ⊤ then ∅ else if a ≤ b ∧ b = ∞ then Set.Ioi a.toReal else Set.Ioo a.toReal b.toReal := by
  split_ifs with ha h
  · rw [ha]
    simp
  · rw [h.2]
    ext x
    simp only [mem_preimage, mem_Ioo, ofReal_lt_top, and_true, mem_Ioi]
    exact lt_ofReal_iff_toReal_lt ha
  · ext x
    simp only [mem_preimage, mem_Ioo]
    push Not at h
    by_cases hx : x < 0
    · rw [ENNReal.ofReal_of_nonpos hx.le]
      simp only [_root_.not_lt_zero, false_and, false_iff, not_and, not_lt]
      intro ha
      exfalso
      have := ha.trans hx
      have := @toReal_nonneg a
      linarith
    push Not at hx
    constructor
    · intro h'
      rw [← ofReal_lt_iff_lt_toReal hx (by aesop)]
      use toReal_lt_of_lt_ofReal h'.1, h'.2
    · intro h'
      rwa [lt_ofReal_iff_toReal_lt ha, ofReal_lt_iff_lt_toReal hx]
      aesop

/--
@isnad1 id=eq.0h1v.s6.ea4671d1eeda from=translated src=- shape=ebadc308 vocab=fa3d258e
-/
lemma ENNReal.ofReal_Iio_eq {b : ℝ≥0∞} : ENNReal.ofReal ⁻¹' Set.Iio b
    = if b = 0 then ∅ else if b = ∞ then Set.univ else Set.Iio b.toReal := by
  split_ifs with hb hb'
  · rw [hb]
    simp
  · rw [hb']
    simp only [preimage_eq_univ_iff]
    intro x hx
    simp only [mem_Iio]
    rcases hx with ⟨y, hy⟩
    rw [← hy]
    simp
  · ext x
    simp only [mem_preimage, mem_Iio]
    by_cases! hx : x < 0
    · rw [ENNReal.ofReal_of_nonpos hx.le]
      exact ⟨fun _ ↦ hx.trans_le (by positivity), fun _ ↦ by positivity⟩
    exact ofReal_lt_iff_lt_toReal hx hb'

/--
@isnad1 id=eq.0h1v.s5.1a93d8714e2a from=translated src=- shape=6e8009fb vocab=417eac43
-/
lemma ENNReal.toNNReal_Iio {b : ℝ≥0∞} : ENNReal.toNNReal '' Set.Iio b
    = if b = ∞ then Set.univ else Set.Iio b.toNNReal := by
  split_ifs with hb
  · rw [hb]
    ext x
    simp only [mem_image, mem_Iio, mem_univ, iff_true]
    use ofNNReal x
    simp
  · ext x
    simp only [mem_image, mem_Iio]
    constructor
    · rintro ⟨y, hyb, hyx⟩
      rwa [← hyx, ENNReal.toNNReal_lt_toNNReal _ hb]
      grind
    · intro h
      use ofNNReal x
      simp only [toNNReal_coe, and_true]
      rw [← ENNReal.toNNReal_lt_toNNReal (by simp) hb]
      simpa

/--
@isnad1 id=eq.1h1v.s5.261d6adddf72 from=translated src=- shape=886f54db vocab=b04cf019
-/
lemma ENNReal.volume_Ioi {a : ℝ≥0∞} (ha : a ≠ ∞) :
    volume (Set.Ioi a) = ⊤ := by
  rw [ENNReal.volume_val measurableSet_Ioi, ENNReal.toReal_Ioi_eq_Ioi ha, measure_union_eq_top_iff]
  left
  exact Real.volume_Ioi

-- TODO: move somewhere else?
/--
@isnad1 id=eq.0h1v.s4.b2b07dddd2b1 from=translated src=- shape=66f0c533 vocab=a298cdb3
-/
theorem ENNReal.Ioi_eq_Ioc_top {a : ℝ≥0∞} : Ioi a = Ioc a ⊤ := by
  unfold Ioi Ioc
  ext x
  simp

/--
@isnad1 id=eq.0h1v.s4.da1692b5c70f from=translated src=- shape=14933b08 vocab=ec73dfaf
-/
lemma ENNReal.volume_Iio {a : ℝ≥0∞} :
    volume (Set.Iio a) = a := by
  rw [ENNReal.volume_val measurableSet_Iio]
  by_cases ha : a = ⊤
  · rw [ha, ENNReal.toReal_Iio_top_eq_Ici, Real.volume_Ici]
  · rw [ENNReal.toReal_Iio_eq_Ico ha, Real.volume_Ico]
    simpa

/--
@isnad1 id=eq.0h0v.s4.0e32c332aacf from=translated src=- shape=e11efaef vocab=92659b60
-/
@[simp]
lemma ENNReal.range_toReal : range ENNReal.toReal = Ici 0 := by
  ext x
  simp only [mem_range, mem_Ici]
  constructor
  · rintro ⟨y, rfl⟩
    exact toReal_nonneg
  · intro hx
    use ENNReal.ofReal x
    simp only [toReal_ofReal_eq_iff]
    exact hx

/--
@isnad1 id=eq.0h0v.s4.ba73cc629f8b from=translated src=- shape=eeaf2933 vocab=bbaecc78
-/
@[simp]
lemma ENNReal.volume_univ : volume (univ : Set ℝ≥0∞) = ⊤ := by
  rw [ENNReal.volume_val MeasurableSet.univ, image_univ]
  simp

/--
@isnad1 id=eq.0h1v.s4.de9f701493d8 from=translated src=- shape=14933b08 vocab=923dc888
-/
@[simp]
lemma ENNReal.volume_Iic {a : ℝ≥0∞} :
    volume (Set.Iic a) = a := by
  rw [ENNReal.volume_val measurableSet_Iic]
  by_cases ha : a = ⊤
  · rw [ha]
    simp
  · rw [← Icc_bot, ENNReal.toReal_Icc_eq_Icc bot_ne_top ha, Real.volume_Icc]
    simpa

/--
@isnad1 id=eq.0h2v.s5.c9df612d820f from=translated src=- shape=4a0aa8f8 vocab=7ddeed85
-/
lemma ENNReal.volume_Ioo {a b : ℝ≥0∞} :
    volume (Set.Ioo a b) = b - a := by
  by_cases ha : a = ∞
  · rw [ha]
    simp
  rw [ENNReal.volume_val measurableSet_Ioo]
  by_cases hb : b = ⊤
  · have : ⊤ - ⊤ = (0 : ENNReal) := by simp only [tsub_self]
    rw [hb, ENNReal.top_sub ha, ENNReal.toReal_Ioo_top_eq_Ioi ha]
    apply Real.volume_Ioi
  rw [toReal_Ioo_eq_Ioo ha hb, Real.volume_Ioo, ofReal_sub _ (by simp), ofReal_toReal hb, ofReal_toReal ha]

instance : Measure.IsOpenPosMeasure (@volume ℝ≥0∞ _) where
  open_pos := by
    intro U open_U nonempty_U
    rcases open_U.exists_Ioo_subset nonempty_U with ⟨a, b, a_lt_b, Ioo_subset⟩
    rw [← ENNReal.bot_eq_zero, ← bot_lt_iff_ne_bot]
    apply lt_of_lt_of_le _ (measure_mono Ioo_subset)
    rw [ENNReal.volume_Ioo]
    simpa

instance : Measure.IsOpenPosMeasure (@volume ℝ≥0 _) where
  open_pos := by
    intro U open_U nonempty_U
    rcases open_U.exists_Ioo_subset nonempty_U with ⟨a, b, a_lt_b, Ioo_subset⟩
    rw [← ENNReal.bot_eq_zero, ← bot_lt_iff_ne_bot]
    apply lt_of_lt_of_le _ (measure_mono Ioo_subset)
    rw [NNReal.volume_Ioo]
    simpa

--TODO: prove analog of lemmas below for ℝ≥0

/--
@isnad1 id=le.2h2v.s6.ee1adaf53e80 from=translated src=- shape=ebf0ac1c vocab=11367fdb
-/
lemma ENNReal.volume_map_add_left_le_self {g : ℝ≥0∞} (hg : g ≠ ⊤) {s : Set ℝ≥0∞} (hs : MeasurableSet s) :
    Measure.map (g + ·) volume s ≤ volume s := by
  wlog hs' : ∞ ∉ s generalizing s
  · push Not at hs'
    have meas : MeasurableSet (s \ {∞}) := by measurability
    have := this meas (by simp)
    apply (this.trans' _).trans _
    · rw [Measure.map_apply (by measurability) (by measurability),
          Measure.map_apply (by measurability) (by measurability)]
      have : ((fun x ↦ g + x) ⁻¹' s) ⊆ ((fun x ↦ g + x) ⁻¹' (s \ {⊤})) ∪ {⊤} := by
        intro x
        simp only [mem_preimage, preimage_sdiff, union_singleton, mem_insert_iff, mem_sdiff,
          mem_singleton_iff, add_eq_top, not_or]
        intro a
        simp_all only [ne_eq, MeasurableSet.singleton, MeasurableSet.diff, mem_sdiff,
          mem_singleton_iff, not_true_eq_false, and_false, not_false_eq_true, true_and]
        exact eq_or_ne x ⊤
      apply (measure_mono this).trans
      apply (measure_union_le _ _).trans
      simp
    · rw [measure_sdiff_null (measure_singleton ⊤)]
  calc _
    _ ≤ volume ((fun x ↦ g.toReal + x) ⁻¹' (ENNReal.toReal '' s)) := by
      rw [Measure.map_apply (by measurability) hs]
      rw [ENNReal.volume_val (by measurability)]
      gcongr
      intro y
      simp only [mem_image, mem_preimage, forall_exists_index, and_imp]
      intro x hx hxy
      use g + x, hx
      rw [← hxy, toReal_add hg (by contrapose! hs'; rwa [hs', add_top] at hx)]
    _ ≤ (Measure.map (fun x ↦ g.toReal + x) volume) (ENNReal.toReal '' s) := by
      apply Measure.le_map_apply (by measurability)
    _ = volume s := by
      rw [map_add_left_eq_self (g := g.toReal) (μ := volume),
          ENNReal.volume_val hs]

/--
@isnad1 id=le.2h2v.s6.ad31aadad07f from=translated src=- shape=fb04f7f7 vocab=11367fdb
-/
lemma ENNReal.volume_map_add_right_le_self {g : ℝ≥0∞} (hg : g ≠ ⊤) {s : Set ℝ≥0∞} (hs : MeasurableSet s) :
    Measure.map (· + g) volume s ≤ volume s := by
  convert ENNReal.volume_map_add_left_le_self hg hs using 4
  apply add_comm

/--
@isnad1 id=eq.0h2v.s5.97194cc8151b from=translated src=- shape=4a0aa8f8 vocab=79be0751
-/
lemma ENNReal.volume_Ico {a b : ℝ≥0∞} :
    volume (Set.Ico a b) = b - a := by
  convert ENNReal.volume_Ioo using 1
  apply measure_congr
  symm
  exact Ioo_ae_eq_Ico

-- sanity check: this measure is what you expect
example : volume (Set.Icc (3 : ℝ≥0∞) 42) = 39 := by
  rw [volume_val measurableSet_Icc,
    toReal_Icc_eq_Icc (by finiteness) (by finiteness),
    toReal_ofNat, Real.volume_Icc, ofReal_eq_ofNat]
  norm_num

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h1v.s5.fe82174aa144 from=translated src=- shape=da1fa517 vocab=402685b3
-/
lemma lintegral_nnreal_eq_lintegral_Ici_ofReal {f : ℝ≥0 → ℝ≥0∞} : ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ici (0 : ℝ), f x.toNNReal := by
  change ∫⁻ (x : ℝ≥0), f x = ∫⁻ (x : ℝ) in Ici 0, (f ∘ Real.toNNReal) x
  rw [← lintegral_subtype_comap measurableSet_Ici]
  simp
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h2v.s5.a53df63f5403 from=translated src=- shape=0d488e76 vocab=0c7bb57d
-/
lemma lintegral_nnreal_Ici_eq_lintegral_Ici_ofReal {f : ℝ≥0 → ℝ≥0∞} {a : ℝ≥0} :
    ∫⁻ x in Ici a, f x = ∫⁻ x in Ici (a : ℝ), f x.toNNReal := by
  rw [← lintegral_indicator measurableSet_Ici, lintegral_nnreal_eq_lintegral_Ici_ofReal]
  simp_rw [← indicator_comp_right]
  rw [setLIntegral_indicator (MeasurableSet.preimage measurableSet_Ici measurable_real_toNNReal)]
  simp only [Function.comp_apply]
  apply setLIntegral_congr
  rw [NNReal.Ici_eq]

/--
@isnad1 id=eq.0h1v.s5.58e8137a7713 from=translated src=- shape=e7282ebc vocab=9d6223f6
-/
lemma lintegral_nnreal_eq_lintegral_Ioi_ofReal {f : ℝ≥0∞ → ℝ≥0∞} : ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ioi (0 : ℝ), f (.ofReal x) := by
  rw [lintegral_nnreal_eq_lintegral_Ici_ofReal]
  exact setLIntegral_congr Ioi_ae_eq_Ici.symm

/--
@isnad1 id=eq.0h1v.s5.36ca5db48d26 from=translated src=- shape=453cd520 vocab=47c225c1
-/
lemma lintegral_ennreal_eq_lintegral_of_nnreal {f : ℝ≥0∞ → ℝ≥0∞} :
    ∫⁻ x : ℝ≥0∞, f x = ∫⁻ x : ℝ≥0, f x := by
  refine (MeasurePreserving.lintegral_comp_emb ⟨by fun_prop, rfl⟩ ?_ f).symm
  refine isEmbedding_coe.measurableEmbedding ?_
  rw [range_coe']; exact measurableSet_Iio

/--
@isnad1 id=eq.1h2v.s5.879dfea6d6fd from=translated src=- shape=b951030a vocab=fa61d3f2
-/
lemma setLIntegral_ennreal_eq_setLintegral_of_nnreal {f : ℝ≥0∞ → ℝ≥0∞} {s : Set ℝ≥0∞} (hs : MeasurableSet s) :
    ∫⁻ x in s, f x = ∫⁻ x in (ofNNReal⁻¹' s), f x := by
  rw [← lintegral_indicator hs, lintegral_ennreal_eq_lintegral_of_nnreal]
  simp_rw [← Set.indicator_comp_right]
  rw [lintegral_indicator (by measurability)]
  rfl

/--
@isnad1 id=eq.0h1v.s5.62fdfb761a15 from=translated src=- shape=2f1456b9 vocab=f2f86d4a
-/
lemma lintegral_ennreal_eq_lintegral_Ioi_ofReal {f : ℝ≥0∞ → ℝ≥0∞} :
    ∫⁻ x : ℝ≥0∞, f x = ∫⁻ x in Ioi (0 : ℝ), f (.ofReal x) :=
  lintegral_ennreal_eq_lintegral_of_nnreal.trans lintegral_nnreal_eq_lintegral_Ioi_ofReal

-- TODO: are there better names?
/--
@isnad1 id=eq.0h1v.s5.a2a5431f3ea2 from=translated src=- shape=da1fa517 vocab=e176f448
-/
lemma lintegral_nnreal_eq_lintegral_toNNReal_Ioi (f : ℝ≥0 → ℝ≥0∞) :
    ∫⁻ x : ℝ≥0, f x = ∫⁻ x in Ioi (0 : ℝ), f x.toNNReal := by
  rw [lintegral_nnreal_eq_lintegral_Ici_ofReal]
  exact setLIntegral_congr Ioi_ae_eq_Ici.symm

-- TODO: do we actually use this?
/--
@isnad1 id=eq.0h1v.s5.b40209cbc741 from=translated src=- shape=f06535bf vocab=ba26f510
-/
lemma lintegral_nnreal_toReal_eq_lintegral_Ioi (f : ℝ → ℝ≥0∞) :
    ∫⁻ x : ℝ≥0, f (x.toReal) = ∫⁻ x in Ioi (0 : ℝ), f x := by
  rw [lintegral_nnreal_eq_lintegral_toNNReal_Ioi]
  refine setLIntegral_congr_fun_ae measurableSet_Ioi ?_
  filter_upwards with x hx
  have : max x 0 = x := max_eq_left_of_lt hx
  simp [this]

/--
@isnad1 id=eq.0h1v.s5.58c8faf2fedc from=translated src=- shape=f06535bf vocab=e291c0bf
-/
lemma lintegral_nnreal_toReal_eq_lintegral_Ici (f : ℝ → ℝ≥0∞) :
    ∫⁻ x : ℝ≥0, f (x.toReal) = ∫⁻ x in Ici (0 : ℝ), f x := by
  rw [lintegral_nnreal_toReal_eq_lintegral_Ioi]
  exact setLIntegral_congr Ioi_ae_eq_Ici

/--
@isnad1 id=eq.0h2v.s5.297fcf0936f6 from=translated src=- shape=52023c42 vocab=cd370e5e
-/
lemma setLIntegral_nnreal_Ici {f : ℝ≥0 → ℝ≥0∞} {a : ℝ≥0} :
    ∫⁻ (t : ℝ≥0) in Set.Ici a, f t = ∫⁻ (t : ℝ≥0), f (t + a) := by
  rw [lintegral_nnreal_eq_lintegral_Ici_ofReal, ← lintegral_shift' (a := -a)]
  simp only [preimage_add_const_Ici, sub_neg_eq_add, zero_add]
  rw [lintegral_nnreal_Ici_eq_lintegral_Ici_ofReal]
  apply setLIntegral_congr_fun measurableSet_Ici
  intro x hx
  simp only
  congr
  have : (a : ℝ).toNNReal = a := by exact Real.toNNReal_coe
  nth_rw 2 [← this]
  rw [← Real.toNNReal_add]
  · simp only [neg_add_cancel_right]
  · simpa
  · exact zero_le_coe

/--
@isnad1 id=eq.1h2v.s6.80f8a0be199b from=translated src=- shape=5ff795a3 vocab=796c57f7
-/
lemma lintegral_nnreal_scale_constant' {f : ℝ≥0 → ℝ≥0∞} {a : ℝ≥0} (h : a ≠ 0) :
    a * ∫⁻ x : ℝ≥0, f (a*x) = ∫⁻ x, f x := by
  rw [lintegral_nnreal_eq_lintegral_toNNReal_Ioi, lintegral_nnreal_eq_lintegral_toNNReal_Ioi]
  symm
  rw [← lintegral_scale_constant_halfspace' (a:=a) (by rw [NNReal.coe_pos, pos_iff_ne_zero]; exact h)]
  congr 1
  · simp
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  congr
  rw [Real.toNNReal_mul (by simp)]
  simp

-- TODO: lemmas about interaction with the Bochner integral
