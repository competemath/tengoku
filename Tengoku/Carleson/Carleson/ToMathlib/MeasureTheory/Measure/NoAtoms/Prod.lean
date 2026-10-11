/-
Copyright (c) 2026 Leo Diedering. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leo Diedering
-/
module

public import Tengoku.Carleson.Carleson.ToMathlib.MeasureTheory.Measure.NoAtoms.Defs
public import Tengoku

-- Upstreaming status: Needs significant clean-up (refactoring, code style, extracting lemmas,
-- moving to proper location etc.)

public section

namespace MeasureTheory

open Set Measure Filter TopologicalSpace Function

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- For a `(s : Set (α × β))` and `(ν : Measure β)`, we define `essProjFst` such that
`x ∈ essProjFst s ν` iff `0 < ν {y | ⟨x, y⟩ ∈ s}`. -/
def essProjFst (s : Set (α × β)) (ν : Measure β) := {x | 0 < ν ((fun y => (x, y)) ⁻¹' s)}

/-- For a `(s : Set (α × β))` and `(μ : Measure α)`, we define `essProjSnd` such that
`y ∈ essProjSnd s μ` iff `0 < μ {x | ⟨x, y⟩ ∈ s}`. -/
def essProjSnd (s : Set (α × β)) (μ : Measure α) := {y | 0 < μ ((fun x => (x, y)) ⁻¹' s)}

variable {μ : Measure α} {ν : Measure β}

/--
@isnad1 id=eq.0h5v.s5.a45a9c758961 from=translated src=- shape=01a5f18e vocab=3cbca17d
-/
theorem essProjSnd_eq_essProjFst_swap {s : Set (α × β)} :
    essProjSnd s μ = essProjFst (Prod.swap ⁻¹' s) μ := by
  unfold essProjFst essProjSnd
  ext y
  simp only [mem_ofPred_eq]
  congr!

/--
@isnad1 id=le.0h5v.s5.e02b3af4725f from=translated src=- shape=35a9ef40 vocab=b5336507
-/
theorem essProjFst_subset {s : Set (α × β)} :
    essProjFst s ν ⊆ Prod.fst '' s := by
  unfold essProjFst
  intro x
  contrapose!
  simp only [mem_image, Prod.exists, exists_and_right, exists_eq_right, not_exists, mem_ofPred_eq,
    not_lt, nonpos_iff_eq_zero]
  intro h
  convert measure_empty (μ := ν)
  aesop

/--
@isnad1 id=le.0h5v.s5.2fd259efa2a2 from=translated src=- shape=d9c45124 vocab=fb57f823
-/
theorem essProjSnd_subset {s : Set (α × β)} :
    essProjSnd s μ ⊆ Prod.snd '' s := by
  rw [essProjSnd_eq_essProjFst_swap]
  apply essProjFst_subset.trans_eq
  aesop

/--
@isnad1 id=eq.0h5v.s6.c7302c7fbf77 from=translated src=- shape=350d6407 vocab=6595fe3c
-/
theorem essProjFst_eq {s : Set (α × β)} :
    essProjFst s ν = (fun x => ν ((fun y => (x, y)) ⁻¹' s)) ⁻¹' (Set.Ioi 0) := by
  unfold essProjFst
  ext b
  simp

/--
@isnad1 id=eq.0h5v.s6.3dccb30a6706 from=translated src=- shape=4fa187f1 vocab=39f5a9db
-/
theorem essProjSnd_eq {s : Set (α × β)} :
    essProjSnd s μ = (fun y => μ ((fun x => (x, y)) ⁻¹' s)) ⁻¹' (Set.Ioi 0) := by
  rw [essProjSnd_eq_essProjFst_swap, essProjFst_eq]
  congr with y

/--
@isnad1 id=eq.0h5v.s5.5573116a99a6 from=translated src=- shape=16efbf63 vocab=f36773e0
-/
theorem essProjFst_eq' {s : Set (α × β)} :
    essProjFst s ν = support (fun x => ν ((fun y => (x, y)) ⁻¹' s)) := by
  rw [essProjFst_eq]
  ext b
  simp only [mem_preimage, mem_Ioi, mem_support, ne_eq, pos_iff_ne_zero]

/--
@isnad1 id=eq.0h5v.s5.185b9b7bc63c from=translated src=- shape=ba9c590c vocab=ee286ebe
-/
theorem essProjSnd_eq' {s : Set (α × β)} :
    essProjSnd s μ = support (fun y => μ ((fun x => (x, y)) ⁻¹' s)) := by
  rw [essProjSnd_eq_essProjFst_swap, essProjFst_eq']
  congr with y

/--
@isnad1 id=eq.1h5v.s5.d74835f63c37 from=translated src=- shape=69d7180f vocab=a2e5e5a6
-/
@[simp]
theorem essProjFst_times_univ {s : Set α} (h : ν ≠ 0) :
    essProjFst (s ×ˢ univ) ν = s := by
  unfold essProjFst
  ext y
  simp only [mem_ofPred_eq]
  constructor
  · contrapose!
    intro hy
    simp only [nonpos_iff_eq_zero]
    convert measure_empty (μ := ν)
    aesop
  · intro hy
    convert measure_univ_pos.mpr h
    aesop

/--
@isnad1 id=eq.1h5v.s5.623f2c5b3bd9 from=translated src=- shape=2358e2e6 vocab=0decc9ea
-/
@[simp]
theorem essProjSnd_univ_times {s : Set β} (h : μ ≠ 0) :
    essProjSnd (univ ×ˢ s) μ = s := by
  rw [essProjSnd_eq_essProjFst_swap, preimage_swap_prod, essProjFst_times_univ h]

/--
@isnad1 id=le.1h6v.s5.f63fc940955b from=translated src=- shape=c53416be vocab=8e16c492
-/
@[gcongr]
theorem essProjFst_mono {s t : Set (α × β)} (h : s ⊆ t) :
    essProjFst s ν ⊆ essProjFst t ν := by
  unfold essProjFst
  intro x hx
  simp_all only [mem_ofPred_eq]
  apply hx.trans_le
  gcongr

/--
@isnad1 id=le.1h6v.s5.7afd66aba4e0 from=translated src=- shape=3c5eacd2 vocab=71882eb2
-/
@[gcongr]
theorem essProjSnd_mono {s t : Set (α × β)} (h : s ⊆ t) :
    essProjSnd s μ ⊆ essProjSnd t μ := by
  rw [essProjSnd_eq_essProjFst_swap, essProjSnd_eq_essProjFst_swap]
  exact essProjFst_mono (preimage_mono h)

/-
theorem essProjFst_essProjFst {s : Set (α × β)} {q : Set β} :
    essProjFst (s ∩ univ ×ˢ (essProjFst s ν)) ν = essProjFst s ν := by
  sorry

theorem essProjFst_inter {s t : Set (α × β)} {ν : Measure α} :
    essProjFst (s ∩ t) ν ⊆ essProjFst s ν ∩ essProjFst t ν := by
  intro b
  unfold essProjFst
  simp only [preimage_inter, mem_ofPred_eq, mem_inter_iff]
  sorry
-/

/--
@isnad1 id=eq.0h6v.s6.7d681401e0ef from=translated src=- shape=70be7785 vocab=4d284f32
-/
theorem essProjFst_inter_times_univ {s : Set (α × β)} {t : Set α} :
    essProjFst (s ∩ t ×ˢ univ) ν = essProjFst s ν ∩ t := by
  unfold essProjFst
  ext y
  simp only [preimage_inter, mem_ofPred_eq, mem_inter_iff]
  constructor
  · intro hy
    constructor
    · apply hy.trans_le
      apply measure_mono Set.inter_subset_left
    · contrapose! hy
      simp only [nonpos_iff_eq_zero]
      convert measure_empty (μ := ν)
      simp_all only [not_false_eq_true, mk_preimage_prod_right_eq_empty, inter_empty]
  · intro ⟨hy, hyt⟩
    convert hy
    aesop

/--
@isnad1 id=eq.0h6v.s6.8c174ebddca4 from=translated src=- shape=bb9e9025 vocab=5c488489
-/
theorem essProjSnd_inter_univ_times {s : Set (α × β)} {t : Set β} :
    essProjSnd (s ∩ univ ×ˢ t) μ = essProjSnd s μ ∩ t := by
  rw [essProjSnd_eq_essProjFst_swap, essProjSnd_eq_essProjFst_swap, preimage_inter,
    preimage_swap_prod, essProjFst_inter_times_univ]

/--
@isnad1 id=measurab.1h6v.s5.92b6c8acf98d from=translated src=- shape=1cf9a32f vocab=4a24cc26
-/
theorem measurableSet_essProjFst [SFinite ν] {s : Set (α × β)} (hs : MeasurableSet s) :
    MeasurableSet (essProjFst s ν) := by
  rw [essProjFst_eq]
  exact measurable_measure_prodMk_left hs measurableSet_Ioi

/--
@isnad1 id=measurab.1h6v.s5.2bccc4520f07 from=translated src=- shape=c90f141c vocab=1bf07a01
-/
theorem measurableSet_essProjSnd [SFinite μ] {s : Set (α × β)} (hs : MeasurableSet s) :
    MeasurableSet (essProjSnd s μ) := by
  rw [essProjSnd_eq_essProjFst_swap]
  apply measurableSet_essProjFst (measurableSet_swap_iff.mpr hs)

/--
@isnad1 id=iff.1h7v.s6.8370720aa932 from=translated src=- shape=0a70b999 vocab=42609332
-/
theorem measure_essProjFst_pos_iff [SFinite ν] {s : Set (α × β)} (hs : MeasurableSet s) :
    0 < μ (essProjFst s ν) ↔ 0 < (μ.prod ν) s := by
  rw [Measure.prod_apply hs, lintegral_pos_iff_support (measurable_measure_prodMk_left hs),
      ← essProjFst_eq']

/--
@isnad1 id=iff.1h7v.s7.ea60a1b2b341 from=translated src=- shape=571561c1 vocab=117546e9
-/
theorem measure_essProjSnd_pos_iff [SFinite μ] [SFinite ν] {s : Set (α × β)} (hs : MeasurableSet s) :
    0 < ν (essProjSnd s μ) ↔ 0 < (μ.prod ν) s := by
  rw [Measure.prod_apply_symm hs, lintegral_pos_iff_support (measurable_measure_prodMk_right hs),
      ← essProjSnd_eq']

/--
@isnad1 id=ex.2h7v.s7.4a2321819bbc from=translated src=- shape=461f69f0 vocab=28c3d7f8
-/
theorem exists_subset_measure_fst_image_lt_top [SigmaFinite μ] [SFinite ν] {s : Set (α × β)}
  (hs : MeasurableSet s) (h : 0 < μ.prod ν s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ.prod ν t ∧ μ (Prod.fst '' t) < ⊤ := by
  set r := essProjFst s ν
  have hμr : 0 < μ r := by
    rwa [measure_essProjFst_pos_iff hs]
  rcases exists_subset_measure_lt_top (measurableSet_essProjFst hs) hμr with
    ⟨q, meas_q, hqr, hμq, hμq_top⟩
  have meas := hs.inter (meas_q.prod MeasurableSet.univ)
  use s ∩ q ×ˢ univ, inter_subset_left, meas
  have hq : essProjFst (s ∩ q ×ˢ univ) ν = q := by
    rw [essProjFst_inter_times_univ, inter_eq_right]
    exact hqr
  have : Prod.fst '' (s ∩ q ×ˢ univ) = q := by
    apply subset_antisymm
    · exact (image_mono inter_subset_right).trans (fst_image_prod_subset _ _)
    · nth_rw 1 [← hq]
      apply essProjFst_subset
  rw [this]
  constructor
  · rw [Measure.prod_apply meas, lintegral_pos_iff_support (measurable_measure_prodMk_left meas)]
    convert hμq
    rw [← essProjFst_eq', hq]
  · exact hμq_top

/--
@isnad1 id=ex.2h7v.s7.8966bb0196f4 from=translated src=- shape=5e1349e0 vocab=cd3c7816
-/
theorem exists_subset_measure_snd_image_lt_top [SFinite μ] [SigmaFinite ν] {s : Set (α × β)}
  (hs : MeasurableSet s) (h : 0 < μ.prod ν s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ.prod ν t ∧ ν (Prod.snd '' t) < ⊤ := by
  rw [← prod_swap, map_apply measurable_swap hs] at h
  rcases exists_subset_measure_fst_image_lt_top (measurableSet_swap_iff.mpr hs) h with
    ⟨t', ht's, meas_t', ht', ht'_top⟩
  rw [← image_subset_iff, image_swap_eq_preimage_swap] at ht's
  rw [← prod_swap, map_apply measurable_swap meas_t'] at ht'
  use Prod.swap ⁻¹' t', ht's, (measurableSet_swap_iff.mpr meas_t'), ht'
  convert ht'_top
  aesop

/--
@isnad1 id=ex.2h7v.s7.2172003ef7af from=translated src=- shape=318259bb vocab=baf101c0
-/
theorem exists_subset_measure_essProjFst_lt [NoAtoms' μ] [SFinite ν] {s : Set (α × β)}
  (hs : MeasurableSet s) (h : 0 < μ.prod ν s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ.prod ν t ∧ μ (essProjFst t ν) < μ (essProjFst s ν) := by
  set r := essProjFst s ν
  have hμr : 0 < μ r := by
    rwa [measure_essProjFst_pos_iff hs]
  rcases NoAtoms'.exists_measurable_subset_lt (measurableSet_essProjFst hs) hμr with
    ⟨q, hqr, meas_q, hμq, hμqr⟩
  have meas := hs.inter (meas_q.prod MeasurableSet.univ)
  use s ∩ q ×ˢ univ, inter_subset_left, meas
  have : essProjFst (s ∩ q ×ˢ univ) ν = q := by
    rw [essProjFst_inter_times_univ, inter_eq_right]
    exact hqr
  rw [this]
  constructor
  · rw [Measure.prod_apply meas, lintegral_pos_iff_support (measurable_measure_prodMk_left meas)]
    convert hμq
    rw [← essProjFst_eq', this]
  · exact hμqr

/--
@isnad1 id=ex.2h7v.s7.cd4bb2e321f1 from=translated src=- shape=9d53d642 vocab=1af8a2e1
-/
theorem exists_subset_measure_essProjSnd_lt [SFinite μ] [SFinite ν] [NoAtoms' ν]
  {s : Set (α × β)} (hs : MeasurableSet s) (h : 0 < μ.prod ν s) :
    ∃ t ⊆ s, MeasurableSet t ∧ 0 < μ.prod ν t ∧ ν (essProjSnd t μ) < ν (essProjSnd s μ) := by
  rw [← prod_swap, map_apply measurable_swap hs] at h
  rcases exists_subset_measure_essProjFst_lt (measurableSet_swap_iff.mpr hs) h with
    ⟨t', ht's, meas_t', ht', ht'_top⟩
  rw [← image_subset_iff, image_swap_eq_preimage_swap] at ht's
  rw [← prod_swap, map_apply measurable_swap meas_t'] at ht'
  use Prod.swap ⁻¹' t', ht's, (measurableSet_swap_iff.mpr meas_t'), ht'
  rwa [essProjSnd_eq_essProjFst_swap, ← image_swap_eq_preimage_swap,
    image_preimage_eq _ Prod.swap_surjective]

open ENNReal

--TODO: move
/--
@isnad1 id=lt.7h6v.s7.f2ec355299f4 from=translated src=- shape=f4cfc2ac vocab=38ab9c1d
-/
theorem setLIntegral_strict_mono_set {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
  {f : α → ℝ≥0∞} {s t : Set α} (hf : Measurable f) (hsm : MeasurableSet s) (htm : MeasurableSet t)
  (htsf : t \ s ⊆ support f) (hfi : ∫⁻ (x : α) in s, f x ∂μ ≠ ∞) (hst : s ⊆ t) (h : μ s < μ t) :
    ∫⁻ (x : α) in s, f x ∂μ < ∫⁻ (x : α) in t, f x ∂μ := by
  have : 0 < ∫⁻ (x : α) in t \ s, f x ∂μ := by
    rwa [lintegral_pos_iff_support hf, Measure.restrict_apply (measurableSet_support hf),
      inter_eq_right.mpr htsf, measure_sdiff hst hsm.nullMeasurableSet h.ne_top, tsub_pos_iff_lt]
  calc _
    _ < ∫⁻ (x : α) in s, f x ∂μ + ∫⁻ (x : α) in (t \ s), f x ∂μ := by
      apply lt_add_right hfi this.ne'
    _ = ∫⁻ (x : α) in t, f x ∂μ := by
      rw [← lintegral_union (htm.diff hsm) disjoint_sdiff_right, union_sdiff_cancel hst]

/--
@isnad1 id=noatoms.0h6v.s5.5616210497c0 from=translated src=- shape=4aa2f223 vocab=c30d9728
-/
instance prod.instNoAtoms_fst [NoAtoms' μ] [SFinite μ] [SigmaFinite ν] :
    NoAtoms' (μ.prod ν) := by
  rw [no_atoms_iff]
  intro s meas_s hs
  rcases exists_subset_measure_snd_image_lt_top meas_s hs with ⟨s', hs's, meas_s', hs', hs'_top⟩
  rcases exists_subset_measure_essProjFst_lt meas_s' hs' with ⟨t, hts', meas_t, ht, ht_lt⟩
  have hts : t ⊆ s := hts'.trans hs's
  use t, hts, meas_t, ht
  rw [Measure.prod_apply meas_t, Measure.prod_apply meas_s,
    ← setLIntegral_eq_of_support_subset subset_rfl, ← essProjFst_eq']
  nth_rw 2 [← setLIntegral_eq_of_support_subset subset_rfl]
  rw [← essProjFst_eq']
  have : ∫⁻ (x : α) in essProjFst t ν, ν (Prod.mk x ⁻¹' s') ∂μ
    < ∫⁻ (x : α) in essProjFst s' ν, ν (Prod.mk x ⁻¹' s') ∂μ := by
    apply setLIntegral_strict_mono_set (measurable_measure_prodMk_left meas_s')
      (measurableSet_essProjFst meas_t) (measurableSet_essProjFst meas_s') _ _ _ ht_lt
    · rw [← essProjFst_eq']
      exact sdiff_subset
    · rw [← lt_top_iff_ne_top]
      calc _
        _ ≤ ∫⁻ (x : α) in essProjFst t ν, ν (Prod.snd '' s') ∂μ := by
          gcongr
          intro y
          aesop
        _ = ν (Prod.snd '' s') * μ (essProjFst t ν) := setLIntegral_const _ _
        _ < ∞ := mul_lt_top hs'_top ht_lt.lt_top
    · gcongr
  calc _
    _ ≤ ∫⁻ (x : α) in essProjFst t ν, ν (Prod.mk x ⁻¹' s') ∂μ := by
      gcongr
    _ < ∫⁻ (x : α) in essProjFst s' ν, ν (Prod.mk x ⁻¹' s') ∂μ := this
    _ ≤ ∫⁻ (x : α) in essProjFst s ν, ν (Prod.mk x ⁻¹' s) ∂μ := by
      gcongr

--TODO: move?
/--
@isnad1 id=iff.1h7v.s6.2fc806a6096b from=translated src=- shape=68902bc1 vocab=ff0e3bc2
-/
theorem isAtom_swap_iff [SFinite μ] [SFinite ν] {s : Set (α × β)} (hs : MeasurableSet s) :
    IsAtom (Prod.swap ⁻¹' s) (ν.prod μ) ↔ IsAtom s (μ.prod ν) := by
  unfold IsAtom
  rw [← map_apply measurable_swap hs, prod_swap]
  simp only [and_congr_right_iff]
  intro h
  constructor
  · intro h' t hts meas_t
    have := h' (Prod.swap ⁻¹' t)
    rw [preimage_subset_preimage_iff (subset_range_of_surjective Prod.swap_surjective _),
      measurableSet_swap_iff, ← map_apply measurable_swap meas_t, prod_swap] at this
    exact this hts meas_t
  · intro h' t hts meas_t
    have := h' (Prod.swap ⁻¹' t)
    nth_rw 1 [← image_swap_eq_preimage_swap, image_subset_iff] at this
    rw [measurableSet_swap_iff,
      ← map_apply measurable_swap meas_t, prod_swap] at this
    exact this hts meas_t

/--
@isnad1 id=noatoms.0h6v.s5.9bf2fb7b05d5 from=translated src=- shape=76395be6 vocab=c30d9728
-/
instance prod.instNoAtoms_snd [SigmaFinite μ] [NoAtoms' ν] [SFinite ν] :
    NoAtoms' (μ.prod ν) where
  no_atoms := by
    intro s hs
    rw [← isAtom_swap_iff hs]
    apply no_atoms
    rwa [measurableSet_swap_iff]

end MeasureTheory
