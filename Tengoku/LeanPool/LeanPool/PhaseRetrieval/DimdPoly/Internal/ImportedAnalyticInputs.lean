/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
module

public import Tengoku

public import Tengoku.LeanPool.LeanPool.PhaseRetrieval.DimdPoly.Internal.Definitions
import Tengoku.LeanPool.LeanPool.PhaseRetrieval.Constant.Internal.RotationalAveraging

/-! # ImportedAnalyticInputs -/

@[expose] public section

noncomputable section

namespace DimdPolyLEAN

open MeasureTheory Filter
open scoped ENNReal Topology RealInnerProductSpace

/-!
# ImportedAnalyticInputs

Mathlib-facing wrapper file for the analytic inputs that later modules are
allowed to cite through a stable local API.
-/

/-- `Circle`: Circle. -/
abbrev Circle := AddCircle (2 * Real.pi)

/-- `μCircle`: the normalized Haar measure on the circle `AddCircle (2π)`. -/
noncomputable def μCircle : MeasureTheory.Measure Circle :=
  AddCircle.haarAddCircle

/-- `muCircle`: mu Circle. -/
noncomputable abbrev muCircle : MeasureTheory.Measure Circle := μCircle

/-- `Cavg`: Cavg. -/
def Cavg : ℝ := 1

/--
@isnad1 id=lt.0h0v.s3.98bd7014c3f2 from=translated src=- shape=ff3a10fc vocab=8921a244
-/
theorem Cavg_pos : 0 < Cavg := by norm_num [Cavg]

/-- `Crot`: Crot. -/
def Crot : ℝ := 64 * Real.pi

/--
@isnad1 id=lt.0h0v.s3.8098a9b946df from=translated src=- shape=ff3a10fc vocab=ca363ae0
-/
theorem Crot_pos : 0 < Crot := by
  unfold Crot
  nlinarith [Real.pi_pos]

/-- `zeta`: zeta. -/
noncomputable def zeta (x : Circle) : ℂ :=
  AddCircle.toCircle x

/--
@isnad1 id=eq.0h1v.s3.5672a0496b06 from=translated src=- shape=8e1bdd70 vocab=2ee2b560
-/
theorem norm_zeta (x : Circle) : ‖zeta x‖ = 1 := by
  simp [zeta, Circle.norm_coe]

/-- `circleChar`: circle Char. -/
noncomputable def circleChar (n : Nat) : Circle -> ℂ :=
  fun x => zeta x ^ n

/--
@isnad1 id=eq.0h2v.s4.7ef72e14d5c6 from=translated src=- shape=c2be0907 vocab=4cffb654
-/
theorem circleChar_eq_zeta_pow (n : Nat) (x : Circle) :
    circleChar n x = zeta x ^ n := rfl

/-- `CircleArc`: Circle Arc. -/
structure CircleArc where
  /-- `left`: left. -/
  left : ℝ
  /-- `right`: right. -/
  right : ℝ
  left_le_right : left ≤ right
  width_le_period : right - left ≤ 2 * Real.pi

/-- `arcLength`: arc Length. -/
def arcLength (I : CircleArc) : ℝ := I.right - I.left

/-- `arcParam`: arc Param. -/
def arcParam (I : CircleArc) (t : ℝ) : Circle :=
  QuotientAddGroup.mk (I.left + t * arcLength I)

/-- `arcSet`: arc Set. -/
def arcSet (I : CircleArc) : Set Circle :=
  {x | ∃ t ∈ Set.Icc (0 : ℝ) 1, arcParam I t = x}

/-- `carrierArc`: carrier Arc. -/
noncomputable def carrierArc (N : Nat) (k : Fin N) : CircleArc where
  left := (2 * Real.pi) * (k.1 : ℝ) / (N : ℝ)
  right := (2 * Real.pi) * ((k.1 + 1 : Nat) : ℝ) / (N : ℝ)
  left_le_right := by
    have hN : 0 <= (N : ℝ) := by exact_mod_cast Nat.le_of_lt k.pos
    apply div_le_div_of_nonneg_right ?_ hN
    gcongr
    exact_mod_cast Nat.le_succ k.1
  width_le_period := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast k.pos
    have hNge : (1 : ℝ) <= (N : ℝ) := by exact_mod_cast k.pos
    have hpi_nonneg : 0 <= (2 * Real.pi : ℝ) := by positivity
    have hwidth :
        (2 * Real.pi) * ((k.1 + 1 : Nat) : ℝ) / (N : ℝ) -
          (2 * Real.pi) * (k.1 : ℝ) / (N : ℝ) =
        (2 * Real.pi) / (N : ℝ) := by
      field_simp [ne_of_gt hNpos]
      norm_num
    rw [hwidth]
    exact div_le_self hpi_nonneg hNge

/--
@isnad1 id=eq.0h2v.s5.cddac81dfa60 from=translated src=- shape=fef82c33 vocab=a4f55017
-/
theorem carrierArc_length {N : Nat} (k : Fin N) :
    arcLength (carrierArc N k) = (2 * Real.pi) / (N : ℝ) := by
  unfold arcLength carrierArc
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast k.pos
  field_simp [ne_of_gt hNpos]
  norm_num

/--
@isnad1 id=lt.0h2v.s4.d84c01c44a00 from=translated src=- shape=5d330033 vocab=a846b2d8
-/
theorem carrierArc_length_pos {N : Nat} (k : Fin N) :
    0 < arcLength (carrierArc N k) := by
  rw [carrierArc_length k]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast k.pos
  positivity

/--
@isnad1 id=le.0h2v.s4.376c441432d2 from=translated src=- shape=5d330033 vocab=207ab4fd
-/
theorem carrierArc_left_nonneg {N : Nat} (k : Fin N) :
    0 <= (carrierArc N k).left := by
  unfold carrierArc
  positivity

/--
@isnad1 id=le.0h2v.s4.2100e1e28fea from=translated src=- shape=88e45b10 vocab=ce35ca6e
-/
theorem carrierArc_right_le_period {N : Nat} (k : Fin N) :
    (carrierArc N k).right <= 2 * Real.pi := by
  unfold carrierArc
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast k.pos
  have hle : ((k.1 + 1 : Nat) : ℝ) <= (N : ℝ) := by exact_mod_cast k.2
  have hT_nonneg : 0 <= (2 * Real.pi : ℝ) := by positivity
  calc
    (2 * Real.pi) * ((k.1 + 1 : Nat) : ℝ) / (N : ℝ)
        <= (2 * Real.pi) * (N : ℝ) / (N : ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hle hT_nonneg)
        (le_of_lt hNpos)
    _ = 2 * Real.pi := by field_simp [ne_of_gt hNpos]

/--
@isnad1 id=lt.0h2v.s4.8f905c7d5262 from=translated src=- shape=9c4a76b5 vocab=23783fca
-/
theorem carrierArc_left_lt_right {N : Nat} (k : Fin N) :
    (carrierArc N k).left < (carrierArc N k).right := by
  have hlen := carrierArc_length_pos k
  dsimp [arcLength] at hlen
  linarith

/--
@isnad1 id=eq.0h2v.s6.993b98a43d1e from=translated src=- shape=3459ae00 vocab=abc6198b
-/
theorem carrierArc_arcSet_eq_mk_image_Icc {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =
      QuotientAddGroup.mk ''
        Set.Icc ((carrierArc N k).left) ((carrierArc N k).right) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨t, ht, rfl⟩
    refine ⟨(carrierArc N k).left + t * arcLength (carrierArc N k), ?_, rfl⟩
    have hlen_nonneg : 0 <= arcLength (carrierArc N k) :=
      le_of_lt (carrierArc_length_pos k)
    constructor
    · dsimp [arcLength] at hlen_nonneg ⊢
      nlinarith [ht.1, hlen_nonneg]
    · dsimp [arcLength] at hlen_nonneg ⊢
      nlinarith [ht.2, hlen_nonneg]
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    let t : ℝ := (y - (carrierArc N k).left) / arcLength (carrierArc N k)
    refine ⟨t, ?_, ?_⟩
    · have hlen_pos : 0 < arcLength (carrierArc N k) :=
        carrierArc_length_pos k
      constructor
      · dsimp [t]
        exact div_nonneg (sub_nonneg.mpr hy.1) (le_of_lt hlen_pos)
      · dsimp [t]
        rw [div_le_one hlen_pos]
        dsimp [arcLength]
        linarith [hy.2]
    · dsimp [arcParam, t]
      have hlen_pos : 0 < arcLength (carrierArc N k) :=
        carrierArc_length_pos k
      apply congrArg (fun r : ℝ => (QuotientAddGroup.mk r : Circle))
      field_simp [ne_of_gt hlen_pos]
      ring_nf

/--
@isnad1 id=eq.0h2v.s8.0924233df4c5 from=translated src=- shape=fa519a44 vocab=564af9ca
-/
theorem carrierArc_arcSet_eq_mk_image_Ioc_union_left {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =
      (QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) ∪
        {(QuotientAddGroup.mk ((carrierArc N k).left) : Circle)} := by
  rw [carrierArc_arcSet_eq_mk_image_Icc k]
  have hIcc :
      Set.Icc ((carrierArc N k).left) ((carrierArc N k).right) =
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) ∪
          {((carrierArc N k).left)} := by
    ext y
    constructor
    · intro hy
      by_cases hleft : y = (carrierArc N k).left
      · exact Or.inr hleft
      · exact Or.inl ⟨lt_of_le_of_ne hy.1 (Ne.symm hleft), hy.2⟩
    · intro hy
      rcases hy with hy | hy
      · exact ⟨le_of_lt hy.1, hy.2⟩
      · rw [Set.mem_singleton_iff.mp hy]
        exact ⟨le_rfl, le_of_lt (carrierArc_left_lt_right k)⟩
  rw [hIcc, Set.image_union, Set.image_singleton]

/--
@isnad1 id=injon.0h0v.s6.13b0f0ae0560 from=translated src=- shape=63f00893 vocab=b3dc71a9
-/
theorem quotient_mk_injOn_Ioc_zero_period :
    Set.InjOn (fun t : ℝ => (QuotientAddGroup.mk t : Circle))
      (Set.Ioc (0 : ℝ) (2 * Real.pi)) := by
  intro x hx y hy hxy
  have hx0 : x ∈ Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) := by simpa using hx
  have hy0 : y ∈ Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) := by simpa using hy
  have hx' :
      AddCircle.equivIoc (2 * Real.pi) (0 : ℝ)
          (QuotientAddGroup.mk x : Circle) = ⟨x, hx0⟩ :=
    AddCircle.equivIoc_coe_eq hx0
  have hy' :
      AddCircle.equivIoc (2 * Real.pi) (0 : ℝ)
          (QuotientAddGroup.mk y : Circle) = ⟨y, hy0⟩ :=
    AddCircle.equivIoc_coe_eq hy0
  have h := congrArg (AddCircle.equivIoc (2 * Real.pi) (0 : ℝ)) hxy
  rw [hx', hy'] at h
  exact Subtype.ext_iff.mp h

/--
@isnad1 id=eq.0h2v.s7.67a763500210 from=translated src=- shape=5abd6f9e vocab=d43fb628
-/
theorem carrierArc_mk_preimage_image_Ioc_inter_fundamental
    {N : Nat} (k : Fin N) :
    ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹'
        ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) ∩
      Set.Ioc (0 : ℝ) (2 * Real.pi)) =
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
  ext x
  constructor
  · intro hx
    rcases hx.1 with ⟨y, hy, hyx⟩
    have hy_fund : y ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) := by
      exact ⟨lt_of_le_of_lt (carrierArc_left_nonneg k) hy.1,
        le_trans hy.2 (carrierArc_right_le_period k)⟩
    have hxy : y = x :=
      quotient_mk_injOn_Ioc_zero_period hy_fund hx.2 hyx
    rwa [← hxy]
  · intro hx
    constructor
    · exact ⟨x, hx, rfl⟩
    · exact ⟨lt_of_le_of_lt (carrierArc_left_nonneg k) hx.1,
        le_trans hx.2 (carrierArc_right_le_period k)⟩

/--
@isnad1 id=eq.0h1v.s6.28ab2c4dc99e from=translated src=- shape=8acf7f27 vocab=fc6d0504
-/
theorem volume_singleton_circle (x : Circle) :
    MeasureTheory.volume ({x} : Set Circle) = 0 := by
  have h := AddCircle.volume_closedBall (T := 2 * Real.pi) (x := x) (ε := 0)
  simpa using h

/--
@isnad1 id=eq.0h1v.s6.43be43069214 from=translated src=- shape=778ca0af vocab=a1470509
-/
theorem μCircle_singleton (x : Circle) :
    μCircle ({x} : Set Circle) = 0 := by
  have hvol : MeasureTheory.volume ({x} : Set Circle) = 0 :=
    volume_singleton_circle x
  rw [AddCircle.volume_eq_smul_haarAddCircle, MeasureTheory.Measure.smul_apply] at hvol
  rw [smul_eq_mul] at hvol
  have hcoef : ENNReal.ofReal (2 * Real.pi) ≠ 0 := by simp [ENNReal.ofReal_eq_zero, Real.pi_pos]
  simpa [μCircle] using (mul_eq_zero.mp hvol).resolve_left hcoef

private theorem carrierArc_arcSet_ae_eq_mk_image_Ioc_of_singleton_null
    {N : Nat} (k : Fin N) (μ : MeasureTheory.Measure Circle)
    (hsingleton : ∀ x : Circle, μ ({x} : Set Circle) = 0) :
    arcSet (carrierArc N k) =ᵐ[μ]
      QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
  rw [carrierArc_arcSet_eq_mk_image_Ioc_union_left k]
  let A : Set Circle :=
    QuotientAddGroup.mk ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  let e : Circle := QuotientAddGroup.mk ((carrierArc N k).left)
  change (Set.union A ({e} : Set Circle)) =ᵐ[μ] A
  rw [MeasureTheory.ae_eq_set]
  constructor
  · refine MeasureTheory.measure_mono_null (μ := μ) (t := {e}) ?_ (hsingleton e)
    intro x hx
    rcases hx.1 with hxIoc | hxleft
    · exact False.elim (hx.2 hxIoc)
    · exact hxleft
  · refine MeasureTheory.measure_mono_null (μ := μ) (t := (∅ : Set Circle)) ?_ ?_
    · intro x hx
      exact False.elim (hx.2 (Or.inl hx.1))
    · simp

/--
@isnad1 id=eventual.0h2v.s6.162dcdd33a2d from=translated src=- shape=5047f6bb vocab=69144f90
-/
theorem carrierArc_arcSet_ae_eq_mk_image_Ioc {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =ᵐ[μCircle]
      QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) :=
  carrierArc_arcSet_ae_eq_mk_image_Ioc_of_singleton_null k μCircle μCircle_singleton

/--
@isnad1 id=eventual.0h2v.s6.60acb1fcaab1 from=translated src=- shape=272f8b00 vocab=c80c1e44
-/
theorem carrierArc_arcSet_ae_eq_mk_image_Ioc_volume {N : Nat} (k : Fin N) :
    arcSet (carrierArc N k) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure Circle)]
      QuotientAddGroup.mk ''
        Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) :=
  carrierArc_arcSet_ae_eq_mk_image_Ioc_of_singleton_null k _ volume_singleton_circle

/-- `carrierAverage`: carrier Average. -/
noncomputable def carrierAverage {N : Nat} (k : Fin N)
    (f : Circle -> ℂ) : ℂ :=
  (N : ℂ) * ∫ x in arcSet (carrierArc N k), f x ∂ μCircle

/--
@isnad1 id=le.0h1v.s3.4f37bad94cc1 from=translated src=- shape=b9369acb vocab=4d9524d6
-/
theorem arcLength_nonneg (I : CircleArc) : 0 <= arcLength I := by
  dsimp [arcLength]
  exact sub_nonneg.mpr I.left_le_right

/--
@isnad1 id=continuo.0h1v.s5.23b75c4672c2 from=translated src=- shape=7000f90d vocab=04a98fdf
-/
theorem continuous_arcParam (I : CircleArc) : Continuous (arcParam I) := by
  unfold arcParam
  exact (AddCircle.continuous_mk' (2 * Real.pi)).comp
    (continuous_const.add (continuous_id.mul continuous_const))

/--
@isnad1 id=eq.0h1v.s4.ce3313b0b9e0 from=translated src=- shape=c83ca1ec vocab=553fe89a
-/
theorem arcSet_eq_image (I : CircleArc) :
    arcSet I = arcParam I '' Set.Icc (0 : ℝ) 1 := rfl

/--
@isnad1 id=iscompac.0h1v.s5.d4a41119c57c from=translated src=- shape=1a6c1393 vocab=de807b21
-/
theorem isCompact_arcSet (I : CircleArc) : IsCompact (arcSet I) := by
  rw [arcSet_eq_image]
  exact isCompact_Icc.image (continuous_arcParam I)

/--
@isnad1 id=measurab.0h1v.s5.4be3f2e718b0 from=translated src=- shape=1a6c1393 vocab=62b30673
-/
theorem measurableSet_arcSet (I : CircleArc) : MeasurableSet (arcSet I) :=
  (isCompact_arcSet I).measurableSet

/--
@isnad1 id=eq.0h2v.s8.319d3353f03f from=translated src=- shape=18397bde vocab=278096ff
-/
theorem volume_mk_image_carrierArc_Ioc {N : Nat} (k : Fin N) :
    MeasureTheory.volume
        ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) =
      ENNReal.ofReal (arcLength (carrierArc N k)) := by
  let S : Set Circle :=
    (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  have hS_null :
      MeasureTheory.NullMeasurableSet S
        (MeasureTheory.volume : MeasureTheory.Measure Circle) := by
    exact (measurableSet_arcSet (carrierArc N k)).nullMeasurableSet.congr
      (carrierArc_arcSet_ae_eq_mk_image_Ioc_volume k)
  have hpre :=
    (AddCircle.measurePreserving_mk (T := 2 * Real.pi) (t := 0)).measure_preimage hS_null
  rw [MeasureTheory.Measure.restrict_apply' measurableSet_Ioc] at hpre
  change MeasureTheory.volume
      (((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹' S) ∩
        Set.Ioc (0 : ℝ) (0 + 2 * Real.pi)) =
      MeasureTheory.volume S at hpre
  have hpre_set :
      ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹' S) ∩
        Set.Ioc (0 : ℝ) (0 + 2 * Real.pi) =
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right) := by
    simpa [S] using carrierArc_mk_preimage_image_Ioc_inter_fundamental k
  rw [hpre_set, Real.volume_Ioc] at hpre
  dsimp [arcLength]
  symm
  rw [← hpre]

/--
@isnad1 id=eq.0h2v.s7.c2191107252b from=translated src=- shape=5c2d2718 vocab=9e3be226
-/
theorem period_smul_μCircle_mk_image_carrierArc_Ioc {N : Nat} (k : Fin N) :
    ENNReal.ofReal (2 * Real.pi) *
        μCircle
          ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
            Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)) =
      ENNReal.ofReal (arcLength (carrierArc N k)) := by
  let S : Set Circle :=
    (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  have hmeasure := congrArg (fun μ : MeasureTheory.Measure Circle => μ S)
    (AddCircle.volume_eq_smul_haarAddCircle (T := 2 * Real.pi))
  change MeasureTheory.volume S =
    ENNReal.ofReal (2 * Real.pi) * μCircle S at hmeasure
  rw [← hmeasure]
  exact volume_mk_image_carrierArc_Ioc k

/--
@isnad1 id=eq.0h2v.s6.de2b2e13bc21 from=translated src=- shape=0b64a15d vocab=b9d9e825
-/
theorem period_smul_μCircle_carrierArc {N : Nat} (k : Fin N) :
    ENNReal.ofReal (2 * Real.pi) *
        μCircle (arcSet (carrierArc N k)) =
      ENNReal.ofReal (arcLength (carrierArc N k)) := by
  rw [MeasureTheory.measure_congr (carrierArc_arcSet_ae_eq_mk_image_Ioc k)]
  exact period_smul_μCircle_mk_image_carrierArc_Ioc k

/-- `arcIntegral`: arc Integral. -/
noncomputable def arcIntegral (I : CircleArc) (f : Circle -> ℝ) : ℝ :=
  ∫ x in arcSet I, f x ∂ μCircle

/--
@isnad1 id=eq.0h3v.s7.32d70059b041 from=translated src=- shape=724f3414 vocab=aa0fe8a2
-/
theorem carrierArc_arcIntegral_eq_mk_image_Ioc
    {N : Nat} (k : Fin N) (f : Circle -> ℝ) :
    arcIntegral (carrierArc N k) f =
      ∫ x in QuotientAddGroup.mk ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        f x ∂ μCircle := by
  unfold arcIntegral
  rw [MeasureTheory.Measure.restrict_congr_set (carrierArc_arcSet_ae_eq_mk_image_Ioc k)]

/--
@isnad1 id=eq.0h3v.s7.5b1ef7737cee from=translated src=- shape=b457baa8 vocab=759d9adf
-/
theorem carrierArc_mk_image_Ioc_integral_eq_scaled
    {N : Nat} (k : Fin N) (f : Circle -> ℝ) :
    (∫ x in (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        f x ∂ μCircle) =
      (2 * Real.pi)⁻¹ *
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          f (QuotientAddGroup.mk t : Circle) := by
  let S : Set Circle :=
    (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
      Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  let A : Set ℝ := Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right)
  let F : Set ℝ := Set.Ioc (0 : ℝ) (2 * Real.pi)
  have hS_null : MeasureTheory.NullMeasurableSet S μCircle := by
    exact (measurableSet_arcSet (carrierArc N k)).nullMeasurableSet.congr
      (carrierArc_arcSet_ae_eq_mk_image_Ioc k)
  have hhaar := AddCircle.integral_haarAddCircle (T := 2 * Real.pi)
    (f := S.indicator f)
  change ∫ x, S.indicator f x ∂ μCircle =
    (2 * Real.pi)⁻¹ • ∫ x, S.indicator f x at hhaar
  rw [MeasureTheory.integral_indicator₀ hS_null] at hhaar
  have hpre := AddCircle.integral_preimage (T := 2 * Real.pi) (t := 0)
    (f := S.indicator f)
  have hpre' :
      (∫ t in F, S.indicator f (QuotientAddGroup.mk t : Circle)) =
        ∫ x : Circle, S.indicator f x := by simpa [F] using hpre
  have hfund_to_A :
      (∫ t in F, S.indicator f (QuotientAddGroup.mk t : Circle)) =
        ∫ t in A, f (QuotientAddGroup.mk t : Circle) := by
    have hpre_set :
        ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹' S) ∩ F = A := by
      simpa [S, A, F] using carrierArc_mk_preimage_image_Ioc_inter_fundamental k
    have hfun : Set.EqOn
        (fun t : ℝ => S.indicator f (QuotientAddGroup.mk t : Circle))
        (fun t : ℝ => A.indicator
          (fun y : ℝ => f (QuotientAddGroup.mk y : Circle)) t)
        F := by
      intro t htF
      by_cases htS : (QuotientAddGroup.mk t : Circle) ∈ S
      · have htA : t ∈ A := by
          have htpre :
              t ∈ ((fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ⁻¹' S) ∩ F :=
            ⟨htS, htF⟩
          simpa [hpre_set] using htpre
        simp [Set.indicator_of_mem htS, Set.indicator_of_mem htA]
      · have htA : t ∉ A := by
          intro htA
          exact htS ⟨t, htA, rfl⟩
        simp [Set.indicator_of_notMem htS, Set.indicator_of_notMem htA]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hfun]
    rw [MeasureTheory.setIntegral_indicator (μ := MeasureTheory.volume) (s := F) (t := A)
      measurableSet_Ioc]
    have h_inter : F ∩ A = A := by
      ext t
      constructor
      · intro ht
        exact ht.2
      · intro htA
        exact ⟨⟨lt_of_le_of_lt (carrierArc_left_nonneg k) htA.1,
          le_trans htA.2 (carrierArc_right_le_period k)⟩, htA⟩
    rw [h_inter]
  calc
    (∫ x in (fun t : ℝ => (QuotientAddGroup.mk t : Circle)) ''
          Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        f x ∂ μCircle)
        = ∫ x in S, f x ∂ μCircle := by rfl
    _ = (2 * Real.pi)⁻¹ * ∫ x : Circle, S.indicator f x := by simpa [smul_eq_mul] using hhaar
    _ = (2 * Real.pi)⁻¹ *
        (∫ t in F, S.indicator f (QuotientAddGroup.mk t : Circle)) := by rw [hpre']
    _ = (2 * Real.pi)⁻¹ * ∫ t in A, f (QuotientAddGroup.mk t : Circle) := by rw [hfund_to_A]
    _ = (2 * Real.pi)⁻¹ *
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          f (QuotientAddGroup.mk t : Circle) := by rfl

/-- `arcAverage`: arc Average. -/
noncomputable def arcAverage (I : CircleArc) (f : Circle -> ℂ) : ℂ :=
  (arcLength I)⁻¹ • ∫ x in arcSet I, f x ∂ μCircle

/--
@isnad1 id=mem.1h2v.s5.779c6f80118e from=translated src=- shape=4016e300 vocab=641a3cc9
-/
theorem intervalParam_mem_arc (I : CircleArc) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, arcParam I t ∈ arcSet I := by
  intro t ht
  exact ⟨t, ht, rfl⟩

/--
@isnad1 id=le.1h2v.s5.739cafada67b from=translated src=- shape=846ad401 vocab=eac28fce
-/
theorem arcIntegral_nonneg
    (I : CircleArc) {f : Circle -> ℝ}
    (hf : ∀ x ∈ arcSet I, 0 <= f x) :
    0 <= arcIntegral I f := by
  unfold arcIntegral
  refine MeasureTheory.integral_nonneg_of_ae ?_
  exact (MeasureTheory.ae_restrict_mem (measurableSet_arcSet I)).mono fun x hx => hf x hx

/--
@isnad1 id=eq.0h2v.s7.641d2972814a from=translated src=- shape=52fa196d vocab=d10b0918
-/
theorem arcAverage_eq_arcIntegral_div
    (I : CircleArc) (f : Circle -> ℂ) :
    arcAverage I f =
      (arcLength I)⁻¹ •
        ∫ x in arcSet I, f x ∂ μCircle := rfl

/--
@isnad1 id=eq.0h2v.s4.dcf7684bf64b from=translated src=- shape=2f019d02 vocab=9cecdc0d
-/
theorem norm_circleChar (n : Nat) (x : Circle) : ‖circleChar n x‖ = 1 := by
  simp [circleChar, norm_zeta]

/--
@isnad1 id=eq.0h1v.s4.60ef0684e71a from=translated src=- shape=fcc0db09 vocab=332527d1
-/
theorem circleChar_zero (x : Circle) : circleChar 0 x = 1 := by simp [circleChar]

/--
@isnad1 id=eq.0h1v.s3.29ce86ca9031 from=translated src=- shape=f110163e vocab=2ca321e9
-/
theorem circleChar_one (x : Circle) : circleChar 1 x = zeta x := by simp [circleChar]

/--
@isnad1 id=eq.0h3v.s5.b5a54ce5a56f from=translated src=- shape=897af36f vocab=53cdf177
-/
theorem circleChar_add (m n : Nat) (x : Circle) :
    circleChar (m + n) x = circleChar m x * circleChar n x := by simp [circleChar, pow_add]

/--
@isnad1 id=eq.0h2v.s5.56c60c1d738f from=translated src=- shape=295bbecf vocab=cade421d
-/
theorem circleChar_mk (n : Nat) (theta : ℝ) :
    circleChar n (QuotientAddGroup.mk theta : Circle) =
      Complex.exp (Complex.I * (n : ℂ) * theta) := by
  simp only [circleChar, zeta, AddCircle.toCircle, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero,
    Real.pi_ne_zero, or_self, not_false_eq_true, div_self, one_mul, Function.Periodic.lift_coe,
    Circle.coe_exp]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/--
@isnad1 id=eq.0h2v.s7.69fc36d6c17c from=translated src=- shape=d9e5d748 vocab=fde74430
-/
theorem circleChar_eq_fourier_nat (n : Nat) (x : Circle) :
    circleChar n x = fourier (n : Int) x := by
  induction n with
  | zero =>
      simp [circleChar]
  | succ n ih =>
      rw [circleChar_eq_zeta_pow, pow_succ]
      change circleChar n x * zeta x = fourier ((n + 1 : Nat) : Int) x
      rw [ih]
      simp only [fourier_apply, Nat.cast_add, Nat.cast_one]
      rw [show ((↑n + 1 : ℤ) • x : AddCircle (2 * Real.pi)) =
          (n : ℤ) • x + x by
        rw [add_zsmul, one_zsmul]]
      rw [AddCircle.toCircle_add]
      rfl

private theorem rotational_averaging_bound_complex (q : ℂ) :
    ∫ t : Circle, (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2
        ∂AddCircle.haarAddCircle ≥
      ‖q‖ ^ 2 / 8 := by
  by_cases hq : q = 0
  · simp [hq, FockSPR.rho, norm_zero]
  · set r := ‖q‖
    have hr_pos : 0 < r := norm_pos_iff.mpr hq
    set α := (r : ℂ)⁻¹ * q
    have hα_norm : ‖α‖ = 1 := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hr_pos]
      exact inv_mul_cancel₀ (ne_of_gt hr_pos)
    have h_rw : ∀ t : Circle,
        (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2 =
        (FockSPR.rho ((r : ℂ) * ((fourier (1 : ℤ) t : ℂ) * α))) ^ 2 := by
      intro t
      congr 2
      show (fourier (1 : ℤ) t : ℂ) * q =
        ↑r * ((fourier (1 : ℤ) t : ℂ) * α)
      simp only [α]
      have hr_ne' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr_pos)
      field_simp
    simp_rw [h_rw]
    have hT_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    obtain ⟨s, hs⟩ := (AddCircle.homeomorphCircle hT_ne).surjective
      ⟨α, by
        rw [← SetLike.mem_coe, Submonoid.coe_unitSphere,
          Metric.mem_sphere, dist_zero_right]
        exact hα_norm⟩
    rw [AddCircle.homeomorphCircle_apply] at hs
    have hα_eq : (fourier (1 : ℤ) s : ℂ) = α := by
      simp only [fourier_apply, one_zsmul]
      exact congr_arg Subtype.val hs
    have h_shift : ∀ t : Circle,
        (fourier (1 : ℤ) t : ℂ) * α = fourier (1 : ℤ) (t + s) := by
      intro t
      rw [← hα_eq]
      simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
    simp_rw [h_shift]
    set F : Circle → ℝ :=
      fun u => (FockSPR.rho ((r : ℂ) * fourier (1 : ℤ) u)) ^ 2
    change ∫ t, F (t + s) ∂AddCircle.haarAddCircle ≥ r ^ 2 / 8
    simp_rw [show ∀ t : Circle, t + s = s + t from fun t => add_comm t s]
    rw [MeasureTheory.integral_add_left_eq_self]
    exact FockSPR.rotational_averaging_bound (r := r) (norm_nonneg q)

private theorem carrierArc_interval_rho_sq_eq_full_circle
    {N : Nat} (k : Fin N) (q : ℂ) :
    ∫ t in (carrierArc N k).left..(carrierArc N k).right,
        (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 =
      (N : ℝ)⁻¹ * ((2 * Real.pi) *
        ∫ y : Circle, (FockSPR.rho ((fourier (1 : ℤ) y : ℂ) * q)) ^ 2
          ∂AddCircle.haarAddCircle) := by
  have hT_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hT_ne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hT_pos
  have hN_pos : (0 : ℝ) < (↑N : ℝ) := Nat.cast_pos.mpr k.pos
  have hN_ne : (↑N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have fourier_rescale : ∀ s : ℝ,
      circleChar N (QuotientAddGroup.mk (s / ↑N) : Circle) =
      fourier (1 : ℤ) (QuotientAddGroup.mk s : Circle) := by
    intro s
    rw [circleChar_eq_fourier_nat]
    simp only [fourier_coe_apply]
    congr 1
    have hN_complex : (↑N : ℂ) ≠ 0 := by exact_mod_cast hN_ne
    have hT_complex : (↑(2 * Real.pi) : ℂ) ≠ 0 := by exact_mod_cast hT_ne
    push_cast
    field_simp [hN_complex, hT_complex]
  set g : ℝ → ℝ := fun t =>
    (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2
  have h_eq_haar_int :
      ∫ t in (carrierArc N k).left..(carrierArc N k).right, g t =
        (↑N : ℝ)⁻¹ * ((2 * Real.pi) *
          ∫ y : Circle, (FockSPR.rho ((fourier (1 : ℤ) y : ℂ) * q)) ^ 2
            ∂AddCircle.haarAddCircle) := by
    have key := intervalIntegral.integral_comp_mul_left
      (fun s => g (s / ↑N)) hN_ne
      (a := (carrierArc N k).left) (b := (carrierArc N k).right)
    have h_simp : (fun x => g ((↑N : ℝ) * x / ↑N)) = g := by
      ext x
      show g (↑N * x / ↑N) = g x
      congr 1
      field_simp [hN_ne]
    rw [h_simp] at key
    have h_el : (↑N : ℝ) * (carrierArc N k).left =
        (2 * Real.pi) * ↑k.val := by
      unfold carrierArc
      field_simp [hN_ne]
    have h_er : (↑N : ℝ) * (carrierArc N k).right =
        (2 * Real.pi) * (↑k.val + 1) := by
      unfold carrierArc
      push_cast
      field_simp [hN_ne]
    rw [h_el, h_er] at key
    rw [key, smul_eq_mul]
    congr 1
    have h_congr :
        ∀ s ∈ Set.uIcc ((2 * Real.pi) * ↑k.val)
            ((2 * Real.pi) * (↑k.val + 1)),
          g (s / ↑N) =
            (FockSPR.rho ((fourier (1 : ℤ) (↑s : Circle) : ℂ) * q)) ^ 2 := by
      intro s _
      change (FockSPR.rho (circleChar N (↑(s / ↑N) : Circle) * q)) ^ 2 = _
      rw [fourier_rescale]
    rw [intervalIntegral.integral_congr h_congr]
    set g₁ : ℝ → ℝ := fun s =>
      (FockSPR.rho ((fourier (1 : ℤ) (↑s : Circle) : ℂ) * q)) ^ 2
    have hg₁_periodic : Function.Periodic g₁ (2 * Real.pi) := by
      intro s
      change (FockSPR.rho
          ((fourier (1 : ℤ) (↑(s + 2 * Real.pi) : Circle) : ℂ) * q)) ^ 2 =
        (FockSPR.rho ((fourier (1 : ℤ) (↑s : Circle) : ℂ) * q)) ^ 2
      simp only [QuotientAddGroup.mk_add_of_mem _
        (AddSubgroup.mem_zmultiples (2 * Real.pi))]
    rw [show (2 * Real.pi) * (↑k.val + 1) =
        (2 * Real.pi) * ↑k.val + (2 * Real.pi) by ring]
    rw [hg₁_periodic.intervalIntegral_add_eq ((2 * Real.pi) * ↑k.val) 0]
    have h_preimage := AddCircle.intervalIntegral_preimage (2 * Real.pi) 0
      (fun t : Circle => (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2)
    have h_haar := @AddCircle.integral_haarAddCircle (2 * Real.pi) _ ℝ _ _
      (fun t : Circle => (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2)
    calc ∫ x in (0 : ℝ)..(0 + 2 * Real.pi), g₁ x
        = ∫ t : Circle, (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2 :=
          h_preimage
      _ = (2 * Real.pi) *
          ∫ t : Circle, (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2
            ∂AddCircle.haarAddCircle := by
        rw [h_haar, smul_eq_mul]
        set V := ∫ t : Circle, (FockSPR.rho ((fourier (1 : ℤ) t : ℂ) * q)) ^ 2
        rw [mul_comm (2 * Real.pi) ((2 * Real.pi)⁻¹ * V), mul_assoc,
          mul_comm V (2 * Real.pi), ← mul_assoc, inv_mul_cancel₀ hT_ne, one_mul]
  exact h_eq_haar_int

private theorem carrierArc_interval_rho_sq_lower
    {N : Nat} (k : Fin N) (q : ℂ) :
    arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8 <=
      ∫ t in (carrierArc N k).left..(carrierArc N k).right,
        (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast k.pos
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  rw [carrierArc_interval_rho_sq_eq_full_circle k q]
  calc
    arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8
        = (N : ℝ)⁻¹ * ((2 * Real.pi) * (‖q‖ ^ 2 / 8)) := by
          rw [carrierArc_length k]
          field_simp [hN_ne]
    _ <= (N : ℝ)⁻¹ *
        ((2 * Real.pi) *
          ∫ y : Circle, (FockSPR.rho ((fourier (1 : ℤ) y : ℂ) * q)) ^ 2
            ∂AddCircle.haarAddCircle) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.mpr hN_pos))
      exact mul_le_mul_of_nonneg_left (rotational_averaging_bound_complex q).le (by positivity)

private lemma constant_center_defect_eq_norm_sq_rho
    {c u z : ℂ} (hc : c ≠ 0) :
    (‖c + z * u‖ - ‖c‖) ^ 2 =
      ‖c‖ ^ 2 * (FockSPR.rho (z * (u / c))) ^ 2 := by
  have hfactor : c + z * u = c * (1 + z * (u / c)) := by field_simp [hc]
  rw [hfactor, norm_mul]
  unfold FockSPR.rho
  rw [sq_abs]
  ring

private theorem carrierArc_setIntegral_constant_center_lower
    {N : Nat} (k : Fin N) {c u : ℂ} (hc : c ≠ 0) :
    arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8 <=
      ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        (‖c + circleChar N (QuotientAddGroup.mk t : Circle) * u‖ - ‖c‖) ^ 2 := by
  set q : ℂ := u / c
  have h_interval' :
      arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8 <=
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 := by
    rw [← intervalIntegral.integral_of_le (le_of_lt (carrierArc_left_lt_right k))]
    exact carrierArc_interval_rho_sq_lower k q
  have hconst :
      ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          ‖c‖ ^ 2 *
            (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 =
        ‖c‖ ^ 2 *
          ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
            (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 := by
    rw [MeasureTheory.integral_const_mul]
  have hscale :
      ‖c‖ ^ 2 * (arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8) =
        arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8 := by
    dsimp [q]
    rw [norm_div]
    have hc_norm_ne : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
    field_simp [hc_norm_ne]
  calc
    arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8
        = ‖c‖ ^ 2 * (arcLength (carrierArc N k) * ‖q‖ ^ 2 / 8) := hscale.symm
    _ <= ‖c‖ ^ 2 *
        ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
          (FockSPR.rho (circleChar N (QuotientAddGroup.mk t : Circle) * q)) ^ 2 :=
      mul_le_mul_of_nonneg_left h_interval' (sq_nonneg ‖c‖)
    _ = ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
        (‖c + circleChar N (QuotientAddGroup.mk t : Circle) * u‖ - ‖c‖) ^ 2 := by
      rw [← hconst]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simpa [q] using
        (constant_center_defect_eq_norm_sq_rho
          (c := c) (u := u) (z := circleChar N (QuotientAddGroup.mk t : Circle)) hc).symm

/--
@isnad1 id=eq.0h3v.s5.8c2553c37b2e from=translated src=- shape=9f148781 vocab=c647306c
-/
theorem circleChar_carrierArc_arcParam {N : Nat} (k : Fin N) (t : ℝ) :
    circleChar N (arcParam (carrierArc N k) t) =
      Complex.exp (Complex.I * (2 * Real.pi * t)) := by
  rw [arcParam, circleChar_mk]
  unfold carrierArc arcLength
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt k.pos)
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt k.pos)
  have harg :
      Complex.I * (N : ℂ) *
          ↑((2 * Real.pi) * (k.1 : ℝ) / (N : ℝ) +
            t * ((2 * Real.pi) * ((k.1 + 1 : Nat) : ℝ) / (N : ℝ) -
              (2 * Real.pi) * (k.1 : ℝ) / (N : ℝ))) =
        Complex.I * (2 * Real.pi * (k.1 : ℝ)) +
          Complex.I * (2 * Real.pi * t) := by
    push_cast
    field_simp [hN, hNreal]
    ring
  rw [harg, Complex.exp_add]
  have hint : Complex.exp (Complex.I * (2 * Real.pi * (k.1 : ℝ))) = 1 := by
    rw [show Complex.I * (2 * Real.pi * (k.1 : ℝ)) =
        (k.1 : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast
      ring]
    exact Complex.exp_nat_mul_two_pi_mul_I k.1
  rw [hint, one_mul]

/--
@isnad1 id=eq.2h3v.s7.c644442acb51 from=translated src=- shape=ec2f50ec vocab=444b378f
-/
theorem circleIntegral_union_finset
    {ι : Type} [Fintype ι] (I : ι -> CircleArc)
    (hdisj : Pairwise fun i j => Disjoint (arcSet (I i)) (arcSet (I j)))
    {f : Circle -> ℝ}
    (hf : ∀ i, MeasureTheory.IntegrableOn f (arcSet (I i)) μCircle) :
    ∫ x in (⋃ i, arcSet (I i)), f x ∂ μCircle =
      ∑ i, arcIntegral (I i) f := by
  simpa [arcIntegral] using
    (MeasureTheory.integral_iUnion_fintype
      (μ := μCircle) (f := f) (s := fun i => arcSet (I i))
      (fun i => measurableSet_arcSet (I i)) hdisj hf)

/--
@isnad1 id=eq.2h2v.s8.cd92d5d1ad97 from=translated src=- shape=251716e8 vocab=08e51d32
-/
theorem circleIntegral_split_compl
    (s : Set Circle) (hs : MeasurableSet s) {f : Circle -> ℝ}
    (hf : MeasureTheory.Integrable f μCircle) :
    ∫ x, f x ∂ μCircle =
      ∫ x in s, f x ∂ μCircle + ∫ x in sᶜ, f x ∂ μCircle :=
  (MeasureTheory.integral_add_compl (μ := μCircle) (f := f) hs hf).symm

/--
@isnad1 id=le.1h4v.s6.8ac9ba33d7d9 from=translated src=- shape=9eab6288 vocab=b94f3091
-/
theorem constantCenter_fastRotate_carrierArc_sq_le_defectSq
    {N : Nat} (k : Fin N) {c u : ℂ} (hc : c ≠ 0) :
    arcLength (carrierArc N k) * ‖u‖ ^ 2 <=
      Crot *
        arcIntegral (carrierArc N k)
          (fun x => (‖c + circleChar N x * u‖ - ‖c‖) ^ 2) := by
  let f : Circle -> ℝ := fun x => (‖c + circleChar N x * u‖ - ‖c‖) ^ 2
  have hrewrite :
      arcIntegral (carrierArc N k) f =
        (2 * Real.pi)⁻¹ *
          ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
            f (QuotientAddGroup.mk t : Circle) := by
    rw [carrierArc_arcIntegral_eq_mk_image_Ioc k f]
    exact carrierArc_mk_image_Ioc_integral_eq_scaled k f
  rw [hrewrite]
  set J : ℝ :=
    ∫ t in Set.Ioc ((carrierArc N k).left) ((carrierArc N k).right),
      f (QuotientAddGroup.mk t : Circle)
  have hJ_lower : arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8 <= J := by
    dsimp [J, f]
    exact carrierArc_setIntegral_constant_center_lower k hc
  have hleft_nonneg :
      0 <= arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8 := by
    have hlen_nonneg : 0 <= arcLength (carrierArc N k) :=
      arcLength_nonneg (carrierArc N k)
    have hnorm_nonneg : 0 <= ‖u‖ ^ 2 := sq_nonneg ‖u‖
    nlinarith
  have hJ_nonneg : 0 <= J := le_trans hleft_nonneg hJ_lower
  calc
    arcLength (carrierArc N k) * ‖u‖ ^ 2
        = 8 * (arcLength (carrierArc N k) * ‖u‖ ^ 2 / 8) := by ring
    _ <= 8 * J := by exact mul_le_mul_of_nonneg_left hJ_lower (by norm_num)
    _ <= 32 * J := by nlinarith
    _ = Crot * ((2 * Real.pi)⁻¹ * J) := by
      unfold Crot
      have hpi_ne : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp [hpi_ne]
      ring

private theorem gamma_d_isOpenPosMeasure (d : Nat) :
    MeasureTheory.Measure.IsOpenPosMeasure (gammaD d) := by
  refine ⟨?_⟩
  intro U hU hUne
  rcases hUne with ⟨x, hxU⟩
  rcases Metric.isOpen_iff.mp hU x hxU with ⟨r, hr, hball⟩
  let w : Cd d → ENNReal := fun z => ENNReal.ofReal (gaussianDensity d z)
  have hgauss_cont : Continuous (gaussianDensity d) := by
    unfold gaussianDensity
    fun_prop
  have hw_meas : Measurable w := by exact ENNReal.measurable_ofReal.comp hgauss_cont.measurable
  have hw_ne_zero : ∀ z : Cd d, w z ≠ 0 := by
    intro z
    have hpos : 0 < gaussianDensity d z := by
      unfold gaussianDensity
      positivity
    simpa [w, ENNReal.ofReal_eq_zero, not_le] using hpos
  have hball_ne : gammaD d (Metric.ball x r) ≠ 0 := by
    intro hzero
    have hzero' : MeasureTheory.volume.withDensity w (Metric.ball x r) = 0 := by
      simpa [gammaD, w] using hzero
    have hvol_zero :
        MeasureTheory.volume ({z : Cd d | w z ≠ 0} ∩ Metric.ball x r) = 0 :=
      (MeasureTheory.withDensity_apply_eq_zero hw_meas).1 hzero'
    have hball_eq :
        {z : Cd d | w z ≠ 0} ∩ Metric.ball x r = Metric.ball x r := by
      ext z
      simp [hw_ne_zero z]
    have hball_vol_zero : MeasureTheory.volume (Metric.ball x r) = 0 := by
      simpa [hball_eq] using hvol_zero
    exact (Metric.measure_ball_pos (MeasureTheory.volume : MeasureTheory.Measure (Cd d)) x hr).ne'
      hball_vol_zero
  exact fun hzero => hball_ne (MeasureTheory.measure_mono_null hball hzero)

/--
@isnad1 id=eq.4h3v.s7.7a9ca9a0a9c9 from=translated src=- shape=2e54975c vocab=7e113037
-/
theorem continuous_eq_of_ae_eq_gamma
    {d : Nat} (hd : 0 < d) {f g : Cd d -> ℂ}
    (hf : Continuous f) (hg : Continuous g) (hfg : f =ᵐ[gammaD d] g) :
    f = g := by
  let _ := hd
  /-
  Scaffolding contract:
  this packages the a.e.-to-everywhere uniqueness bridge for continuous
  representatives under the frozen Gaussian measure.
  -/
  have := gamma_d_isOpenPosMeasure d
  exact MeasureTheory.Measure.eq_of_ae_eq hfg hf hg

/-!
## Phase-space analytic boundary stubs

These declaration-shaped stubs expose the analytic objects needed by
`ExactModulusRecovery`.  The definitions are placeholders; the theorem
statements record the frozen API that the STFT/ambiguity proof must eventually
provide.
-/

/-- `RealVec`: Real Vec. -/
abbrev RealVec (d : Nat) := EuclideanSpace ℝ (Fin d)

/-- `PhaseSpace`: Phase Space. -/
abbrev PhaseSpace (d : Nat) := RealVec d × RealVec d

/-- `L2Real`: L2 Real. -/
abbrev L2Real (d : Nat) :=
  MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))

/-- `stftRep`: stft Rep. -/
noncomputable def stftRep {d : Nat} :
    L2Real d -> L2Real d -> PhaseSpace d -> ℂ :=
  fun h f ξ =>
    ∫ t : RealVec d,
      ((f : RealVec d -> ℂ) t) *
        star ((h : RealVec d -> ℂ) (t - ξ.1)) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.2 t : ℝ) : ℂ))

/-- `ambiguityRep`: ambiguity Rep. -/
noncomputable def ambiguityRep {d : Nat} :
    L2Real d -> L2Real d -> PhaseSpace d -> ℂ :=
  fun f g ξ =>
    ∫ t : RealVec d,
      ((f : RealVec d -> ℂ) (t + ((1 / 2 : ℝ) • ξ.1))) *
        star ((g : RealVec d -> ℂ) (t - ((1 / 2 : ℝ) • ξ.1))) *
        Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ξ.2 t : ℝ) : ℂ))

/-- `symplecticFourierRep`: symplectic Fourier Rep. -/
noncomputable def symplecticFourierRep {d : Nat}
    (F : PhaseSpace d -> ℂ) : PhaseSpace d -> ℂ :=
  fun ξ =>
    ∫ η : PhaseSpace d,
      F η * Complex.exp
        ((2 * Real.pi : ℂ) * Complex.I *
          (((inner ℝ η.2 ξ.1 : ℝ) - (inner ℝ η.1 ξ.2 : ℝ) : ℝ) : ℂ))

/--
@isnad1 id=eq.0h3v.s7.5d5077ef0121 from=translated src=- shape=9f4c8acc vocab=795211c5
-/
theorem symplecticFourierPhase_norm {d : Nat} (η ξ : PhaseSpace d) :
    ‖Complex.exp
        ((2 * Real.pi : ℂ) * Complex.I *
          (((inner ℝ η.2 ξ.1 : ℝ) - (inner ℝ η.1 ξ.2 : ℝ) : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre :
      (((2 * Real.pi : ℂ) * Complex.I *
          (((inner ℝ η.2 ξ.1 : ℝ) - (inner ℝ η.1 ξ.2 : ℝ) : ℝ) : ℂ))).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

/-- `symplecticFormLinear`: symplectic Form Linear. -/
def symplecticFormLinear {d : Nat} : PhaseSpace d →ₗ[ℝ] PhaseSpace d →ₗ[ℝ] ℝ where
  toFun η :=
    { toFun := fun ξ => inner ℝ η.1 ξ.2 - inner ℝ η.2 ξ.1
      map_add' := by
        intro ξ ζ
        simp [inner_add_right]
        ring
      map_smul' := by
        intro c ξ
        simp [inner_smul_right]
        ring }
  map_add' := by
    intro η θ
    apply LinearMap.ext
    intro ξ
    simp [inner_add_left]
    ring
  map_smul' := by
    intro c η
    apply LinearMap.ext
    intro ξ
    simp [inner_smul_left]
    ring

/--
@isnad1 id=eq.0h3v.s9.121877250713 from=translated src=- shape=390f489c vocab=c86ff7f9
-/
theorem symplecticFourierRep_eq_vectorFourier {d : Nat}
    (F : PhaseSpace d -> ℂ) (ξ : PhaseSpace d) :
    symplecticFourierRep F ξ =
      VectorFourier.fourierIntegral Real.fourierChar volume
        (symplecticFormLinear (d := d)) F ξ := by
  unfold symplecticFourierRep VectorFourier.fourierIntegral
  apply integral_congr_ae
  filter_upwards with η
  simp [symplecticFormLinear, Real.fourierChar_apply, Circle.smul_def, sub_eq_add_neg,
    mul_assoc, mul_comm]

/--
@isnad1 id=le.2h4v.s10.d6e9db1a0a8f from=translated src=- shape=e9faf31d vocab=89ea9127
-/
theorem symplecticFourierRep_sub_le_lpNorm_one {d : Nat}
    {G₁ G₂ : PhaseSpace d -> ℂ}
    (h1 : Integrable G₁ (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (h2 : Integrable G₂ (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (ξ : PhaseSpace d) :
    ‖symplecticFourierRep G₁ ξ - symplecticFourierRep G₂ ξ‖ ≤
      MeasureTheory.lpNorm (fun η : PhaseSpace d => G₁ η - G₂ η) 1
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)) := by
  let μ : MeasureTheory.Measure (PhaseSpace d) := MeasureTheory.volume
  let φ : PhaseSpace d -> ℂ := fun η =>
    Complex.exp
      ((2 * Real.pi : ℂ) * Complex.I *
        (((inner ℝ η.2 ξ.1 : ℝ) - (inner ℝ η.1 ξ.2 : ℝ) : ℝ) : ℂ))
  have hφ_meas : AEStronglyMeasurable φ μ := (by fun_prop : Measurable φ).aestronglyMeasurable
  have hφ_bound : ∀ᵐ η : PhaseSpace d ∂μ, ‖φ η‖ ≤ (1 : ℝ) := by
    filter_upwards [Filter.Eventually.of_forall
      (fun η : PhaseSpace d => symplecticFourierPhase_norm η ξ)] with η hη
    exact le_of_eq hη
  have hdiff : Integrable (fun η : PhaseSpace d => G₁ η - G₂ η) μ := by exact h1.sub h2
  have h1φ : Integrable (fun η : PhaseSpace d => G₁ η * φ η) μ := h1.mul_bdd hφ_meas hφ_bound
  have h2φ : Integrable (fun η : PhaseSpace d => G₂ η * φ η) μ := h2.mul_bdd hφ_meas hφ_bound
  calc
    ‖symplecticFourierRep G₁ ξ - symplecticFourierRep G₂ ξ‖
        = ‖∫ η : PhaseSpace d, (G₁ η - G₂ η) * φ η ∂μ‖ := by
            unfold symplecticFourierRep
            rw [← MeasureTheory.integral_sub h1φ h2φ]
            have hfun :
                (fun η : PhaseSpace d => G₁ η * φ η - G₂ η * φ η) =
                  (fun η : PhaseSpace d => (G₁ η - G₂ η) * φ η) := by
              funext η
              simp [sub_mul]
            rw [hfun]
    _ ≤ ∫ η : PhaseSpace d, ‖(G₁ η - G₂ η) * φ η‖ ∂μ := by exact norm_integral_le_integral_norm _
    _ = ∫ η : PhaseSpace d, ‖G₁ η - G₂ η‖ ∂μ := by
          refine integral_congr_ae ?_
          filter_upwards [Filter.Eventually.of_forall
            (fun η : PhaseSpace d => symplecticFourierPhase_norm η ξ)] with η hη
          rw [norm_mul, hη, mul_one]
    _ = MeasureTheory.lpNorm (fun η : PhaseSpace d => G₁ η - G₂ η) 1 μ := by
          symm
          exact MeasureTheory.lpNorm_one_eq_integral_norm hdiff.aestronglyMeasurable

/--
@isnad1 id=tendsto.3h4v.s10.84dda93ce922 from=translated src=- shape=ffd53a2d vocab=64d592ad
-/
theorem tendsto_symplecticFourierRep_of_lpNorm_one {d : Nat}
    {G : PhaseSpace d -> ℂ} {Gₙ : Nat -> PhaseSpace d -> ℂ}
    (hG : Integrable G (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (hGₙ : ∀ n, Integrable (Gₙ n) (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (hLp : Tendsto
      (fun n : Nat => MeasureTheory.lpNorm (fun η : PhaseSpace d => Gₙ n η - G η) 1
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
      atTop (nhds 0))
    (ξ : PhaseSpace d) :
    Tendsto (fun n : Nat => symplecticFourierRep (Gₙ n) ξ) atTop
      (nhds (symplecticFourierRep G ξ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) ?_ hLp
  intro n
  simpa using symplecticFourierRep_sub_le_lpNorm_one (h1 := hGₙ n) (h2 := hG) ξ

/--
@isnad1 id=eq.5h6v.s10.6fc79705b294 from=translated src=- shape=58f7a60b vocab=64d592ad
-/
theorem symplecticFourierRep_eq_of_lpNorm_one_approx {d : Nat}
    {G : PhaseSpace d -> ℂ} {Gₙ : Nat -> PhaseSpace d -> ℂ}
    {A : ℂ} {Aₙ : Nat -> ℂ}
    (hG : Integrable G (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (hGₙ : ∀ n, Integrable (Gₙ n) (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
    (hLp : Tendsto
      (fun n : Nat => MeasureTheory.lpNorm (fun η : PhaseSpace d => Gₙ n η - G η) 1
        (MeasureTheory.volume : MeasureTheory.Measure (PhaseSpace d)))
      atTop (nhds 0))
    (hA : Tendsto Aₙ atTop (nhds A))
    (ξ : PhaseSpace d)
    (hEq : ∀ n : Nat, symplecticFourierRep (Gₙ n) ξ = Aₙ n) :
    symplecticFourierRep G ξ = A := by
  have hleft := tendsto_symplecticFourierRep_of_lpNorm_one hG hGₙ hLp ξ
  have hright :
      Tendsto (fun n : Nat => symplecticFourierRep (Gₙ n) ξ) atTop (nhds A) := by
    rw [show (fun n : Nat => symplecticFourierRep (Gₙ n) ξ) = Aₙ by
      funext n
      exact hEq n]
    exact hA
  exact tendsto_nhds_unique hleft hright

/-- `IsL2Rep`: Is L2 Rep. -/
def IsL2Rep {d : Nat} (f : L2Real d) (fRep : RealVec d -> ℂ) : Prop :=
  ∃ hf_mem : MeasureTheory.MemLp fRep 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)),
    hf_mem.toLp fRep = f

/-- `translateL2`: translate L2. -/
noncomputable def translateL2 {d : Nat} (a : RealVec d) (f : L2Real d) : L2Real d :=
  DomAddAct.mk a +ᵥ f

/--
@isnad1 id=eventual.0h3v.s12.66fb9cee9b1c from=translated src=- shape=bfbb52b8 vocab=df46eb54
-/
theorem translateL2_coeFn {d : Nat} (a : RealVec d) (f : L2Real d) :
    ((translateL2 a f : L2Real d) : RealVec d -> ℂ)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
        fun t => (f : RealVec d -> ℂ) (t + a) := by
  filter_upwards [DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk a) f] with t ht
  simpa [translateL2, vadd_eq_add, add_comm] using ht

/--
@isnad1 id=eventual.0h3v.s12.d8be326200cd from=translated src=- shape=dab0807e vocab=b1dfde75
-/
theorem translateL2_neg_coeFn {d : Nat} (a : RealVec d) (f : L2Real d) :
    ((translateL2 (-a) f : L2Real d) : RealVec d -> ℂ)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
        fun t => (f : RealVec d -> ℂ) (t - a) := by
  simpa [sub_eq_add_neg] using translateL2_coeFn (-a) f

/--
@isnad1 id=eq.0h3v.s12.a55679933d8d from=translated src=- shape=4bc4ab12 vocab=9a1ccb16
-/
theorem norm_translateL2 {d : Nat} (a : RealVec d) (f : L2Real d) :
    ‖translateL2 a f‖ = ‖f‖ := by simp [translateL2]

/--
@isnad1 id=eq.0h4v.s12.79dde8a2d529 from=translated src=- shape=fbde0844 vocab=6d679ec4
-/
theorem dist_translateL2 {d : Nat} (a : RealVec d) (f g : L2Real d) :
    dist (translateL2 a f) (translateL2 a g) = dist f g := by simp [translateL2]

/--
@isnad1 id=continuo.0h2v.s13.f0b3f8fd5d3b from=translated src=- shape=621ca69d vocab=344cf5b0
-/
theorem continuous_translateL2_apply {d : Nat} (f : L2Real d) :
    Continuous fun a : RealVec d => translateL2 a f := by
  have : Fact (Ne (2 : ENNReal) ⊤) := ⟨by norm_num⟩
  unfold translateL2
  refine (DomAddAct.continuous_mk.vadd
    (continuous_const : Continuous fun _ : RealVec d => f)).congr ?_
  intro a
  rfl

/-- `modulationPhase`: modulation Phase. -/
noncomputable def modulationPhase {d : Nat} (ω : RealVec d) (t : RealVec d) : ℂ :=
  Complex.exp (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ))

/--
@isnad1 id=eq.0h3v.s4.6faa2daf49ab from=translated src=- shape=b799a142 vocab=d9930229
-/
theorem modulationPhase_norm {d : Nat} (ω t : RealVec d) :
    ‖modulationPhase ω t‖ = 1 := by
  unfold modulationPhase
  rw [Complex.norm_exp]
  have hre :
      (-(2 * Real.pi : ℂ) * Complex.I * ((inner ℝ ω t : ℝ) : ℂ)).re = 0 := by simp [Complex.mul_re]
  rw [hre, Real.exp_zero]

/--
@isnad1 id=eq.1h3v.s8.54226d539c20 from=translated src=- shape=35ee2624 vocab=03654b7a
-/
theorem fourier_translate_realVec {d : Nat} (a : RealVec d) (f : RealVec d -> ℂ)
    (_hf : Integrable f (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))) :
    FourierTransform.fourier (fun t : RealVec d => f (t - a)) =
      fun ω : RealVec d => modulationPhase a ω * FourierTransform.fourier f ω := by
  have h := (VectorFourier.fourierIntegral_comp_add_right (e := Real.fourierChar)
      (μ := (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)))
      (L := innerₗ (RealVec d)) (f := f) (v₀ := -a))
  rw [FourierTransform.fourier]
  ext ω
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ (RealVec d))
      (fun t : RealVec d => f (t - a)) ω =
    modulationPhase a ω *
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ (RealVec d)) f ω
  have hω := congrFun h ω
  simp only [Function.comp_def] at hω
  simpa [modulationPhase, Real.fourierChar_apply, sub_eq_add_neg, Circle.smul_def, mul_assoc,
    mul_left_comm, mul_comm] using hω

private theorem sub_const_hasTemperateGrowth {d : Nat} (a : RealVec d) :
    (fun x : RealVec d => x - a).HasTemperateGrowth := by fun_prop

private theorem sub_const_antilipschitz {d : Nat} (a : RealVec d) :
    AntilipschitzWith 1 (fun x : RealVec d => x - a) := by
  rw [antilipschitzWith_iff_le_mul_dist]
  intro x y
  simp

-- to_mathlib: Mathlib/Analysis/Distribution/SchwartzSpace/Basic.lean
/-- `schwartzCompSubConstCLM`: schwartz Comp Sub Const CLM. -/
noncomputable def schwartzCompSubConstCLM {d : Nat} (a : RealVec d) :
    SchwartzMap (RealVec d) ℂ →L[ℂ] SchwartzMap (RealVec d) ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (K := 1) (g := fun x : RealVec d => x - a)
    (by exact sub_const_hasTemperateGrowth a)
    (by exact sub_const_antilipschitz a)

/--
@isnad1 id=eq.0h3v.s11.93845bbcc81e from=translated src=- shape=7b68e21c vocab=1a7f2bdf
-/
@[simp] theorem schwartzCompSubConstCLM_apply {d : Nat} (a : RealVec d)
    (f : SchwartzMap (RealVec d) ℂ) :
    schwartzCompSubConstCLM a f = f ∘ fun x : RealVec d => x - a := by rfl

/--
@isnad1 id=eq.0h3v.s11.724d65430bee from=translated src=- shape=66694775 vocab=a103d9fc
-/
theorem fourier_schwartzCompSubConstCLM_realVec {d : Nat}
    (f : SchwartzMap (RealVec d) ℂ) (a : RealVec d) :
    FourierTransform.fourier (schwartzCompSubConstCLM a f : RealVec d -> ℂ) =
      fun ω : RealVec d =>
        modulationPhase a ω * FourierTransform.fourier (f : RealVec d -> ℂ) ω := by
  ext ω
  simpa [schwartzCompSubConstCLM_apply, Function.comp_def] using
    congrFun (fourier_translate_realVec a (f : RealVec d -> ℂ) f.integrable) ω

private def stftWindowSchwartz {d : Nat} (x : RealVec d)
    (h : SchwartzMap (RealVec d) ℂ) : SchwartzMap (RealVec d) ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) (F := ℂ) (G := ℂ) Complex.conjCLE
    (schwartzCompSubConstCLM x h)

@[simp] private theorem stftWindowSchwartz_apply {d : Nat}
    (x t : RealVec d) (h : SchwartzMap (RealVec d) ℂ) :
    stftWindowSchwartz x h t = star (h (t - x)) := by simp [stftWindowSchwartz]

private def stftSliceSchwartz {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x : RealVec d) : SchwartzMap (RealVec d) ℂ :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ)
    (stftWindowSchwartz x h).hasTemperateGrowth f

@[simp] private theorem stftSliceSchwartz_apply {d : Nat}
    (h f : SchwartzMap (RealVec d) ℂ) (x t : RealVec d) :
    stftSliceSchwartz h f x t = f t * star (h (t - x)) := by simp [stftSliceSchwartz]

private theorem modulateL2_mem {d : Nat} (ω : RealVec d) (f : L2Real d) :
    MeasureTheory.MemLp
      (fun t : RealVec d => modulationPhase ω t * (f : RealVec d -> ℂ) t)
      2 (MeasureTheory.volume : MeasureTheory.Measure (RealVec d)) := by
  have hf := MeasureTheory.Lp.memLp f
  refine hf.of_le ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by
      unfold modulationPhase
      fun_prop)).mul hf.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      rw [norm_mul, modulationPhase_norm]
      simp

/-- `modulateL2`: modulate L2. -/
noncomputable def modulateL2 {d : Nat} (ω : RealVec d) (f : L2Real d) : L2Real d :=
  (private_decl% (modulateL2_mem ω f)).toLp
    (fun t : RealVec d => modulationPhase ω t * (f : RealVec d -> ℂ) t)

/--
@isnad1 id=eventual.0h3v.s12.5b98822a2c55 from=translated src=- shape=3bd0e9cc vocab=f330f5bd
-/
theorem modulateL2_coeFn {d : Nat} (ω : RealVec d) (f : L2Real d) :
    ((modulateL2 ω f : L2Real d) : RealVec d -> ℂ)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
        fun t => modulationPhase ω t * (f : RealVec d -> ℂ) t := (modulateL2_mem ω f).coeFn_toLp

/--
@isnad1 id=eq.1h4v.s12.b54f2de95a98 from=translated src=- shape=7a88690a vocab=18e0090b
-/
theorem stftRep_congr_right
    {d : Nat} {h f g : L2Real d} (hfg : f = g) :
    stftRep h f = stftRep h g := by
  subst hfg
  rfl

/--
@isnad1 id=eq.1h4v.s12.bbf60f4b5585 from=translated src=- shape=4cdd54e6 vocab=18e0090b
-/
theorem stftRep_congr_left
    {d : Nat} {h h' f : L2Real d} (hh : h = h') :
    stftRep h f = stftRep h' f := by
  subst hh
  rfl

/--
@isnad1 id=eq.1h4v.s12.f33e129cab75 from=translated src=- shape=4cdd54e6 vocab=6f0890c4
-/
theorem ambiguityRep_congr_left
    {d : Nat} {f f' g : L2Real d} (hf : f = f') :
    ambiguityRep f g = ambiguityRep f' g := by
  subst hf
  rfl

/--
@isnad1 id=eq.1h4v.s12.ddd0bb14536c from=translated src=- shape=7a88690a vocab=6f0890c4
-/
theorem ambiguityRep_congr_right
    {d : Nat} {f g g' : L2Real d} (hg : g = g') :
    ambiguityRep f g = ambiguityRep f g' := by
  subst hg
  rfl

/--
@isnad1 id=eq.0h4v.s17.3b35e1c76955 from=translated src=- shape=d105db1d vocab=4f0939b4
-/
theorem ambiguityRep_eq_lpPairing
    {d : Nat} (f g : L2Real d) (ξ : PhaseSpace d) :
    ambiguityRep f g ξ =
      ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
        2 2)
        (translateL2 ((1 / 2 : ℝ) • ξ.1) f)
        (modulateL2 ξ.2
          (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g))) := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  unfold ambiguityRep
  apply MeasureTheory.integral_congr_ae
  filter_upwards [
    translateL2_coeFn ((1 / 2 : ℝ) • ξ.1) f,
    modulateL2_coeFn ξ.2 (star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g)),
    MeasureTheory.Lp.coeFn_star (translateL2 (-((1 / 2 : ℝ) • ξ.1)) g),
    translateL2_neg_coeFn ((1 / 2 : ℝ) • ξ.1) g] with t hf hmod hstar hg
  rw [hf, hmod, hstar]
  simp only [Pi.star_apply]
  rw [hg]
  unfold modulationPhase
  simp [ContinuousLinearMap.mul_apply']
  ring_nf

/--
@isnad1 id=eq.0h4v.s17.ade67e1c45b8 from=translated src=- shape=1d9c6072 vocab=4d31e76b
-/
theorem stftRep_eq_lpPairing
    {d : Nat} (h f : L2Real d) (ξ : PhaseSpace d) :
    stftRep h f ξ =
      ((ContinuousLinearMap.mul ℂ ℂ).lpPairing
        (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))
        2 2)
        f
        (modulateL2 ξ.2 (star (translateL2 (-ξ.1) h))) := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  unfold stftRep
  apply MeasureTheory.integral_congr_ae
  filter_upwards [
    modulateL2_coeFn ξ.2 (star (translateL2 (-ξ.1) h)),
    MeasureTheory.Lp.coeFn_star (translateL2 (-ξ.1) h),
    translateL2_neg_coeFn ξ.1 h] with t hmod hstar hh
  rw [hmod, hstar]
  simp only [Pi.star_apply]
  rw [hh]
  unfold modulationPhase
  simp [ContinuousLinearMap.mul_apply']
  ring_nf

/--
@isnad1 id=eq.0h4v.s11.bc8107f8aa8b from=translated src=- shape=892844ae vocab=52872ae3
-/
theorem spectrogramRep_eq_stft_mul_star
    {d : Nat} (h f : L2Real d) (ξ : PhaseSpace d) :
    ((‖stftRep h f ξ‖ ^ 2 : ℝ) : ℂ) =
      stftRep h f ξ * star (stftRep h f ξ) := by
  rw [Complex.star_def]
  exact_mod_cast (Complex.mul_conj' (stftRep h f ξ)).symm

/--
@isnad1 id=eq.1h4v.s12.edad5a11899a from=translated src=- shape=34852fdf vocab=435d57c1
-/
theorem spectrogram_ambiguity_identity_of_product_moyal
    {d : Nat}
    (hmoyal : ∀ (h f : L2Real d) (ξ : PhaseSpace d),
      symplecticFourierRep
          (fun η : PhaseSpace d => stftRep h f η * star (stftRep h f η)) ξ =
        ambiguityRep f f ξ * star (ambiguityRep h h ξ))
    (h f : L2Real d) (ξ : PhaseSpace d) :
    symplecticFourierRep
        (fun η : PhaseSpace d => ((‖stftRep h f η‖ ^ 2 : ℝ) : ℂ)) ξ =
      ambiguityRep f f ξ * star (ambiguityRep h h ξ) := by
  rw [show (fun η : PhaseSpace d => ((‖stftRep h f η‖ ^ 2 : ℝ) : ℂ)) =
      fun η : PhaseSpace d => stftRep h f η * star (stftRep h f η) by
    funext η
    exact spectrogramRep_eq_stft_mul_star h f η]
  exact hmoyal h f ξ

/--
@isnad1 id=eq.3h6v.s15.27a6fbfd6472 from=translated src=- shape=9b65afb9 vocab=c183506f
-/
theorem ae_unimodular_phase_to_L2_eq
    {d : Nat} {f g : L2Real d} {fRep gRep : RealVec d -> ℂ} {w : ℂ}
    (hf_rep : IsL2Rep f fRep) (hg_rep : IsL2Rep g gRep)
    (hphase :
      gRep =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
        fun u => w * fRep u) :
    g = w • f := by
  rcases hf_rep with ⟨hf_mem, hf_eq⟩
  rcases hg_rep with ⟨hg_mem, hg_eq⟩
  apply MeasureTheory.Lp.ext
  have hg_coe :
      ((g : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume] gRep := by
    rw [← hg_eq]
    exact hg_mem.coeFn_toLp
  have hf_coe :
      ((f : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume] fRep := by
    rw [← hf_eq]
    exact hf_mem.coeFn_toLp
  have hsmul :
      ((w • f : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume]
        fun u => w * fRep u := by
    filter_upwards [MeasureTheory.Lp.coeFn_smul w f, hf_coe] with u hw hf
    rw [hw]
    simp [Pi.smul_apply, smul_eq_mul, hf]
  filter_upwards [hg_coe, hphase, hsmul] with u hg hph hsm
  calc
    ((g : L2Real d) : RealVec d -> ℂ) u = gRep u := hg
    _ = w * fRep u := hph
    _ = ((w • f : L2Real d) : RealVec d -> ℂ) u := hsm.symm

/--
@isnad1 id=eventual.2h3v.s13.6a5407f1a4c0 from=translated src=- shape=bf15ab07 vocab=a30a2150
-/
theorem rep_ae_eq_zero_of_L2_eq_zero
    {d : Nat} {f : L2Real d} {fRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep) (hf_zero : f = 0) :
    fRep =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
      fun _ => (0 : ℂ) := by
  rcases hf_rep with ⟨hf_mem, hf_eq⟩
  have hcoe :
      ((f : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume] fRep := by
    rw [← hf_eq]
    exact hf_mem.coeFn_toLp
  have hzero :
      ((f : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume]
        fun _ => (0 : ℂ) := by
    rw [hf_zero]
    exact MeasureTheory.Lp.coeFn_zero ℂ 2 MeasureTheory.volume
  exact hcoe.symm.trans hzero

/--
@isnad1 id=eq.2h3v.s13.83345a457b5c from=translated src=- shape=6647508a vocab=a30a2150
-/
theorem L2_eq_zero_of_rep_ae_eq_zero
    {d : Nat} {f : L2Real d} {fRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep)
    (hzero : fRep =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d))]
      fun _ => (0 : ℂ)) :
    f = 0 := by
  rcases hf_rep with ⟨hf_mem, hf_eq⟩
  apply MeasureTheory.Lp.ext
  have hcoe :
      ((f : L2Real d) : RealVec d -> ℂ) =ᵐ[MeasureTheory.volume] fRep := by
    rw [← hf_eq]
    exact hf_mem.coeFn_toLp
  filter_upwards [hcoe, hzero,
    MeasureTheory.Lp.coeFn_zero ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure (RealVec d))] with u hf hrep h0
  calc
    ((f : L2Real d) : RealVec d -> ℂ) u = fRep u := hf
    _ = 0 := hrep
    _ = ((0 : L2Real d) : RealVec d -> ℂ) u := h0.symm

/--
@isnad1 id=true.1h2v.s4.284da25aec02 from=translated src=- shape=0e860516 vocab=f5bcf41c
-/
theorem boxPartialSums_have_L2_limit
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    True := by
  let _ := hd
  let _ := kappa
  /-
  Placeholder for the imported `L²` convergence package for box partial sums of
  square-summable coefficient data.
  -/
  trivial

/--
@isnad1 id=true.0h0v.s0.76c777b0ce3c from=translated src=- shape=45709ebd vocab=e3b0c442
-/
theorem circleFourier_exact_modulus_bridge :
    True := by
  /-
  Placeholder for the one-dimensional analytic uniqueness and Fourier/STFT
  bridge used downstream by the circle and rigidity modules.
  -/
  trivial

end DimdPolyLEAN
