/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Measure.RestrictedVolume
public import Tengoku

/-!
# Geometry for ball Poincare estimates

Adapted from CoarseGraining (LeanIntoHomogenization, 2026) with the author's
permission.  This file keeps the bounded convex-domain and affine-segment
interfaces needed by the ball estimate while using the established CKN carriers.
-/

@[expose] public section

namespace CKN

open MeasureTheory

/-- A coordinatewise bounded domain in the native finite-dimensional carrier. -/
def IsBoundedDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ∀ i, |x i| ≤ R

/--
@isnad1 id=isbounde.1h2v.s4.74b1a13670ed from=translated src=- shape=2b3152d1 vocab=360643ee
-/
theorem IsBoundedDomain.isBounded {d : ℕ} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) : Bornology.IsBounded U := by
  rcases hU with ⟨R, hR, hU⟩
  refine isBounded_iff_forall_norm_le.2 ⟨R, ?_⟩
  intro x hx
  refine (pi_norm_le_iff_of_nonneg hR.le).2 ?_
  intro i
  simpa [Real.norm_eq_abs] using hU x hx i

/--
@isnad1 id=lt.1h2v.s6.fd8694f2313f from=translated src=- shape=ce7090ed vocab=f0032c69
-/
theorem IsBoundedDomain.volume_lt_top {d : ℕ} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) : MeasureTheory.volume U < ⊤ :=
  hU.isBounded.measure_lt_top

/--
@isnad1 id=isfinite.1h2v.s6.e27f98a0dda0 from=translated src=- shape=f830b74e vocab=b4caa57f
-/
theorem IsBoundedDomain.isFiniteMeasure_restrict_volume
    {d : ℕ} {U : Set (Vec d)} (hU : IsBoundedDomain U) :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U) := by
  let _ : Fact (MeasureTheory.volume U < ⊤) := ⟨hU.volume_lt_top⟩
  infer_instance

/-- The average of a scalar function over a restricted volume measure. -/
noncomputable def integralAverage {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  MeasureTheory.average (MeasureTheory.volume.restrict U) u

/-- Measurable bounded domain on which the Sobolev estimates are formulated. -/
def IsSobolevRegularDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  MeasurableSet U ∧ IsBoundedDomain U

namespace IsSobolevRegularDomain

/--
@isnad1 id=measurab.1h2v.s4.c40ca5849edc from=translated src=- shape=2b3152d1 vocab=f3639b79
-/
theorem measurableSet {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U) :
    MeasurableSet U :=
  hU.1

/--
@isnad1 id=isbounde.1h2v.s3.91f3f2fea2b4 from=translated src=- shape=b87405bf vocab=45dfe536
-/
theorem isBoundedDomain {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U) :
    IsBoundedDomain U :=
  hU.2

/--
@isnad1 id=lt.1h2v.s6.00f5f616902e from=translated src=- shape=ce7090ed vocab=27b68d2a
-/
theorem volume_lt_top {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U) :
    MeasureTheory.volume U < ⊤ :=
  hU.isBoundedDomain.volume_lt_top

/--
@isnad1 id=isfinite.1h2v.s6.c85396155d95 from=translated src=- shape=f830b74e vocab=48baa46d
-/
theorem isFiniteMeasure_restrict_volume {d : ℕ} {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U) :=
  hU.isBoundedDomain.isFiniteMeasure_restrict_volume

end IsSobolevRegularDomain

/-- An open bounded convex domain in the native carrier. -/
def IsOpenBoundedConvexDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  IsOpen U ∧ IsBoundedDomain U ∧ Convex ℝ U

namespace IsOpenBoundedConvexDomain

/--
@isnad1 id=isopen.1h2v.s4.77c4cd2961a9 from=translated src=- shape=2b3152d1 vocab=fb2dd7c3
-/
theorem isOpen {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    IsOpen U :=
  hU.1

/--
@isnad1 id=isbounde.1h2v.s3.77a9990b059f from=translated src=- shape=b87405bf vocab=d7c65dbe
-/
theorem isBoundedDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) : IsBoundedDomain U :=
  hU.2.1

/--
@isnad1 id=convex.1h2v.s5.c808f422d983 from=translated src=- shape=e68b04ad vocab=87af50b4
-/
theorem convex {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    Convex ℝ U :=
  hU.2.2

/--
@isnad1 id=measurab.1h2v.s4.9bd83a9c6516 from=translated src=- shape=2b3152d1 vocab=c8450c43
-/
theorem measurableSet {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    MeasurableSet U :=
  hU.isOpen.measurableSet

/--
@isnad1 id=isfinite.1h2v.s6.692682e2aaf3 from=translated src=- shape=f830b74e vocab=9738c128
-/
theorem isFiniteMeasure_restrict_volume {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U) :=
  hU.isBoundedDomain.isFiniteMeasure_restrict_volume

/--
@isnad1 id=issobole.1h2v.s3.b6264c8127e5 from=translated src=- shape=b87405bf vocab=d3611055
-/
theorem isSobolevRegularDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) :
    IsSobolevRegularDomain U :=
  ⟨hU.measurableSet, hU.isBoundedDomain⟩

end IsOpenBoundedConvexDomain

/--
@isnad1 id=le.2h3v.s6.5bcfe8b6b4a6 from=translated src=- shape=80391658 vocab=999e3ef4
-/
theorem IsBoundedDomain.norm_le_choose {d : ℕ} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) {x : Vec d} (hx : x ∈ U) :
    ‖x‖ ≤ Classical.choose hU := by
  have hRpos : 0 < Classical.choose hU := (Classical.choose_spec hU).1
  have hR : ∀ z ∈ U, ∀ i, |z i| ≤ Classical.choose hU :=
    (Classical.choose_spec hU).2
  refine (pi_norm_le_iff_of_nonneg hRpos.le).2 ?_
  intro i
  simpa [Real.norm_eq_abs] using hR x hx i

/--
@isnad1 id=le.3h4v.s7.9ce1253767ef from=translated src=- shape=efdf7590 vocab=a496501a
-/
theorem IsBoundedDomain.norm_sub_le_two_mul_choose {d : ℕ} {U : Set (Vec d)}
    (hU : IsBoundedDomain U) {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) :
    ‖x - y‖ ≤ 2 * Classical.choose hU := by
  calc
    ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
    _ ≤ Classical.choose hU + Classical.choose hU :=
      add_le_add (hU.norm_le_choose hx) (hU.norm_le_choose hy)
    _ = 2 * Classical.choose hU := by ring

/-- Translate a set by a vector in the native finite-dimensional carrier. -/
def translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) : Set (Vec d) :=
  {x | ∃ y ∈ U, x = y + z}

/--
@isnad1 id=iff.0h4v.s5.4e5cee1e0b2e from=translated src=- shape=af81b11a vocab=77f41c2c
-/
theorem mem_translateSet_iff_sub_mem {d : ℕ} {z x : Vec d} {U : Set (Vec d)} :
    x ∈ translateSet z U ↔ x - z ∈ U := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [sub_eq_add_neg, add_assoc]
  · intro hx
    refine ⟨x - z, hx, ?_⟩
    ext i
    simp [sub_eq_add_neg, add_assoc]

/--
@isnad1 id=eq.0h3v.s5.a83f2f2380db from=translated src=- shape=e4657379 vocab=1d5f8541
-/
theorem preimage_addNeg_eq_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    (fun x : Vec d => x + -z) ⁻¹' U = translateSet z U := by
  ext x
  simp [mem_translateSet_iff_sub_mem, sub_eq_add_neg]

/--
@isnad1 id=eq.0h4v.s5.8f4f075431c0 from=translated src=- shape=b78343c3 vocab=dffecc48
-/
theorem translateSet_translateSet {d : ℕ} (z w : Vec d) (U : Set (Vec d)) :
    translateSet w (translateSet z U) = translateSet (z + w) U := by
  ext x
  constructor
  · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by simp [add_assoc]⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u + z, ⟨u, hu, rfl⟩, by simp [add_assoc]⟩

/--
@isnad1 id=eq.0h2v.s5.14781f45ad97 from=translated src=- shape=1d841b21 vocab=ab3bff8b
-/
@[simp] theorem translateSet_zero {d : ℕ} (U : Set (Vec d)) :
    translateSet (0 : Vec d) U = U := by
  ext x
  simp [translateSet]

/--
@isnad1 id=measurep.0h3v.s7.2b7e7a1b7c34 from=translated src=- shape=2ee2e5e6 vocab=47973a93
-/
theorem measurePreserving_subRight_restrict_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => x - z)
      (MeasureTheory.volume.restrict (translateSet z U))
      (MeasureTheory.volume.restrict U) := by
  let hμ : MeasurePreserving (fun x : Vec d => x + -z)
      (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) MeasureTheory.volume :=
    measurePreserving_add_right (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) (-z)
  simpa [preimage_addNeg_eq_translateSet (z := z) U, sub_eq_add_neg] using
    MeasurePreserving.restrict_preimage_emb hμ (Homeomorph.subRight z).measurableEmbedding U

/--
@isnad1 id=eq.0h3v.s5.f223dd0ce193 from=translated src=- shape=feed5c33 vocab=65d9934e
-/
theorem image_addRight_eq_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    (fun x : Vec d => x + z) '' U = translateSet z U := by
  ext x
  constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, rfl⟩

/--
@isnad1 id=measurep.0h3v.s7.7626d22b2abb from=translated src=- shape=d1263654 vocab=22db738c
-/
theorem measurePreserving_addRight_restrict_translateSet {d : ℕ} (z : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x : Vec d => x + z)
      (MeasureTheory.volume.restrict U)
      (MeasureTheory.volume.restrict (translateSet z U)) := by
  let hμ : MeasurePreserving (fun x : Vec d => x + z)
      (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) MeasureTheory.volume :=
    measurePreserving_add_right (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) z
  simpa [preimage_addNeg_eq_translateSet (z := z) U, image_addRight_eq_translateSet (z := z) U,
    sub_eq_add_neg] using
    MeasurePreserving.restrict_image_emb hμ (Homeomorph.addRight z).measurableEmbedding U

/--
@isnad1 id=eq.0h5v.s7.a3f74d5e3e54 from=translated src=- shape=75fb42f9 vocab=630ddbff
-/
theorem setIntegral_comp_subRight_translateSet {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ x in translateSet z U, f (x - z) ∂MeasureTheory.volume =
      ∫ y in U, f y ∂MeasureTheory.volume := by
  simpa using
    (measurePreserving_subRight_restrict_translateSet (d := d) z U).integral_comp
      (Homeomorph.subRight z).measurableEmbedding f

/--
@isnad1 id=eq.0h5v.s7.e00404d23d6f from=translated src=- shape=b0d0f85d vocab=67ce3b0e
-/
theorem setIntegral_comp_addRight_translateSet {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : Vec d) (U : Set (Vec d)) (f : Vec d → E) :
    ∫ y in U, f (y + z) ∂MeasureTheory.volume =
      ∫ x in translateSet z U, f x ∂MeasureTheory.volume := by
  simpa using
    (measurePreserving_addRight_restrict_translateSet (d := d) z U).integral_comp
      (Homeomorph.addRight z).measurableEmbedding f

/--
@isnad1 id=isopenbo.1h3v.s5.c544a89128e2 from=translated src=- shape=8d3978c2 vocab=6ca32fde
-/
theorem isOpenBoundedConvexDomain_ball {d : ℕ} (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    IsOpenBoundedConvexDomain (Metric.ball x₀ r) := by
  refine ⟨Metric.isOpen_ball, ?_, convex_ball x₀ r⟩
  refine ⟨‖x₀‖ + r + 1, ?_, ?_⟩
  · positivity
  · intro x hx i
    have hx' : ‖x - x₀‖ < r := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hxi : |x i| ≤ ‖x‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm x i
    have hnorm : ‖x‖ ≤ ‖x - x₀‖ + ‖x₀‖ := by
      calc
        ‖x‖ = ‖(x - x₀) + x₀‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
    linarith only [hxi, hx', hnorm]

/-- The affine map which sends the unit ball to the ball of radius `r`. -/
def ballAffineMap {d : ℕ} (x₀ : Vec d) (r : ℝ) (x : Vec d) : Vec d :=
  x₀ + r • x

/-- The point on the segment from `y` to `x` with parameter `t`. -/
noncomputable def segmentBlend {d : ℕ} (x : Vec d) (t : ℝ) (y : Vec d) : Vec d :=
  AffineMap.lineMap y x t

/--
@isnad1 id=eq.0h3v.s4.2b3f2602a9cc from=translated src=- shape=f183d97e vocab=2ef21e9c
-/
@[simp] theorem segmentBlend_zero {d : ℕ} (x y : Vec d) :
    segmentBlend x 0 y = y := by
  simp [segmentBlend]

/--
@isnad1 id=eq.0h3v.s4.59c19717f332 from=translated src=- shape=5fe9effd vocab=2ef21e9c
-/
@[simp] theorem segmentBlend_one {d : ℕ} (x y : Vec d) :
    segmentBlend x 1 y = x := by
  simp [segmentBlend]

/--
@isnad1 id=eq.0h4v.s6.370e3b81da73 from=translated src=- shape=60132e3c vocab=aeb2ed30
-/
theorem segmentBlend_eq_add_smul_sub {d : ℕ} (x y : Vec d) (t : ℝ) :
    segmentBlend x t y = y + t • (x - y) := by
  simpa [segmentBlend, add_comm] using (AffineMap.lineMap_apply_module' y x t)

/--
@isnad1 id=eq.0h3v.s4.3a59fa02a492 from=translated src=- shape=2809aa23 vocab=2ef21e9c
-/
@[simp] theorem segmentBlend_self {d : ℕ} (x : Vec d) (t : ℝ) :
    segmentBlend x t x = x := by
  simp [segmentBlend]

/--
@isnad1 id=mem.5h5v.s6.79ca7af19c9e from=translated src=- shape=a3da11d4 vocab=8e769cf0
-/
theorem segmentBlend_mem {d : ℕ} {U : Set (Vec d)} (hU : Convex ℝ U)
    {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segmentBlend x t y ∈ U := by
  simpa [segmentBlend] using hU.lineMap_mem hy hx ⟨ht0, ht1⟩

/--
@isnad1 id=mem.5h5v.s6.5a395dc9b1ab from=translated src=- shape=e66366d9 vocab=ac323b85
-/
theorem segmentBlend_mem_of_isOpenBoundedConvexDomain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {x y : Vec d}
    (hx : x ∈ U) (hy : y ∈ U) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    segmentBlend x t y ∈ U :=
  segmentBlend_mem hU.convex hx hy ht0 ht1

end CKN
