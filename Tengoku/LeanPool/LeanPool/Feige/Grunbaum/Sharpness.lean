/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.Grunbaum.Definitions
public import Tengoku

/-!
# Sharpness of Grünbaum's centroid halfspace constant

This file constructs the full-dimensional standard simplex and its sharp
centroid halfspace.  It computes the relevant centroid coordinate by the
layer-cake formula and proves that every universal project-level lower bound
is at most `grunbaumConstant`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace Grunbaum

/-- Euclidean space in an arbitrary (possibly zero) dimension.  The project
type `Euc d` is definitionally `SimplexE (d + 1)`. -/
abbrev SimplexE (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The sum of the coordinates, bundled as a continuous linear functional. -/
def coordinateSum (n : ℕ) : SimplexE n →L[ℝ] ℝ :=
  ∑ i : Fin n, (EuclideanSpace.proj i : SimplexE n →L[ℝ] ℝ)

/--
@isnad1 id=eq.0h2v.s8.ef47bcb56176 from=translated src=- shape=1f474824 vocab=6ca1e9ce
-/
@[simp]
theorem coordinateSum_apply (n : ℕ) (x : SimplexE n) :
    coordinateSum n x = ∑ i, x i := by
  simp [coordinateSum]

/-- The full-dimensional standard simplex `xᵢ ≥ 0`, `∑ xᵢ ≤ 1`. -/
def simplexSet (n : ℕ) : Set (SimplexE n) :=
  {x | (∀ i, 0 ≤ x i) ∧ coordinateSum n x ≤ 1}

/--
@isnad1 id=iff.0h2v.s8.0153bd7fdd54 from=translated src=- shape=b935d5a2 vocab=526d0f86
-/
@[simp]
theorem mem_simplexSet {n : ℕ} {x : SimplexE n} :
    x ∈ simplexSet n ↔ (∀ i, 0 ≤ x i) ∧ coordinateSum n x ≤ 1 :=
  Iff.rfl

/--
@isnad1 id=convex.0h1v.s6.20a91417d1e0 from=translated src=- shape=b70c6bb1 vocab=4a29e575
-/
theorem convex_simplexSet (n : ℕ) : Convex ℝ (simplexSet n) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i ↦ ?_, ?_⟩
  · change 0 ≤ a * x i + b * y i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · rw [map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    calc
      a * coordinateSum n x + b * coordinateSum n y
          ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by linarith

/--
@isnad1 id=isclosed.0h1v.s5.e1b03ac40969 from=translated src=- shape=fc2c1e2b vocab=e47a36fe
-/
theorem isClosed_simplexSet (n : ℕ) : IsClosed (simplexSet n) := by
  have hcoord : IsClosed {x : SimplexE n | ∀ i, 0 ≤ x i} := by
    rw [show {x : SimplexE n | ∀ i, 0 ≤ x i} =
        ⋂ i : Fin n, {x : SimplexE n | 0 ≤ x i} by ext x; simp]
    exact isClosed_iInter fun i ↦
      isClosed_le continuous_const (EuclideanSpace.proj i).continuous
  have hsum : IsClosed {x : SimplexE n | coordinateSum n x ≤ 1} :=
    isClosed_le (coordinateSum n).continuous continuous_const
  exact hcoord.inter hsum

/--
@isnad1 id=iscompac.0h1v.s5.d662266899a1 from=translated src=- shape=fc2c1e2b vocab=65065781
-/
theorem isCompact_simplexSet (n : ℕ) : IsCompact (simplexSet n) := by
  let e : SimplexE n ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hcube : IsCompact (e.symm '' Icc (0 : Fin n → ℝ) 1) :=
    isCompact_Icc.image e.symm.continuous
  refine hcube.of_isClosed_subset (isClosed_simplexSet n) ?_
  intro x hx
  refine ⟨e x, ?_, e.symm_apply_apply x⟩
  constructor
  · intro i
    change 0 ≤ x i
    exact hx.1 i
  · intro i
    change x i ≤ 1
    exact (Finset.single_le_sum (fun j _ ↦ hx.1 j) (Finset.mem_univ i)).trans
      (by simpa using hx.2)

/--
@isnad1 id=nonempty.0h1v.s2.84b349142bef from=translated src=- shape=fc2c1e2b vocab=64ed96b6
-/
theorem nonempty_simplexSet (n : ℕ) : (simplexSet n).Nonempty := by
  refine ⟨0, ?_⟩
  simp

/--
@isnad1 id=nonempty.0h1v.s5.c9186888aafa from=translated src=- shape=1bc48d19 vocab=e695ddd4
-/
theorem interior_simplexSet_nonempty (n : ℕ) :
    (interior (simplexSet n)).Nonempty := by
  rw [(convex_simplexSet n).interior_nonempty_iff_affineSpan_eq_top]
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hsub : insert 0 (Set.range b) ⊆ simplexSet n := by
    rintro x (rfl | ⟨i, rfl⟩)
    · simp
    · constructor
      · intro j
        change 0 ≤ (EuclideanSpace.basisFun (Fin n) ℝ i) j
        rw [EuclideanSpace.basisFun_apply, PiLp.single_apply]
        split_ifs <;> positivity
      · simp [b, coordinateSum_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  have htop : affineSpan ℝ (insert 0 (Set.range b)) = ⊤ := by
    apply SetLike.ext
    intro x
    change x ∈ (affineSpan ℝ (insert 0 (Set.range b)) : Set (SimplexE n)) ↔
      x ∈ (⊤ : AffineSubspace ℝ (SimplexE n))
    have hi := Set.ext_iff.mp
      (affineSpan_insert_zero (k := ℝ) (Set.range b)) x
    rw [hi, b.span_eq]
    simp
  exact top_unique (htop ▸ affineSpan_mono ℝ hsub)

/--
@isnad1 id=lt.0h1v.s8.34e3d9be32f6 from=translated src=- shape=6844b64b vocab=f8c4fa06
-/
theorem volume_simplexSet_pos (n : ℕ) :
    0 < volume (simplexSet n) :=
  measure_pos_of_nonempty_interior volume (interior_simplexSet_nonempty n)

/--
@isnad1 id=lt.0h1v.s7.d1edf5f35e54 from=translated src=- shape=8c96c685 vocab=be1ed5df
-/
theorem volumeReal_simplexSet_pos (n : ℕ) :
    0 < volume.real (simplexSet n) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (volume_simplexSet_pos n).ne'
    (isCompact_simplexSet n).measure_ne_top

/-- The part of the simplex below coordinate-sum level `t`. -/
def simplexCap (n : ℕ) (t : ℝ) : Set (SimplexE n) :=
  simplexSet n ∩ {x | coordinateSum n x ≤ t}

/--
@isnad1 id=eq.2h2v.s6.45c4f6477c74 from=translated src=- shape=2b37c7f4 vocab=623b6d97
-/
theorem simplexCap_eq_smul {n : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    simplexCap n t = t • simplexSet n := by
  ext x
  constructor
  · rintro ⟨hx, hxt⟩
    refine Set.mem_smul_set.mpr ⟨t⁻¹ • x, ?_, ?_⟩
    · constructor
      · intro i
        change 0 ≤ t⁻¹ * x i
        exact mul_nonneg (inv_nonneg.mpr ht0.le) (hx.1 i)
      · rw [map_smul]
        simp only [smul_eq_mul]
        calc
          t⁻¹ * coordinateSum n x ≤ t⁻¹ * t :=
            mul_le_mul_of_nonneg_left hxt (inv_nonneg.mpr ht0.le)
          _ = 1 := inv_mul_cancel₀ ht0.ne'
    · simp [smul_smul, ht0.ne']
  · intro hx
    rcases Set.mem_smul_set.mp hx with ⟨y, hy, rfl⟩
    refine ⟨?_, ?_⟩
    · constructor
      · intro i
        change 0 ≤ t * y i
        exact mul_nonneg ht0.le (hy.1 i)
      · rw [map_smul]
        simp only [smul_eq_mul]
        calc
          t * coordinateSum n y ≤ t * 1 :=
            mul_le_mul_of_nonneg_left hy.2 ht0.le
          _ ≤ 1 := by simpa using ht1
    · change coordinateSum n (t • y) ≤ t
      rw [map_smul]
      simp only [smul_eq_mul]
      simpa using mul_le_mul_of_nonneg_left hy.2 ht0.le

/--
@isnad1 id=eq.2h2v.s8.d51c1ea08dfe from=translated src=- shape=a06ca9a2 vocab=2f416747
-/
theorem volumeReal_simplexCap {n : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    volume.real (simplexCap n t) = t ^ n * volume.real (simplexSet n) := by
  rw [simplexCap_eq_smul ht0 ht1, measureReal_def,
    Measure.addHaar_smul_of_nonneg volume ht0.le]
  simp only [finrank_euclideanSpace_fin]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ht0.le n)]
  rw [measureReal_def]

/-- The exact strict-tail measure of the coordinate sum on the simplex.
@isnad1 id=eq.2h2v.s9.f021289c25f2 from=translated src=- shape=ff9517b2 vocab=a0dbc81b
-/
theorem restrictSimplex_tail {n : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (volume.restrict (simplexSet n)).real {x | t < coordinateSum n x} =
      (1 - t ^ n) * volume.real (simplexSet n) := by
  let ν := volume.restrict (simplexSet n)
  let A : Set (SimplexE n) := {x | coordinateSum n x ≤ t}
  have hA : MeasurableSet A :=
    isClosed_le (coordinateSum n).continuous continuous_const |>.measurableSet
  have hset : {x : SimplexE n | t < coordinateSum n x} = Aᶜ := by
    ext x
    simp [A]
  have hν : ν.real A = volume.real (simplexCap n t) := by
    simp only [ν, measureReal_restrict_apply hA]
    congr 1
    ext x
    simp [A, simplexCap, and_comm]
  let : IsFiniteMeasure ν := ⟨by
    change volume.restrict (simplexSet n) univ < ∞
    rw [Measure.restrict_apply_univ]
    exact (isCompact_simplexSet n).measure_lt_top⟩
  rw [hset, measureReal_compl hA, measureReal_restrict_apply_univ, hν,
    volumeReal_simplexCap ht0 ht1]
  ring

/-- The first moment of the coordinate sum over the standard simplex.
@isnad1 id=eq.0h1v.s9.ce9f05f732f9 from=translated src=- shape=2a519fff vocab=cecd071b
-/
theorem integral_coordinateSum (n : ℕ) :
    (∫ x in simplexSet n, coordinateSum n x ∂volume) =
      (n : ℝ) / ((n : ℝ) + 1) * volume.real (simplexSet n) := by
  let ν := volume.restrict (simplexSet n)
  let : IsFiniteMeasure ν := ⟨by
    change volume.restrict (simplexSet n) univ < ∞
    rw [Measure.restrict_apply_univ]
    exact (isCompact_simplexSet n).measure_lt_top⟩
  have hInt : Integrable (coordinateSum n) ν := by
    change IntegrableOn (coordinateSum n) (simplexSet n) volume
    exact (coordinateSum n).continuous.continuousOn.integrableOn_compact
      (isCompact_simplexSet n)
  have hnn : 0 ≤ᵐ[ν] coordinateSum n := by
    filter_upwards [ae_restrict_mem (isClosed_simplexSet n).measurableSet] with x hx
    rw [coordinateSum_apply]
    exact Finset.sum_nonneg fun i _ ↦ hx.1 i
  have hupper : coordinateSum n ≤ᵐ[ν] (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem (isClosed_simplexSet n).measurableSet] with x hx
    exact hx.2
  change (∫ x, coordinateSum n x ∂ν) =
    (n : ℝ) / ((n : ℝ) + 1) * volume.real (simplexSet n)
  rw [hInt.integral_eq_integral_meas_lt hnn]
  rw [setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      nullMeasurableSet_Ioi Ioc_subset_Ioi_self ?_]
  · rw [setIntegral_congr_fun measurableSet_Ioc fun t ht ↦
      restrictSimplex_tail ht.1 ht.2]
    rw [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_mul_const]
    congr 1
    have h_one : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have h_pow : IntervalIntegrable (fun t : ℝ ↦ t ^ n) volume 0 1 :=
      (continuous_id.pow n).intervalIntegrable 0 1
    rw [intervalIntegral.integral_sub h_one h_pow,
      intervalIntegral.integral_const, integral_pow]
    norm_num
    field_simp
    ring
  · apply Eventually.of_forall
    intro t ht
    have ht1 : 1 < t := by
      simp_all only [Set.mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le]
    have obs : ν {x | 1 < coordinateSum n x} = 0 := by
      rw [measure_eq_zero_iff_ae_notMem]
      filter_upwards [hupper] with x hx using not_lt.mpr hx
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff]
    exact Or.inl <| measure_mono_null
      (fun _ hx ↦ ht1.trans hx) obs

/-- The volume centroid of the standard simplex. -/
def simplexCentroid (n : ℕ) : SimplexE n :=
  ⨍ x in simplexSet n, x ∂volume

/-- The scalar coordinate needed to locate the sharp supporting hyperplane.
@isnad1 id=eq.0h1v.s8.5ad655b78ad6 from=translated src=- shape=c0ee7f82 vocab=33843c40
-/
theorem coordinateSum_simplexCentroid (n : ℕ) :
    coordinateSum n (simplexCentroid n) = (n : ℝ) / ((n : ℝ) + 1) := by
  have h_id : Integrable (fun x : SimplexE n ↦ x)
      (volume.restrict (simplexSet n)) := by
    change IntegrableOn (fun x : SimplexE n ↦ x) (simplexSet n) volume
    exact continuous_id.continuousOn.integrableOn_compact (isCompact_simplexSet n)
  have h_map :
      coordinateSum n (∫ x in simplexSet n, x ∂volume) =
        ∫ x in simplexSet n, coordinateSum n x ∂volume := by
    exact ((coordinateSum n).integral_comp_comm h_id).symm
  rw [simplexCentroid, setAverage_eq, map_smul, h_map, integral_coordinateSum]
  simp only [smul_eq_mul]
  field_simp [(volumeReal_simplexSet_pos n).ne']

/-- The sharp normalized coordinate-sum threshold in dimension `n`. -/
def sharpLevel (n : ℕ) : ℝ :=
  (n : ℝ) / ((n : ℝ) + 1)

/-- The simplex halfspace attaining the sharp Grünbaum fraction. -/
def sharpHalfspaceSet (n : ℕ) : Set (SimplexE n) :=
  {x | coordinateSum n x ≤ sharpLevel n}

/--
@isnad1 id=lt.1h1v.s4.4762962d19ae from=translated src=- shape=7f2e781e vocab=41445eb0
-/
theorem sharpLevel_pos {n : ℕ} (hn : 0 < n) : 0 < sharpLevel n := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact div_pos hn' (by positivity)

/--
@isnad1 id=le.0h1v.s3.1442cec250e5 from=translated src=- shape=a311c14d vocab=6f289cbc
-/
theorem sharpLevel_le_one (n : ℕ) : sharpLevel n ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
  norm_num

/--
@isnad1 id=mem.0h1v.s3.ce9f9d39a1ba from=translated src=- shape=58e3eb1f vocab=c115d0d7
-/
theorem simplexCentroid_mem_sharpHalfspaceSet (n : ℕ) :
    simplexCentroid n ∈ sharpHalfspaceSet n := by
  exact (coordinateSum_simplexCentroid n).le

/--
@isnad1 id=eq.1h1v.s8.9bb2d5683b53 from=translated src=- shape=3a7b5d05 vocab=d500faf7
-/
theorem sharpHalfspaceSet_volume_ratio {n : ℕ} (hn : 0 < n) :
    volume.real (simplexSet n ∩ sharpHalfspaceSet n) /
        volume.real (simplexSet n) =
      sharpLevel n ^ n := by
  rw [show simplexSet n ∩ sharpHalfspaceSet n = simplexCap n (sharpLevel n) by rfl,
    volumeReal_simplexCap (sharpLevel_pos hn) (sharpLevel_le_one n)]
  field_simp [(volumeReal_simplexSet_pos n).ne']

/-- The standard simplex, regarded as a full-dimensional body in project
dimension `d + 1`. -/
def simplexFullBody (d : ℕ) : FullDimensionalConvexBody d where
  carrier := simplexSet (d + 1)
  convex' := convex_simplexSet (d + 1)
  isCompact' := isCompact_simplexSet (d + 1)
  interior_nonempty' := interior_simplexSet_nonempty (d + 1)

/--
@isnad1 id=eq.0h1v.s4.3647f7b51133 from=translated src=- shape=04784e3b vocab=90a5b080
-/
theorem simplexFullBody_centroid (d : ℕ) :
    (simplexFullBody d).centroid = simplexCentroid (d + 1) :=
  rfl

/-- The sharp halfspace for the standard simplex. -/
def sharpClosedHalfspace (d : ℕ) : ClosedHalfspace d where
  normal := coordinateSum (d + 1)
  threshold := sharpLevel (d + 1)
  normal_ne_zero := by
    intro h
    let i : Fin (d + 1) := ⟨0, Nat.succ_pos d⟩
    have h' := congrArg
      (fun L : SimplexE (d + 1) →L[ℝ] ℝ ↦
        L (EuclideanSpace.single i 1)) h
    simp [coordinateSum_apply, PiLp.single_apply] at h'

/--
@isnad1 id=mem.0h1v.s3.22306ac94390 from=translated src=- shape=3803fbca vocab=6d1ba1a4
-/
theorem simplexFullBody_centroid_mem_sharpClosedHalfspace (d : ℕ) :
    (simplexFullBody d).centroid ∈ sharpClosedHalfspace d := by
  change coordinateSum (d + 1) (simplexCentroid (d + 1)) ≤
    sharpLevel (d + 1)
  exact (coordinateSum_simplexCentroid (d + 1)).le

/--
@isnad1 id=eq.0h1v.s4.112fcc4cbeea from=translated src=- shape=8abb8f81 vocab=42128285
-/
theorem sharpClosedHalfspace_ratio (d : ℕ) :
    halfspaceVolumeRatio (simplexFullBody d)
        (sharpClosedHalfspace d).normal
        (sharpClosedHalfspace d).threshold =
      grunbaumConstant d := by
  have h := sharpHalfspaceSet_volume_ratio (n := d + 1) (Nat.succ_pos d)
  rw [halfspaceVolumeRatio, ENNReal.toReal_div]
  change
    volume.real (simplexSet (d + 1) ∩ sharpHalfspaceSet (d + 1)) /
        volume.real (simplexSet (d + 1)) =
      grunbaumConstant d
  rw [h]
  simp only [sharpLevel, grunbaumConstant, Nat.cast_add, Nat.cast_one]
  congr 1
  ring

/-- `c` is a lower bound for every project convex body and every proper
closed halfspace containing its centroid. -/
def IsUniversalCentroidHalfspaceLowerBound (d : ℕ) (c : ℝ) : Prop :=
  ∀ (C : FullDimensionalConvexBody d) (H : ClosedHalfspace d),
    C.centroid ∈ H →
      c ≤ halfspaceVolumeRatio C H.normal H.threshold

/-- The simplex equality case shows that no universal centroid-halfspace
lower bound can exceed `grunbaumConstant d`.
@isnad1 id=le.1h2v.s3.20911db7d42f from=translated src=- shape=dedfc776 vocab=0bc49b22
-/
theorem universalCentroidHalfspaceLowerBound_le_grunbaumConstant
    {d : ℕ} {c : ℝ}
    (hc : IsUniversalCentroidHalfspaceLowerBound d c) :
    c ≤ grunbaumConstant d := by
  have h := hc (simplexFullBody d) (sharpClosedHalfspace d)
    (simplexFullBody_centroid_mem_sharpClosedHalfspace d)
  rwa [sharpClosedHalfspace_ratio d] at h

end Grunbaum
