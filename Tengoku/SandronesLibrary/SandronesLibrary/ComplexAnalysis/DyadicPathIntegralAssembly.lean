/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PiecewiseC1Path
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.UnitIntervalMesh
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.PrimitiveFromPathIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Piecewise-C1 admissibility and finite dyadic reconstruction of path integrals.

> **Entry**: complex-analysis.path-integral.dyadic-assembly -/

open Set Metric MeasureTheory
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.ComplexAnalysis

open SandronesLibrary.Topology

/-- The topology-owned `PiecewiseC1` certificate,
together with range control and continuity on the ambient open set, produces
the existing complex-analysis `AdmissiblePath` certificate.-/
theorem admissiblePath_of_piecewiseC1
    {f : ℂ → ℂ} {U : Set ℂ} {a b : ℂ} {gamma : Path a b}
    (hgamma : Path.PiecewiseC1 gamma)
    (hrange : Set.range gamma ⊆ U) (hf : ContinuousOn f U) :
    AdmissiblePath f U gamma := by
  induction hgamma with
  | of_contDiffOn gamma regular =>
      apply AdmissiblePath.of_contDiffOn gamma hrange _ regular
      have hform : ContinuousOn (scalarOneForm f) U :=
        (ContinuousLinearMap.smulRightL ℂ ℂ ℂ
          (1 : ℂ →L[ℂ] ℂ)).continuous.comp_continuousOn hf
      exact hform.curveIntegrable_of_contDiffOn regular (fun t ↦ hrange ⟨t, rfl⟩)
  | trans gamma delta hgamma hdelta ihgamma ihdelta =>
      apply AdmissiblePath.trans
      · apply ihgamma
        intro z hz
        apply hrange
        rw [Path.trans_range]
        exact Set.mem_union_left _ hz
      · apply ihdelta
        intro z hz
        apply hrange
        rw [Path.trans_range]
        exact Set.mem_union_right _ hz
  | cast gamma hgamma hx hy ih =>
      subst hx
      subst hy
      simpa using ih (by
        intro z hz
        apply hrange
        simpa only [Path.cast_coe] using hz)

end SandronesLibrary.ComplexAnalysis

namespace SandronesLibrary.ComplexAnalysis

open SandronesLibrary.Topology

private def unitIntervalMidpoint : unitInterval := ⟨1 / 2, by norm_num⟩

private def unitIntervalLeftHalf (t : unitInterval) : unitInterval :=
  ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

private def unitIntervalRightHalf (t : unitInterval) : unitInterval :=
  ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

private theorem Path.subpath_zero_midpoint_subpath_apply
    {X : Type*} [TopologicalSpace X] {a b : X} (gamma : Path a b)
    (s t u : unitInterval) :
    (gamma.subpath 0 unitIntervalMidpoint).subpath s t u =
      gamma.subpath (unitIntervalLeftHalf s) (unitIntervalLeftHalf t) u := by
  change gamma (Set.Icc.convexComb 0 unitIntervalMidpoint
      (Set.Icc.convexComb s t u)) =
    gamma (Set.Icc.convexComb (unitIntervalLeftHalf s) (unitIntervalLeftHalf t) u)
  congr 1
  apply Subtype.ext
  simp [unitIntervalMidpoint, unitIntervalLeftHalf]
  ring

private theorem Path.subpath_midpoint_one_subpath_apply
    {X : Type*} [TopologicalSpace X] {a b : X} (gamma : Path a b)
    (s t u : unitInterval) :
    (gamma.subpath unitIntervalMidpoint 1).subpath s t u =
      gamma.subpath (unitIntervalRightHalf s) (unitIntervalRightHalf t) u := by
  change gamma (Set.Icc.convexComb unitIntervalMidpoint 1
      (Set.Icc.convexComb s t u)) =
    gamma (Set.Icc.convexComb (unitIntervalRightHalf s) (unitIntervalRightHalf t) u)
  congr 1
  apply Subtype.ext
  simp [unitIntervalMidpoint, unitIntervalRightHalf]
  ring

private theorem PathIntegrable.leftHalf_subpath
    {f : ℂ → ℂ} {a b : ℂ} (gamma : Path a b) (s t : unitInterval)
    (h : PathIntegrable f
      (gamma.subpath (unitIntervalLeftHalf s) (unitIntervalLeftHalf t))) :
    PathIntegrable f ((gamma.subpath 0 unitIntervalMidpoint).subpath s t) := by
  have hsource :
      (gamma.subpath 0 unitIntervalMidpoint) s = gamma (unitIntervalLeftHalf s) := by
    simpa using Path.subpath_zero_midpoint_subpath_apply gamma s t 0
  have htarget :
      (gamma.subpath 0 unitIntervalMidpoint) t = gamma (unitIntervalLeftHalf t) := by
    simpa using Path.subpath_zero_midpoint_subpath_apply gamma s t 1
  have heq :
      (((gamma.subpath (unitIntervalLeftHalf s) (unitIntervalLeftHalf t)).cast
        hsource htarget) : Path _ _) =
        (gamma.subpath 0 unitIntervalMidpoint).subpath s t := by
    apply Path.ext
    funext u
    rw [Path.cast_coe]
    exact (Path.subpath_zero_midpoint_subpath_apply gamma s t u).symm
  rw [← heq]
  exact h.cast hsource htarget

private theorem PathIntegrable.rightHalf_subpath
    {f : ℂ → ℂ} {a b : ℂ} (gamma : Path a b) (s t : unitInterval)
    (h : PathIntegrable f
      (gamma.subpath (unitIntervalRightHalf s) (unitIntervalRightHalf t))) :
    PathIntegrable f ((gamma.subpath unitIntervalMidpoint 1).subpath s t) := by
  have hsource :
      (gamma.subpath unitIntervalMidpoint 1) s = gamma (unitIntervalRightHalf s) := by
    simpa using Path.subpath_midpoint_one_subpath_apply gamma s t 0
  have htarget :
      (gamma.subpath unitIntervalMidpoint 1) t = gamma (unitIntervalRightHalf t) := by
    simpa using Path.subpath_midpoint_one_subpath_apply gamma s t 1
  have heq :
      (((gamma.subpath (unitIntervalRightHalf s) (unitIntervalRightHalf t)).cast
        hsource htarget) : Path _ _) =
        (gamma.subpath unitIntervalMidpoint 1).subpath s t := by
    apply Path.ext
    funext u
    rw [Path.cast_coe]
    exact (Path.subpath_midpoint_one_subpath_apply gamma s t u).symm
  rw [← heq]
  exact h.cast hsource htarget

private theorem pathIntegral_leftHalf_subpath
    {f : ℂ → ℂ} {a b : ℂ} (gamma : Path a b) (s t : unitInterval) :
    pathIntegral f ((gamma.subpath 0 unitIntervalMidpoint).subpath s t) =
      pathIntegral f
        (gamma.subpath (unitIntervalLeftHalf s) (unitIntervalLeftHalf t)) := by
  have hsource :
      (gamma.subpath 0 unitIntervalMidpoint) s = gamma (unitIntervalLeftHalf s) := by
    simpa using Path.subpath_zero_midpoint_subpath_apply gamma s t 0
  have htarget :
      (gamma.subpath 0 unitIntervalMidpoint) t = gamma (unitIntervalLeftHalf t) := by
    simpa using Path.subpath_zero_midpoint_subpath_apply gamma s t 1
  have heq :
      (((gamma.subpath (unitIntervalLeftHalf s) (unitIntervalLeftHalf t)).cast
        hsource htarget) : Path _ _) =
        (gamma.subpath 0 unitIntervalMidpoint).subpath s t := by
    apply Path.ext
    funext u
    rw [Path.cast_coe]
    exact (Path.subpath_zero_midpoint_subpath_apply gamma s t u).symm
  rw [← heq]
  simp [pathIntegral]

private theorem pathIntegral_rightHalf_subpath
    {f : ℂ → ℂ} {a b : ℂ} (gamma : Path a b) (s t : unitInterval) :
    pathIntegral f ((gamma.subpath unitIntervalMidpoint 1).subpath s t) =
      pathIntegral f
        (gamma.subpath (unitIntervalRightHalf s) (unitIntervalRightHalf t)) := by
  have hsource :
      (gamma.subpath unitIntervalMidpoint 1) s = gamma (unitIntervalRightHalf s) := by
    simpa using Path.subpath_midpoint_one_subpath_apply gamma s t 0
  have htarget :
      (gamma.subpath unitIntervalMidpoint 1) t = gamma (unitIntervalRightHalf t) := by
    simpa using Path.subpath_midpoint_one_subpath_apply gamma s t 1
  have heq :
      (((gamma.subpath (unitIntervalRightHalf s) (unitIntervalRightHalf t)).cast
        hsource htarget) : Path _ _) =
        (gamma.subpath unitIntervalMidpoint 1).subpath s t := by
    apply Path.ext
    funext u
    rw [Path.cast_coe]
    exact (Path.subpath_midpoint_one_subpath_apply gamma s t u).symm
  rw [← heq]
  simp [pathIntegral]

private def integralDyadicMeshPoint (n : ℕ) (i : Fin (2 ^ n + 1)) : unitInterval :=
  unitIntervalMeshPoint (2 ^ n) (by positivity) i

private def integralDyadicLeftSegmentIndex (n : ℕ) (i : Fin (2 ^ n)) :
    Fin (2 ^ (n + 1)) :=
  ⟨i, by
    calc
      i.val < 2 ^ n := i.isLt
      _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (n := 2) (by norm_num) (Nat.le_succ n)⟩

private def integralDyadicRightSegmentIndex (n : ℕ) (i : Fin (2 ^ n)) :
    Fin (2 ^ (n + 1)) :=
  ⟨2 ^ n + i, by simp only [pow_succ]; omega⟩

private theorem sum_dyadic_succ_split
    {G : Type*} [AddCommMonoid G] (n : ℕ)
    (value : Fin (2 ^ (n + 1)) → G) :
    (∑ k, value k) =
      (∑ i : Fin (2 ^ n), value (integralDyadicLeftSegmentIndex n i)) +
      ∑ i : Fin (2 ^ n), value (integralDyadicRightSegmentIndex n i) := by
  let e : Fin (2 ^ n + 2 ^ n) ≃ Fin (2 ^ (n + 1)) :=
    finCongr (by simp [pow_succ, Nat.mul_two])
  have hsplit := Fin.sum_univ_add (fun k : Fin (2 ^ n + 2 ^ n) ↦ value (e k))
  calc
    (∑ k, value k) = ∑ k : Fin (2 ^ n + 2 ^ n), value (e k) :=
      (e.sum_comp value).symm
    _ = (∑ i : Fin (2 ^ n), value (e (Fin.castAdd (2 ^ n) i))) +
        ∑ i : Fin (2 ^ n), value (e (Fin.natAdd (2 ^ n) i)) := hsplit
    _ = (∑ i : Fin (2 ^ n), value (integralDyadicLeftSegmentIndex n i)) +
        ∑ i : Fin (2 ^ n), value (integralDyadicRightSegmentIndex n i) := by
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i hi
        congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        congr 1

@[simp] private theorem integralDyadicMeshPoint_left_castSucc
    (n : ℕ) (i : Fin (2 ^ n)) :
    integralDyadicMeshPoint (n + 1)
        (integralDyadicLeftSegmentIndex n i).castSucc =
      unitIntervalLeftHalf (integralDyadicMeshPoint n i.castSucc) := by
  apply Subtype.ext
  simp only [integralDyadicMeshPoint, integralDyadicLeftSegmentIndex,
    unitIntervalMeshPoint, unitIntervalLeftHalf]
  push_cast
  simp only [Fin.val_castSucc]
  change (i.val : ℝ) / (2 : ℝ) ^ (n + 1) =
    ((i.val : ℝ) / (2 : ℝ) ^ n) / 2
  rw [pow_succ]
  field_simp

@[simp] private theorem integralDyadicMeshPoint_left_succ
    (n : ℕ) (i : Fin (2 ^ n)) :
    integralDyadicMeshPoint (n + 1)
        (integralDyadicLeftSegmentIndex n i).succ =
      unitIntervalLeftHalf (integralDyadicMeshPoint n i.succ) := by
  apply Subtype.ext
  simp only [integralDyadicMeshPoint, integralDyadicLeftSegmentIndex,
    unitIntervalMeshPoint, unitIntervalLeftHalf, Fin.val_succ]
  push_cast
  change ((i.val : ℝ) + 1) / (2 : ℝ) ^ (n + 1) =
    (((i.val : ℝ) + 1) / (2 : ℝ) ^ n) / 2
  rw [pow_succ]
  field_simp

@[simp] private theorem integralDyadicMeshPoint_right_castSucc
    (n : ℕ) (i : Fin (2 ^ n)) :
    integralDyadicMeshPoint (n + 1)
        (integralDyadicRightSegmentIndex n i).castSucc =
      unitIntervalRightHalf (integralDyadicMeshPoint n i.castSucc) := by
  apply Subtype.ext
  simp only [integralDyadicMeshPoint, integralDyadicRightSegmentIndex,
    unitIntervalMeshPoint, unitIntervalRightHalf]
  push_cast
  simp only [Fin.val_castSucc]
  push_cast
  change (((2 : ℝ) ^ n + i.val) / (2 : ℝ) ^ (n + 1)) =
    (((i.val : ℝ) / (2 : ℝ) ^ n) + 1) / 2
  rw [pow_succ]
  field_simp
  ring

@[simp] private theorem integralDyadicMeshPoint_right_succ
    (n : ℕ) (i : Fin (2 ^ n)) :
    integralDyadicMeshPoint (n + 1)
        (integralDyadicRightSegmentIndex n i).succ =
      unitIntervalRightHalf (integralDyadicMeshPoint n i.succ) := by
  apply Subtype.ext
  simp only [integralDyadicMeshPoint, integralDyadicRightSegmentIndex,
    unitIntervalMeshPoint, unitIntervalRightHalf, Fin.val_succ]
  push_cast
  change (((2 : ℝ) ^ n + i.val + 1) / (2 : ℝ) ^ (n + 1)) =
    ((((i.val : ℝ) + 1) / (2 : ℝ) ^ n) + 1) / 2
  rw [pow_succ]
  field_simp
  ring

/-- The two midpoint subpaths concatenate strictly back to the original path,
up to its canonical endpoint cast.-/
private theorem Path.midpointSubpaths_trans
    {X : Type*} [TopologicalSpace X] {a b : X} (gamma : Path a b) :
    (gamma.subpath 0 unitIntervalMidpoint).trans
        (gamma.subpath unitIntervalMidpoint 1) =
      gamma.cast gamma.source gamma.target := by
  apply Path.ext
  funext t
  rw [Path.cast_coe, Path.trans_apply]
  split_ifs with ht
  · change gamma (Set.Icc.convexComb 0 unitIntervalMidpoint
        ⟨2 * (t : ℝ), by constructor <;> nlinarith [t.2.1, ht]⟩) = gamma t
    congr 1
    apply Subtype.ext
    simp [unitIntervalMidpoint]
    ring
  · change gamma (Set.Icc.convexComb unitIntervalMidpoint 1
        ⟨2 * (t : ℝ) - 1, by
          constructor <;> nlinarith [not_le.1 ht, t.2.2]⟩) = gamma t
    congr 1
    apply Subtype.ext
    simp [unitIntervalMidpoint]
    ring

/-- One dyadic bisection is additive for path integrals. This uses only strict
concatenation and `pathIntegral_trans`, not homotopy invariance.-/
private theorem pathIntegral_eq_midpointSubpaths_add
    {f : ℂ → ℂ} {a b : ℂ} (gamma : Path a b)
    (hleft : PathIntegrable f (gamma.subpath 0 unitIntervalMidpoint))
    (hright : PathIntegrable f (gamma.subpath unitIntervalMidpoint 1)) :
    pathIntegral f gamma =
      pathIntegral f (gamma.subpath 0 unitIntervalMidpoint) +
        pathIntegral f (gamma.subpath unitIntervalMidpoint 1) := by
  rw [← pathIntegral_trans f _ _ hleft hright,
    Path.midpointSubpaths_trans]
  simp [pathIntegral]

/-- Integrability on every elementary interval of a dyadic grid assembles to
integrability on the original path.-/
private theorem pathIntegrable_of_dyadicSubpaths :
    ∀ (n : ℕ) {f : ℂ → ℂ} {a b : ℂ} (gamma : Path a b),
      (∀ i : Fin (2 ^ n), PathIntegrable f
        (gamma.subpath (integralDyadicMeshPoint n i.castSucc)
          (integralDyadicMeshPoint n i.succ))) →
      PathIntegrable f gamma
  | 0, f, a, b, gamma, h => by
      have h0 := h (0 : Fin 1)
      have hstart : integralDyadicMeshPoint 0 (Fin.castSucc (0 : Fin 1)) = 0 := by
        apply Subtype.ext
        norm_num [integralDyadicMeshPoint, unitIntervalMeshPoint]
      have hend : integralDyadicMeshPoint 0 (Fin.succ (0 : Fin 1)) = 1 := by
        apply Subtype.ext
        norm_num [integralDyadicMeshPoint, unitIntervalMeshPoint]
      rw [hstart, hend, Path.subpath_zero_one] at h0
      simpa [PathIntegrable] using h0
  | n + 1, f, a, b, gamma, h => by
      have hleftLeaves : ∀ i : Fin (2 ^ n), PathIntegrable f
          ((gamma.subpath 0 unitIntervalMidpoint).subpath
            (integralDyadicMeshPoint n i.castSucc)
            (integralDyadicMeshPoint n i.succ)) := by
        intro i
        apply PathIntegrable.leftHalf_subpath gamma
        have hi := h (integralDyadicLeftSegmentIndex n i)
        rw [integralDyadicMeshPoint_left_castSucc,
          integralDyadicMeshPoint_left_succ] at hi
        exact hi
      have hrightLeaves : ∀ i : Fin (2 ^ n), PathIntegrable f
          ((gamma.subpath unitIntervalMidpoint 1).subpath
            (integralDyadicMeshPoint n i.castSucc)
            (integralDyadicMeshPoint n i.succ)) := by
        intro i
        apply PathIntegrable.rightHalf_subpath gamma
        have hi := h (integralDyadicRightSegmentIndex n i)
        rw [integralDyadicMeshPoint_right_castSucc,
          integralDyadicMeshPoint_right_succ] at hi
        exact hi
      have hleft := pathIntegrable_of_dyadicSubpaths n
        (gamma.subpath 0 unitIntervalMidpoint) hleftLeaves
      have hright := pathIntegrable_of_dyadicSubpaths n
        (gamma.subpath unitIntervalMidpoint 1) hrightLeaves
      have htrans := hleft.trans hright
      rw [Path.midpointSubpaths_trans] at htrans
      simpa [PathIntegrable] using htrans

/-- The path integral is the finite sum of the integrals over all elementary
subpaths of any dyadic grid, assuming those elementary subpaths are
integrable.-/
private theorem pathIntegral_eq_sum_dyadicSubpaths :
    ∀ (n : ℕ) {f : ℂ → ℂ} {a b : ℂ} (gamma : Path a b)
      (_hleaf : ∀ i : Fin (2 ^ n), PathIntegrable f
        (gamma.subpath (integralDyadicMeshPoint n i.castSucc)
          (integralDyadicMeshPoint n i.succ))),
      pathIntegral f gamma =
        ∑ i : Fin (2 ^ n), pathIntegral f
          (gamma.subpath (integralDyadicMeshPoint n i.castSucc)
            (integralDyadicMeshPoint n i.succ))
  | 0, f, a, b, gamma, _hleaf => by
      have hstart : integralDyadicMeshPoint 0 (0 : Fin 2) = 0 := by
        apply Subtype.ext
        norm_num [integralDyadicMeshPoint, unitIntervalMeshPoint]
      have hend : integralDyadicMeshPoint 0 (1 : Fin 2) = 1 := by
        apply Subtype.ext
        norm_num [integralDyadicMeshPoint, unitIntervalMeshPoint]
      let value : Fin (2 ^ 0) → ℂ := fun i ↦ pathIntegral f
        (gamma.subpath (integralDyadicMeshPoint 0 i.castSucc)
          (integralDyadicMeshPoint 0 i.succ))
      have hsum : (∑ i, value i) = value (0 : Fin 1) := by
        exact Fin.sum_univ_one value
      change pathIntegral f gamma = ∑ i, value i
      rw [hsum]
      dsimp [value]
      rw [hstart, hend, Path.subpath_zero_one]
      simp [pathIntegral]
  | n + 1, f, a, b, gamma, hleaf => by
      have hleftLeaves : ∀ i : Fin (2 ^ n), PathIntegrable f
          ((gamma.subpath 0 unitIntervalMidpoint).subpath
            (integralDyadicMeshPoint n i.castSucc)
            (integralDyadicMeshPoint n i.succ)) := by
        intro i
        apply PathIntegrable.leftHalf_subpath gamma
        have hi := hleaf (integralDyadicLeftSegmentIndex n i)
        rw [integralDyadicMeshPoint_left_castSucc,
          integralDyadicMeshPoint_left_succ] at hi
        exact hi
      have hrightLeaves : ∀ i : Fin (2 ^ n), PathIntegrable f
          ((gamma.subpath unitIntervalMidpoint 1).subpath
            (integralDyadicMeshPoint n i.castSucc)
            (integralDyadicMeshPoint n i.succ)) := by
        intro i
        apply PathIntegrable.rightHalf_subpath gamma
        have hi := hleaf (integralDyadicRightSegmentIndex n i)
        rw [integralDyadicMeshPoint_right_castSucc,
          integralDyadicMeshPoint_right_succ] at hi
        exact hi
      have hleftIntegrable := pathIntegrable_of_dyadicSubpaths n
        (gamma.subpath 0 unitIntervalMidpoint) hleftLeaves
      have hrightIntegrable := pathIntegrable_of_dyadicSubpaths n
        (gamma.subpath unitIntervalMidpoint 1) hrightLeaves
      rw [pathIntegral_eq_midpointSubpaths_add gamma hleftIntegrable hrightIntegrable,
        pathIntegral_eq_sum_dyadicSubpaths n
          (gamma.subpath 0 unitIntervalMidpoint) hleftLeaves,
        pathIntegral_eq_sum_dyadicSubpaths n
          (gamma.subpath unitIntervalMidpoint 1) hrightLeaves,
        sum_dyadic_succ_split]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integralDyadicMeshPoint_left_castSucc,
          integralDyadicMeshPoint_left_succ]
        exact pathIntegral_leftHalf_subpath gamma _ _
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integralDyadicMeshPoint_right_castSucc,
          integralDyadicMeshPoint_right_succ]
        exact pathIntegral_rightHalf_subpath gamma _ _

/-- Final scalar assembly for a dyadic homotopy grid: if the two horizontal
outer sides contribute zero and the oriented outer-boundary sum vanishes, then
the complete source and target path integrals agree.-/
theorem pathIntegral_eq_of_dyadicOuterBoundary
    {f : ℂ → ℂ} {a b : ℂ} (gamma delta : Path a b) (n : ℕ)
    (hgammaLeaf : ∀ i : Fin (2 ^ n), PathIntegrable f
      (gamma.subpath (unitIntervalMeshPoint (2 ^ n) (by positivity) i.castSucc)
        (unitIntervalMeshPoint (2 ^ n) (by positivity) i.succ)))
    (hdeltaLeaf : ∀ i : Fin (2 ^ n), PathIntegrable f
      (delta.subpath (unitIntervalMeshPoint (2 ^ n) (by positivity) i.castSucc)
        (unitIntervalMeshPoint (2 ^ n) (by positivity) i.succ)))
    (bottom top left right : Fin (2 ^ n) → ℂ)
    (hbottom : ∀ i, bottom i = 0) (htop : ∀ i, top i = 0)
    (hleft : ∀ i, left i = pathIntegral f
      (gamma.subpath (unitIntervalMeshPoint (2 ^ n) (by positivity) i.castSucc)
        (unitIntervalMeshPoint (2 ^ n) (by positivity) i.succ)))
    (hright : ∀ i, right i = pathIntegral f
      (delta.subpath (unitIntervalMeshPoint (2 ^ n) (by positivity) i.castSucc)
        (unitIntervalMeshPoint (2 ^ n) (by positivity) i.succ)))
    (houter : (∑ i, (bottom i - top i)) + ∑ i, (right i - left i) = 0) :
    pathIntegral f gamma = pathIntegral f delta := by
  have hgammaLeaf' : ∀ i : Fin (2 ^ n), PathIntegrable f
      (gamma.subpath (integralDyadicMeshPoint n i.castSucc)
        (integralDyadicMeshPoint n i.succ)) := by
    simpa [integralDyadicMeshPoint] using hgammaLeaf
  have hdeltaLeaf' : ∀ i : Fin (2 ^ n), PathIntegrable f
      (delta.subpath (integralDyadicMeshPoint n i.castSucc)
        (integralDyadicMeshPoint n i.succ)) := by
    simpa [integralDyadicMeshPoint] using hdeltaLeaf
  have hleft' : ∀ i, left i = pathIntegral f
      (gamma.subpath (integralDyadicMeshPoint n i.castSucc)
        (integralDyadicMeshPoint n i.succ)) := by
    simpa [integralDyadicMeshPoint] using hleft
  have hright' : ∀ i, right i = pathIntegral f
      (delta.subpath (integralDyadicMeshPoint n i.castSucc)
        (integralDyadicMeshPoint n i.succ)) := by
    simpa [integralDyadicMeshPoint] using hright
  simp only [hbottom, htop, sub_self, Finset.sum_const_zero, zero_add,
    hright', hleft', Finset.sum_sub_distrib] at houter
  rw [← pathIntegral_eq_sum_dyadicSubpaths n delta hdeltaLeaf',
    ← pathIntegral_eq_sum_dyadicSubpaths n gamma hgammaLeaf'] at houter
  exact sub_eq_zero.mp houter |>.symm

end SandronesLibrary.ComplexAnalysis
