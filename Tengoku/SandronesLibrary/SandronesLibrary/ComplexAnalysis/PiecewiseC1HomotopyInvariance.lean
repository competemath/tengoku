/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PiecewiseC1DyadicAlignment
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.IndexedOpenCoverSquareSubdivision
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.FiniteRawOpenPathGridBoundary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Path-integral invariance under continuous relative homotopies with piecewise-C1 boundary.

> **Entry**: complex-analysis.path-integral.piecewise-c1-homotopy-invariance -/

open Set Metric MeasureTheory
open scoped unitInterval

noncomputable section

open SandronesLibrary.Topology
open SandronesLibrary.ComplexAnalysis

namespace SandronesLibrary.ComplexAnalysis

open SandronesLibrary.Topology

/-- Final endpoint for the local-primitive square-grid route: a holomorphic
integrand has equal integrals on relatively homotopic piecewise-C1 paths.
@isnad1 id=eq.5h7v.s8.4a471b09cf5e from=translated src=- shape=42bcd10b vocab=bfaa6b22
-/
theorem pathIntegral_eq_of_piecewiseC1_homotopyWithin
    {U : Set ℂ} {f : ℂ → ℂ} {a b : ℂ} {gamma delta : Path a b}
    (hU : IsOpen U) (hf : HolomorphicOnTextbook f U)
    (hgamma : Path.PiecewiseC1 gamma) (hdelta : Path.PiecewiseC1 delta)
    (F : gamma.Homotopy delta)
    (hF : ∀ z : unitInterval × unitInterval, pathHomotopySquare F z ∈ U) :
    pathIntegral f gamma = pathIntegral f delta := by
  classical
  have hdiff : DifferentiableOn ℂ f U :=
    (holomorphicOnTextbook_iff_differentiableOn hU).mp hf
  obtain ⟨ngamma, hgammaDepth⟩ := hgamma.exists_dyadicC1AtDepth
  obtain ⟨ndelta, hdeltaDepth⟩ := hdelta.exists_dyadicC1AtDepth
  let minimumDepth := max ngamma ndelta
  have hr : ∀ z : unitInterval × unitInterval, ∃ ε > 0,
      Metric.ball (pathHomotopySquare F z) ε ⊆ U := by
    intro z
    exact Metric.mem_nhds_iff.mp (hU.mem_nhds (hF z))
  let radius : unitInterval × unitInterval → ℝ :=
    fun z ↦ Classical.choose (hr z)
  have hradius_pos : ∀ z, 0 < radius z :=
    fun z ↦ (Classical.choose_spec (hr z)).1
  have hradius_sub : ∀ z,
      Metric.ball (pathHomotopySquare F z) (radius z) ⊆ U :=
    fun z ↦ (Classical.choose_spec (hr z)).2
  let W : (unitInterval × unitInterval) → Set ℂ :=
    fun z ↦ Metric.ball (pathHomotopySquare F z) (radius z)
  have hWopen : ∀ z, IsOpen (W z) := fun z ↦ Metric.isOpen_ball
  have hWcover : ∀ z, ∃ k, pathHomotopySquare F z ∈ W k := by
    intro z
    exact ⟨z, Metric.mem_ball_self (hradius_pos z)⟩
  obtain ⟨n, hminimum, label, hcell⟩ :=
    exists_indexedOpenCoverSquareSubdivisionData_atLeastDepth
      (pathHomotopySquare F) W hWopen hWcover minimumDepth
  have hgammaDepthN : Path.DyadicC1AtDepth gamma n :=
    hgammaDepth.mono (le_trans (le_max_left _ _) hminimum)
  have hdeltaDepthN : Path.DyadicC1AtDepth delta n :=
    hdeltaDepth.mono (le_trans (le_max_right _ _) hminimum)
  let R : FiniteRawOpenPathGrid ℂ :=
    finiteRawOpenPathGrid_of_squareSubdivisionData
      (pathHomotopySquare F) (2 ^ n) (by positivity) W label hWopen hcell
      (pathHomotopySquare_horizontal_zero_piecewiseC1 F (2 ^ n) (by positivity))
      (pathHomotopySquare_horizontal_last_piecewiseC1 F (2 ^ n) (by positivity))
      (hgammaDepthN.pathHomotopySquare_vertical_zero_piecewiseC1 F)
      (hdeltaDepthN.pathHomotopySquare_vertical_last_piecewiseC1 F)
  have hexact : ∀ i j, Complex.IsExactOn f (R.cellSet i j) := by
    intro i j
    exact (hdiff.mono (hradius_sub (label i j))).isExactOn_ball
  have houter := finiteRawOpenPathGrid_outerBoundaryIntegral_eq_zero R hexact
  let mesh := fun (i : Fin (2 ^ n + 1)) ↦
    unitIntervalMeshPoint (2 ^ n) (by positivity) i
  have hgammaLeaf : ∀ i : Fin (2 ^ n), PathIntegrable f
      (gamma.subpath (mesh i.castSucc) (mesh i.succ)) := by
    intro i
    have hpiece : Path.PiecewiseC1
        (gamma.subpath (mesh i.castSucc) (mesh i.succ)) := by
      exact hgammaDepthN.dyadicSegment_piecewiseC1 i
    apply (admissiblePath_of_piecewiseC1 hpiece _ hdiff.continuousOn).pathIntegrable
    intro z hz
    obtain ⟨t, rfl⟩ := hz
    simpa [mesh, Path.subpath] using hF ((0 : unitInterval),
      Set.Icc.convexComb (mesh i.castSucc) (mesh i.succ) t)
  have hdeltaLeaf : ∀ i : Fin (2 ^ n), PathIntegrable f
      (delta.subpath (mesh i.castSucc) (mesh i.succ)) := by
    intro i
    have hpiece : Path.PiecewiseC1
        (delta.subpath (mesh i.castSucc) (mesh i.succ)) := by
      exact hdeltaDepthN.dyadicSegment_piecewiseC1 i
    apply (admissiblePath_of_piecewiseC1 hpiece _ hdiff.continuousOn).pathIntegrable
    intro z hz
    obtain ⟨t, rfl⟩ := hz
    simpa [mesh, Path.subpath] using hF ((1 : unitInterval),
      Set.Icc.convexComb (mesh i.castSucc) (mesh i.succ) t)
  let bottom : Fin (2 ^ n) → ℂ := fun i ↦
    pathIntegral f (squareGridHorizontalEdge (pathHomotopySquare F)
      (2 ^ n) (by positivity) i 0)
  let top : Fin (2 ^ n) → ℂ := fun i ↦
    pathIntegral f (squareGridHorizontalEdge (pathHomotopySquare F)
      (2 ^ n) (by positivity) i (Fin.last (2 ^ n)))
  let left : Fin (2 ^ n) → ℂ := fun i ↦
    pathIntegral f (squareGridVerticalEdge (pathHomotopySquare F)
      (2 ^ n) (by positivity) 0 i)
  let right : Fin (2 ^ n) → ℂ := fun i ↦
    pathIntegral f (squareGridVerticalEdge (pathHomotopySquare F)
      (2 ^ n) (by positivity) (Fin.last (2 ^ n)) i)
  apply pathIntegral_eq_of_dyadicOuterBoundary gamma delta n hgammaLeaf hdeltaLeaf
      bottom top left right
  · intro i
    have hsource : squareGridVertex (pathHomotopySquare F) (2 ^ n)
        (by positivity) i.castSucc 0 = a := by simp [squareGridVertex]
    have htarget : squareGridVertex (pathHomotopySquare F) (2 ^ n)
        (by positivity) i.succ 0 = a := by simp [squareGridVertex]
    have heq : ((Path.refl a).cast hsource htarget) =
        squareGridHorizontalEdge (pathHomotopySquare F) (2 ^ n)
          (by positivity) i 0 := by
      apply Path.ext
      funext t
      rw [Path.cast_coe]
      exact (squareGridHorizontalEdge_pathHomotopySquare_bottom F
        (2 ^ n) (by positivity) i t).symm
    dsimp [bottom]
    calc
      pathIntegral f (squareGridHorizontalEdge (pathHomotopySquare F)
          (2 ^ n) (by positivity) i 0) =
          pathIntegral f ((Path.refl a).cast hsource htarget) :=
        congrArg (pathIntegral f) heq.symm
      _ = 0 := by simp [pathIntegral]
  · intro i
    have hsource : squareGridVertex (pathHomotopySquare F) (2 ^ n)
        (by positivity) i.castSucc (Fin.last (2 ^ n)) = b := by
      simp [squareGridVertex]
    have htarget : squareGridVertex (pathHomotopySquare F) (2 ^ n)
        (by positivity) i.succ (Fin.last (2 ^ n)) = b := by
      simp [squareGridVertex]
    have heq : ((Path.refl b).cast hsource htarget) =
        squareGridHorizontalEdge (pathHomotopySquare F) (2 ^ n)
          (by positivity) i (Fin.last (2 ^ n)) := by
      apply Path.ext
      funext t
      rw [Path.cast_coe]
      exact (squareGridHorizontalEdge_pathHomotopySquare_top F
        (2 ^ n) (by positivity) i t).symm
    dsimp [top]
    calc
      pathIntegral f (squareGridHorizontalEdge (pathHomotopySquare F)
          (2 ^ n) (by positivity) i (Fin.last (2 ^ n))) =
          pathIntegral f ((Path.refl b).cast hsource htarget) :=
        congrArg (pathIntegral f) heq.symm
      _ = 0 := by simp [pathIntegral]
  · intro i
    have hsource : squareGridVertex (pathHomotopySquare F) (2 ^ n)
        (by positivity) 0 i.castSucc = gamma (mesh i.castSucc) := by
      simp [squareGridVertex, mesh]
    have htarget : squareGridVertex (pathHomotopySquare F) (2 ^ n)
        (by positivity) 0 i.succ = gamma (mesh i.succ) := by
      simp [squareGridVertex, mesh]
    have heq : ((gamma.subpath (mesh i.castSucc) (mesh i.succ)).cast
        hsource htarget) = squareGridVerticalEdge (pathHomotopySquare F)
          (2 ^ n) (by positivity) 0 i := by
      apply Path.ext
      funext t
      rw [Path.cast_coe]
      exact (squareGridVerticalEdge_pathHomotopySquare_left F
        (2 ^ n) (by positivity) i t).symm
    dsimp [left]
    calc
      pathIntegral f (squareGridVerticalEdge (pathHomotopySquare F)
          (2 ^ n) (by positivity) 0 i) =
          pathIntegral f ((gamma.subpath (mesh i.castSucc) (mesh i.succ)).cast
            hsource htarget) := congrArg (pathIntegral f) heq.symm
      _ = pathIntegral f (gamma.subpath (mesh i.castSucc) (mesh i.succ)) := by
        simp [pathIntegral]
      _ = pathIntegral f (gamma.subpath
          (unitIntervalMeshPoint (2 ^ n) (by positivity) i.castSucc)
          (unitIntervalMeshPoint (2 ^ n) (by positivity) i.succ)) := by
        rfl
  · intro i
    have hsource : squareGridVertex (pathHomotopySquare F) (2 ^ n)
        (by positivity) (Fin.last (2 ^ n)) i.castSucc = delta (mesh i.castSucc) := by
      simp [squareGridVertex, mesh]
    have htarget : squareGridVertex (pathHomotopySquare F) (2 ^ n)
        (by positivity) (Fin.last (2 ^ n)) i.succ = delta (mesh i.succ) := by
      simp [squareGridVertex, mesh]
    have heq : ((delta.subpath (mesh i.castSucc) (mesh i.succ)).cast
        hsource htarget) = squareGridVerticalEdge (pathHomotopySquare F)
          (2 ^ n) (by positivity) (Fin.last (2 ^ n)) i := by
      apply Path.ext
      funext t
      rw [Path.cast_coe]
      exact (squareGridVerticalEdge_pathHomotopySquare_right F
        (2 ^ n) (by positivity) i t).symm
    dsimp [right]
    calc
      pathIntegral f (squareGridVerticalEdge (pathHomotopySquare F)
          (2 ^ n) (by positivity) (Fin.last (2 ^ n)) i) =
          pathIntegral f ((delta.subpath (mesh i.castSucc) (mesh i.succ)).cast
            hsource htarget) := congrArg (pathIntegral f) heq.symm
      _ = pathIntegral f (delta.subpath (mesh i.castSucc) (mesh i.succ)) := by
        simp [pathIntegral]
      _ = pathIntegral f (delta.subpath
          (unitIntervalMeshPoint (2 ^ n) (by positivity) i.castSucc)
          (unitIntervalMeshPoint (2 ^ n) (by positivity) i.succ)) := by
        rfl
  · dsimp only [bottom, top, left, right]
    dsimp only [R, finiteRawOpenPathGrid_of_squareSubdivisionData] at houter
    exact houter

/-- A piecewise-C1 loop that is continuously null-homotopic inside the
holomorphy domain has zero integral.
@isnad1 id=eq.4h5v.s8.70fc587b3f53 from=translated src=- shape=32e345c2 vocab=b4a443aa
-/
theorem pathIntegral_eq_zero_of_piecewiseC1_nullHomotopyWithin
    {U : Set ℂ} {f : ℂ → ℂ} {a : ℂ} {gamma : Path a a}
    (hU : IsOpen U) (hf : HolomorphicOnTextbook f U)
    (hgamma : Path.PiecewiseC1 gamma) (F : gamma.Homotopy (Path.refl a))
    (hF : ∀ z : unitInterval × unitInterval, pathHomotopySquare F z ∈ U) :
    pathIntegral f gamma = 0 := by
  rw [pathIntegral_eq_of_piecewiseC1_homotopyWithin hU hf hgamma
    (Path.piecewiseC1_refl a) F hF]
  simp [pathIntegral]

end SandronesLibrary.ComplexAnalysis
