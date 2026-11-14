/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PiecewiseC1Path
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.HomotopySquareGrid

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Dyadic alignment certificates for the existing piecewise-C1 path carrier.

> **Entry**: topology.homotopy.piecewise-c1-dyadic-alignment -/

open Set
open scoped unitInterval

noncomputable section

namespace SandronesLibrary.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A proof-relevant alignment certificate saying that every binary breakpoint
used to construct `gamma` is visible at dyadic depth `n`. This remains a `Prop`;
it is not a second path type or a replacement for `Path.PiecewiseC1`.-/
inductive Path.DyadicC1AtDepth : {x y : E} → Path x y → ℕ → Prop
  | of_contDiffOn {x y : E} (gamma : Path x y)
      (regular : ContDiffOn ℝ 1 gamma.extend (Icc 0 1)) (n : ℕ) :
      Path.DyadicC1AtDepth gamma n
  | trans {x y z : E} {gamma : Path x y} {delta : Path y z} {n : ℕ}
      (hgamma : Path.DyadicC1AtDepth gamma n)
      (hdelta : Path.DyadicC1AtDepth delta n) :
      Path.DyadicC1AtDepth (gamma.trans delta) (n + 1)
  | cast {x y x' y' : E} {gamma : Path x y} {n : ℕ}
      (hgamma : Path.DyadicC1AtDepth gamma n) (hx : x' = x) (hy : y' = y) :
      Path.DyadicC1AtDepth (gamma.cast hx hy) n

/-- Increasing the dyadic depth preserves an alignment certificate.-/
theorem Path.DyadicC1AtDepth.mono
    {x y : E} {gamma : Path x y} {n m : ℕ}
    (hgamma : Path.DyadicC1AtDepth gamma n) (hnm : n ≤ m) :
    Path.DyadicC1AtDepth gamma m := by
  induction hgamma generalizing m with
  | of_contDiffOn gamma regular n =>
      exact .of_contDiffOn gamma regular m
  | @trans x y z gamma delta n hgamma hdelta ihgamma ihdelta =>
      cases m with
      | zero => omega
      | succ m =>
          apply Path.DyadicC1AtDepth.trans
          · exact ihgamma (by omega)
          · exact ihdelta (by omega)
  | @cast x y x' y' gamma n hgamma hx hy ih =>
      exact .cast (ih hnm) hx hy

/-- Forgetting the alignment depth recovers the original piecewise-C1
predicate.-/
theorem Path.DyadicC1AtDepth.piecewiseC1
    {x y : E} {gamma : Path x y} {n : ℕ}
    (hgamma : Path.DyadicC1AtDepth gamma n) : Path.PiecewiseC1 gamma := by
  induction hgamma with
  | of_contDiffOn gamma regular n =>
      exact .of_contDiffOn gamma regular
  | trans hgamma hdelta ihgamma ihdelta =>
      exact .trans _ _ ihgamma ihdelta
  | cast hgamma hx hy ih =>
      exact .cast _ ih hx hy

/-- Every value of the existing `PiecewiseC1 : Prop` has some finite common
dyadic alignment depth. The witness is existential because Lean correctly
forbids computing data directly by eliminating a proof in `Prop`.-/
theorem Path.PiecewiseC1.exists_dyadicC1AtDepth
    {x y : E} {gamma : Path x y} (hgamma : Path.PiecewiseC1 gamma) :
    ∃ n : ℕ, Path.DyadicC1AtDepth gamma n := by
  induction hgamma with
  | of_contDiffOn gamma regular =>
      exact ⟨0, .of_contDiffOn gamma regular 0⟩
  | trans gamma delta hgamma hdelta ihgamma ihdelta =>
      obtain ⟨n, hn⟩ := ihgamma
      obtain ⟨m, hm⟩ := ihdelta
      let k := max n m
      exact ⟨k + 1, .trans (hn.mono (le_max_left n m))
        (hm.mono (le_max_right n m))⟩
  | cast gamma hgamma hx hy ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n, .cast hn hx hy⟩

/-- The dyadic denominator associated to an alignment depth.-/
private def piecewiseC1DyadicScale (n : ℕ) : ℕ := 2 ^ n

@[simp] private theorem piecewiseC1DyadicScale_pos (n : ℕ) :
    0 < piecewiseC1DyadicScale n := by
  simp [piecewiseC1DyadicScale]

private def unitIntervalLeftHalf (t : unitInterval) : unitInterval :=
  ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

private def unitIntervalRightHalf (t : unitInterval) : unitInterval :=
  ⟨((t : ℝ) + 1) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩

omit [NormedSpace ℝ E] in
/-- Strict parameter identity for a subpath wholly contained in the left half
of a concatenation.-/
private theorem Path.trans_subpath_leftHalf_apply
    {x y z : E} (gamma : Path x y) (delta : Path y z)
    (a b t : unitInterval) :
    (gamma.trans delta).subpath (unitIntervalLeftHalf a)
        (unitIntervalLeftHalf b) t = gamma.subpath a b t := by
  change (gamma.trans delta)
      (Set.Icc.convexComb (unitIntervalLeftHalf a) (unitIntervalLeftHalf b) t) =
    gamma (Set.Icc.convexComb a b t)
  rw [Path.trans_apply, dite_eq_left]
  · congr 1
    apply Subtype.ext
    simp [unitIntervalLeftHalf]
    ring
  · change ((1 - (t : ℝ)) * ((a : ℝ) / 2) +
      (t : ℝ) * ((b : ℝ) / 2)) ≤ 1 / 2
    nlinarith [a.2.1, a.2.2, b.2.1, b.2.2, t.2.1, t.2.2]

omit [NormedSpace ℝ E] in
/-- Strict parameter identity for a subpath wholly contained in the right half
of a concatenation. At the shared endpoint the two branches agree by the path
endpoint laws.-/
private theorem Path.trans_subpath_rightHalf_apply
    {x y z : E} (gamma : Path x y) (delta : Path y z)
    (a b t : unitInterval) :
    (gamma.trans delta).subpath (unitIntervalRightHalf a)
        (unitIntervalRightHalf b) t = delta.subpath a b t := by
  change (gamma.trans delta)
      (Set.Icc.convexComb (unitIntervalRightHalf a) (unitIntervalRightHalf b) t) =
    delta (Set.Icc.convexComb a b t)
  rw [Path.trans_apply]
  split_ifs with h
  · have hlower : 1 / 2 ≤
        (1 - (t : ℝ)) * (((a : ℝ) + 1) / 2) +
          (t : ℝ) * (((b : ℝ) + 1) / 2) := by
      nlinarith [a.2.1, b.2.1, t.2.1, t.2.2]
    have heq :
        (1 - (t : ℝ)) * (((a : ℝ) + 1) / 2) +
          (t : ℝ) * (((b : ℝ) + 1) / 2) = 1 / 2 := by
      simpa [unitIntervalRightHalf] using le_antisymm h hlower
    have hab : Set.Icc.convexComb a b t = 0 := by
      apply Subtype.ext
      change (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) = 0
      simp at heq
      norm_num at heq
      linear_combination 2 * heq
    have hleftArg :
        (⟨2 * (Set.Icc.convexComb (unitIntervalRightHalf a)
          (unitIntervalRightHalf b) t : ℝ), by
            constructor
            · exact mul_nonneg (by norm_num)
                (Set.Icc.convexComb (unitIntervalRightHalf a)
                  (unitIntervalRightHalf b) t).2.1
            · linarith⟩ : unitInterval) = 1 := by
      apply Subtype.ext
      simp [unitIntervalRightHalf]
      nlinarith
    rw [hleftArg, gamma.target, hab, delta.source]
  · congr 1
    apply Subtype.ext
    simp [unitIntervalRightHalf]
    ring

/-- Piecewise-C1 regularity transports strictly from a child subpath to the
corresponding left-half subpath of a concatenation.-/
private theorem Path.PiecewiseC1.trans_subpath_leftHalf
    {x y z : E} (gamma : Path x y) (delta : Path y z)
    (a b : unitInterval) (hgamma : Path.PiecewiseC1 (gamma.subpath a b)) :
    Path.PiecewiseC1 ((gamma.trans delta).subpath
      (unitIntervalLeftHalf a) (unitIntervalLeftHalf b)) := by
  have hx : (gamma.trans delta) (unitIntervalLeftHalf a) = gamma a := by
    simpa using Path.trans_subpath_leftHalf_apply gamma delta a b 0
  have hy : (gamma.trans delta) (unitIntervalLeftHalf b) = gamma b := by
    simpa using Path.trans_subpath_leftHalf_apply gamma delta a b 1
  have hcast : Path.PiecewiseC1 ((gamma.subpath a b).cast hx hy) :=
    .cast _ hgamma hx hy
  have heq : ((gamma.subpath a b).cast hx hy) =
      (gamma.trans delta).subpath
        (unitIntervalLeftHalf a) (unitIntervalLeftHalf b) := by
    apply Path.ext
    funext t
    rw [Path.cast_coe]
    exact (Path.trans_subpath_leftHalf_apply gamma delta a b t).symm
  rwa [heq] at hcast

/-- Piecewise-C1 regularity transports strictly from a child subpath to the
corresponding right-half subpath of a concatenation.-/
private theorem Path.PiecewiseC1.trans_subpath_rightHalf
    {x y z : E} (gamma : Path x y) (delta : Path y z)
    (a b : unitInterval) (hdelta : Path.PiecewiseC1 (delta.subpath a b)) :
    Path.PiecewiseC1 ((gamma.trans delta).subpath
      (unitIntervalRightHalf a) (unitIntervalRightHalf b)) := by
  have hx : (gamma.trans delta) (unitIntervalRightHalf a) = delta a := by
    simpa using Path.trans_subpath_rightHalf_apply gamma delta a b 0
  have hy : (gamma.trans delta) (unitIntervalRightHalf b) = delta b := by
    simpa using Path.trans_subpath_rightHalf_apply gamma delta a b 1
  have hcast : Path.PiecewiseC1 ((delta.subpath a b).cast hx hy) :=
    .cast _ hdelta hx hy
  have heq : ((delta.subpath a b).cast hx hy) =
      (gamma.trans delta).subpath
        (unitIntervalRightHalf a) (unitIntervalRightHalf b) := by
    apply Path.ext
    funext t
    rw [Path.cast_coe]
    exact (Path.trans_subpath_rightHalf_apply gamma delta a b t).symm
  rwa [heq] at hcast

private def dyadicMeshPoint (n : ℕ) (i : Fin (2 ^ n + 1)) : unitInterval :=
  unitIntervalMeshPoint (2 ^ n) (by positivity) i

private def dyadicLeftPointIndex (n : ℕ) (i : Fin (2 ^ n + 1)) :
    Fin (2 ^ (n + 1) + 1) :=
  ⟨i, by
    calc
      i.val < 2 ^ n + 1 := i.isLt
      _ ≤ 2 ^ (n + 1) + 1 := Nat.add_le_add_right
        (Nat.pow_le_pow_right (n := 2) (by norm_num) (Nat.le_succ n)) 1⟩

private def dyadicRightPointIndex (n : ℕ) (i : Fin (2 ^ n + 1)) :
    Fin (2 ^ (n + 1) + 1) :=
  ⟨2 ^ n + i, by
    have hi : i.val ≤ 2 ^ n := Nat.le_of_lt_succ i.isLt
    simp only [pow_succ]
    omega⟩

@[simp] private theorem dyadicMeshPoint_leftIndex
    (n : ℕ) (i : Fin (2 ^ n + 1)) :
    dyadicMeshPoint (n + 1) (dyadicLeftPointIndex n i) =
      unitIntervalLeftHalf (dyadicMeshPoint n i) := by
  apply Subtype.ext
  simp only [dyadicMeshPoint, dyadicLeftPointIndex, unitIntervalMeshPoint,
    unitIntervalLeftHalf]
  push_cast
  rw [pow_succ]
  field_simp

@[simp] private theorem dyadicMeshPoint_rightIndex
    (n : ℕ) (i : Fin (2 ^ n + 1)) :
    dyadicMeshPoint (n + 1) (dyadicRightPointIndex n i) =
      unitIntervalRightHalf (dyadicMeshPoint n i) := by
  apply Subtype.ext
  simp only [dyadicMeshPoint, dyadicRightPointIndex, unitIntervalMeshPoint,
    unitIntervalRightHalf]
  push_cast
  rw [pow_succ]
  field_simp
  ring

private def subpathAffine (a b : unitInterval) (t : ℝ) : ℝ :=
  (1 - t) * (a : ℝ) + t * (b : ℝ)

private theorem subpathAffine_mem_Icc (a b : unitInterval) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : subpathAffine a b t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr ht.2) a.property.1)
      (mul_nonneg ht.1 b.property.1)
  · calc
      subpathAffine a b t ≤ (1 - t) * 1 + t * 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left a.property.2 (sub_nonneg.mpr ht.2))
          (mul_le_mul_of_nonneg_left b.property.2 ht.1)
      _ = 1 := by ring

omit [NormedSpace ℝ E] in
private theorem subpath_extend_eq
    {x y : E} (gamma : Path x y) (a b : unitInterval) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (gamma.subpath a b).extend t = gamma.extend (subpathAffine a b t) := by
  rw [Path.extend_apply _ ht]
  rw [Path.extend_apply _ (subpathAffine_mem_Icc a b ht)]
  rfl

private theorem Path.piecewiseC1_subpath_of_contDiffOn'
    {x y : E} (gamma : Path x y)
    (regular : ContDiffOn ℝ 1 gamma.extend (Icc 0 1))
    (a b : unitInterval) : Path.PiecewiseC1 (gamma.subpath a b) := by
  apply Path.piecewiseC1_of_contDiffOn
  have haffine : ContDiffOn ℝ 1 (subpathAffine a b) (Icc (0 : ℝ) 1) := by
    unfold subpathAffine
    fun_prop
  have hcomp : ContDiffOn ℝ 1 (gamma.extend ∘ subpathAffine a b) (Icc 0 1) :=
    regular.comp haffine (fun _ ht => subpathAffine_mem_Icc a b ht)
  apply hcomp.congr
  intro t ht
  exact subpath_extend_eq gamma a b ht

private theorem Path.DyadicC1AtDepth.dyadicSegment_piecewiseC1_aux
    {x y : E} {gamma : Path x y} {n : ℕ}
    (hgamma : Path.DyadicC1AtDepth gamma n) (i : Fin (2 ^ n)) :
    Path.PiecewiseC1 (gamma.subpath
      (dyadicMeshPoint n i.castSucc) (dyadicMeshPoint n i.succ)) := by
  induction hgamma with
  | of_contDiffOn gamma regular n =>
      exact Path.piecewiseC1_subpath_of_contDiffOn' gamma regular _ _
  | @trans x y z gamma delta n hgamma hdelta ihgamma ihdelta =>
      by_cases hi : i.val < 2 ^ n
      · let j : Fin (2 ^ n) := ⟨i, hi⟩
        have hstart : i.castSucc = dyadicLeftPointIndex n j.castSucc := by
          apply Fin.ext
          rfl
        have hend : i.succ = dyadicLeftPointIndex n j.succ := by
          apply Fin.ext
          rfl
        rw [hstart, hend, dyadicMeshPoint_leftIndex, dyadicMeshPoint_leftIndex]
        exact Path.PiecewiseC1.trans_subpath_leftHalf gamma delta _ _ (ihgamma j)
      · have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
          simp [pow_succ, Nat.mul_two]
        let j : Fin (2 ^ n) := ⟨i.val - 2 ^ n, by
          have hiLt : i.val < 2 ^ n + 2 ^ n := by
            simpa [pow_succ, Nat.mul_two] using i.isLt
          omega⟩
        have hstart : i.castSucc = dyadicRightPointIndex n j.castSucc := by
          apply Fin.ext
          simp only [dyadicRightPointIndex, Fin.val_castSucc, j]
          omega
        have hend : i.succ = dyadicRightPointIndex n j.succ := by
          apply Fin.ext
          simp only [Fin.val_succ, dyadicRightPointIndex, j]
          omega
        rw [hstart, hend, dyadicMeshPoint_rightIndex, dyadicMeshPoint_rightIndex]
        exact Path.PiecewiseC1.trans_subpath_rightHalf gamma delta _ _ (ihdelta j)
  | @cast x y x' y' gamma n hgamma hx hy ih =>
      have hsub := ih i
      have hsource : (gamma.cast hx hy) (dyadicMeshPoint n i.castSucc) =
          gamma (dyadicMeshPoint n i.castSucc) := by simp
      have htarget : (gamma.cast hx hy) (dyadicMeshPoint n i.succ) =
          gamma (dyadicMeshPoint n i.succ) := by simp
      have hcast : Path.PiecewiseC1
          ((gamma.subpath (dyadicMeshPoint n i.castSucc)
            (dyadicMeshPoint n i.succ)).cast hsource htarget) :=
        .cast _ hsub hsource htarget
      have heq :
          ((gamma.subpath (dyadicMeshPoint n i.castSucc)
            (dyadicMeshPoint n i.succ)).cast hsource htarget) =
          (gamma.cast hx hy).subpath (dyadicMeshPoint n i.castSucc)
            (dyadicMeshPoint n i.succ) := by
        apply Path.ext
        funext t
        change gamma (Set.Icc.convexComb _ _ t) =
          (gamma.cast hx hy) (Set.Icc.convexComb _ _ t)
        rw [Path.cast_coe]
      rwa [heq] at hcast

/-- Every elementary interval of the dyadic grid certified by
`DyadicC1AtDepth` is piecewise C1. The public statement uses the shared
`unitIntervalMeshPoint` interface rather than exposing an implementation-local
dyadic abbreviation.-/
theorem Path.DyadicC1AtDepth.dyadicSegment_piecewiseC1
    {x y : E} {gamma : Path x y} {n : ℕ}
    (hgamma : Path.DyadicC1AtDepth gamma n) (i : Fin (2 ^ n)) :
    Path.PiecewiseC1 (gamma.subpath
      (unitIntervalMeshPoint (2 ^ n) (by positivity) i.castSucc)
      (unitIntervalMeshPoint (2 ^ n) (by positivity) i.succ)) := by
  simpa [dyadicMeshPoint] using hgamma.dyadicSegment_piecewiseC1_aux i

/-- Every piecewise-C1 path has a uniform dyadic grid on which each elementary
subpath is again piecewise C1. Unlike arbitrary `Path.subpath` closure, this
statement is valid for the midpoint-based inductive carrier.-/
theorem Path.PiecewiseC1.exists_dyadicGrid_segments_piecewiseC1
    {x y : E} {gamma : Path x y} (hgamma : Path.PiecewiseC1 gamma) :
    ∃ n : ℕ, ∀ i : Fin (2 ^ n),
      Path.PiecewiseC1 (gamma.subpath
        (unitIntervalMeshPoint (2 ^ n) (by positivity) i.castSucc)
        (unitIntervalMeshPoint (2 ^ n) (by positivity) i.succ)) := by
  obtain ⟨n, hn⟩ := hgamma.exists_dyadicC1AtDepth
  exact ⟨n, hn.dyadicSegment_piecewiseC1⟩

/-- The bottom horizontal edge of a relative path-homotopy square is constant,
hence piecewise C1.-/
theorem pathHomotopySquare_horizontal_zero_piecewiseC1
    {x y : E} {gamma delta : Path x y} (F : gamma.Homotopy delta)
    (N : ℕ) (hN : 0 < N) (i : Fin N) :
    Path.PiecewiseC1
      (squareGridHorizontalEdge (pathHomotopySquare F) N hN i 0) := by
  have hsource : squareGridVertex (pathHomotopySquare F) N hN i.castSucc 0 = x := by
    simp [squareGridVertex]
  have htarget : squareGridVertex (pathHomotopySquare F) N hN i.succ 0 = x := by
    simp [squareGridVertex]
  have hcast : Path.PiecewiseC1 ((Path.refl x).cast hsource htarget) :=
    .cast _ (Path.piecewiseC1_refl x) hsource htarget
  have heq : ((Path.refl x).cast hsource htarget) =
      squareGridHorizontalEdge (pathHomotopySquare F) N hN i 0 := by
    apply Path.ext
    funext t
    rw [Path.cast_coe]
    simp [squareGridHorizontalEdge]
  rwa [heq] at hcast

/-- The top horizontal edge of a relative path-homotopy square is constant.-/
theorem pathHomotopySquare_horizontal_last_piecewiseC1
    {x y : E} {gamma delta : Path x y} (F : gamma.Homotopy delta)
    (N : ℕ) (hN : 0 < N) (i : Fin N) :
    Path.PiecewiseC1
      (squareGridHorizontalEdge (pathHomotopySquare F) N hN i (Fin.last N)) := by
  have hsource :
      squareGridVertex (pathHomotopySquare F) N hN i.castSucc (Fin.last N) = y := by
    simp [squareGridVertex]
  have htarget :
      squareGridVertex (pathHomotopySquare F) N hN i.succ (Fin.last N) = y := by
    simp [squareGridVertex]
  have hcast : Path.PiecewiseC1 ((Path.refl y).cast hsource htarget) :=
    .cast _ (Path.piecewiseC1_refl y) hsource htarget
  have heq : ((Path.refl y).cast hsource htarget) =
      squareGridHorizontalEdge (pathHomotopySquare F) N hN i (Fin.last N) := by
    apply Path.ext
    funext t
    rw [Path.cast_coe]
    simp [squareGridHorizontalEdge]
  rwa [heq] at hcast

/-- At dyadic scale `2^n`, the left vertical grid edges are exactly the
certified dyadic subpaths of the source path.-/
theorem Path.DyadicC1AtDepth.pathHomotopySquare_vertical_zero_piecewiseC1
    {x y : E} {gamma delta : Path x y} (F : gamma.Homotopy delta)
    {n : ℕ} (hgamma : Path.DyadicC1AtDepth gamma n) (i : Fin (2 ^ n)) :
    Path.PiecewiseC1
      (squareGridVerticalEdge (pathHomotopySquare F) (2 ^ n) (by positivity) 0 i) := by
  let a := dyadicMeshPoint n i.castSucc
  let b := dyadicMeshPoint n i.succ
  have hsource :
      squareGridVertex (pathHomotopySquare F) (2 ^ n) (by positivity) 0 i.castSucc =
        gamma a := by
    simp [squareGridVertex, a, dyadicMeshPoint]
  have htarget :
      squareGridVertex (pathHomotopySquare F) (2 ^ n) (by positivity) 0 i.succ =
        gamma b := by
    simp [squareGridVertex, b, dyadicMeshPoint]
  have hcast : Path.PiecewiseC1 ((gamma.subpath a b).cast hsource htarget) :=
    .cast _ (hgamma.dyadicSegment_piecewiseC1 i) hsource htarget
  have heq : ((gamma.subpath a b).cast hsource htarget) =
      squareGridVerticalEdge (pathHomotopySquare F) (2 ^ n) (by positivity) 0 i := by
    apply Path.ext
    funext t
    rw [Path.cast_coe]
    simp [Path.subpath, squareGridVerticalEdge, a, b, dyadicMeshPoint]
    rfl
  rwa [heq] at hcast

/-- At dyadic scale `2^n`, the right vertical grid edges are exactly the
certified dyadic subpaths of the target path.-/
theorem Path.DyadicC1AtDepth.pathHomotopySquare_vertical_last_piecewiseC1
    {x y : E} {gamma delta : Path x y} (F : gamma.Homotopy delta)
    {n : ℕ} (hdelta : Path.DyadicC1AtDepth delta n) (i : Fin (2 ^ n)) :
    Path.PiecewiseC1
      (squareGridVerticalEdge (pathHomotopySquare F) (2 ^ n) (by positivity)
        (Fin.last (2 ^ n)) i) := by
  let a := dyadicMeshPoint n i.castSucc
  let b := dyadicMeshPoint n i.succ
  have hsource :
      squareGridVertex (pathHomotopySquare F) (2 ^ n) (by positivity)
          (Fin.last (2 ^ n)) i.castSucc = delta a := by
    simp [squareGridVertex, a, dyadicMeshPoint]
  have htarget :
      squareGridVertex (pathHomotopySquare F) (2 ^ n) (by positivity)
          (Fin.last (2 ^ n)) i.succ = delta b := by
    simp [squareGridVertex, b, dyadicMeshPoint]
  have hcast : Path.PiecewiseC1 ((delta.subpath a b).cast hsource htarget) :=
    .cast _ (hdelta.dyadicSegment_piecewiseC1 i) hsource htarget
  have heq : ((delta.subpath a b).cast hsource htarget) =
      squareGridVerticalEdge (pathHomotopySquare F) (2 ^ n) (by positivity)
        (Fin.last (2 ^ n)) i := by
    apply Path.ext
    funext t
    rw [Path.cast_coe]
    simp [Path.subpath, squareGridVerticalEdge, a, b, dyadicMeshPoint]
    rfl
  rwa [heq] at hcast

end SandronesLibrary.Topology
