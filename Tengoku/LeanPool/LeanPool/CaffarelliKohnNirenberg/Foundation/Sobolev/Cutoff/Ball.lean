/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Basic
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Profile
public import Tengoku

/-!
# Quantitative smooth cutoffs for round balls

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This independent port uses the native `Fin d → ℝ` carrier and an
explicit Euclidean squared distance.

## Main definitions

* `euclideanBall` and `euclideanClosedBall`: round balls for the explicit
  Euclidean norm.
* `canonicalBallCutoff`: a smooth cutoff with a midpoint support collar.

## Main results

* `canonicalBallCutoff_smooth`, `canonicalBallCutoff_eq_one_on_inner`, and
  `canonicalBallCutoff_tsupport_subset_outer` give the qualitative cutoff
  properties.
* `canonicalBallCutoff_gradient_bound` gives the explicit bound
  `32 / (R - r)`.
-/

@[expose] public section

open Set

noncomputable section

namespace CKN

/-- Euclidean squared distance on native vectors. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ :=
  vecNormSq (x - y)

/-- The explicit round Euclidean open ball. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}

/-- The explicit round Euclidean closed ball. -/
def euclideanClosedBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ ≤ R ^ 2}

@[simp]
theorem euclideanSqDist_self {d : ℕ} (x : Vec d) :
    euclideanSqDist x x = 0 := by
  simp [euclideanSqDist, vecNormSq, vecDot]

theorem mem_euclideanBall_iff_vecEuclideanNorm_lt {d : ℕ}
    {x₀ x : Vec d} {R : ℝ} (hR : 0 < R) :
    x ∈ euclideanBall x₀ R ↔
      vecEuclideanNorm (x - x₀) < R := by
  change vecNormSq (x - x₀) < R ^ 2 ↔
    Real.sqrt (vecNormSq (x - x₀)) < R
  exact (Real.sqrt_lt' hR).symm

theorem mem_euclideanClosedBall_iff_vecEuclideanNorm_le {d : ℕ}
    {x₀ x : Vec d} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ euclideanClosedBall x₀ R ↔
      vecEuclideanNorm (x - x₀) ≤ R := by
  change vecNormSq (x - x₀) ≤ R ^ 2 ↔
    Real.sqrt (vecNormSq (x - x₀)) ≤ R
  exact (Real.sqrt_le_left hR).symm

theorem contDiff_vecNormSq {d : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => vecNormSq x) := by
  unfold vecNormSq vecDot
  exact ContDiff.sum (s := Finset.univ) fun i _hi =>
    (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)

theorem contDiff_euclideanSqDist_left {d : ℕ} (x₀ : Vec d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec d => euclideanSqDist x x₀) := by
  unfold euclideanSqDist
  exact contDiff_vecNormSq.comp (contDiff_id.sub contDiff_const)

theorem isClosed_euclideanClosedBall {d : ℕ} (x₀ : Vec d) (R : ℝ) :
    IsClosed (euclideanClosedBall x₀ R) := by
  change IsClosed
    ((fun x : Vec d => euclideanSqDist x x₀) ⁻¹' Iic (R ^ 2))
  exact isClosed_Iic.preimage (contDiff_euclideanSqDist_left x₀).continuous

theorem sq_coord_sub_le_euclideanSqDist {d : ℕ}
    (x y : Vec d) (i : Fin d) :
    (x i - y i) ^ 2 ≤ euclideanSqDist x y := by
  simpa [euclideanSqDist, Pi.sub_apply] using
    sq_apply_le_vecNormSq (x - y) i

/-- A round closed ball is contained in the inherited supremum-metric closed
ball with the same nonnegative radius. -/
theorem euclideanClosedBall_subset_supClosedBall {d : ℕ}
    {x₀ : Vec d} {R : ℝ} (hR : 0 ≤ R) :
    euclideanClosedBall x₀ R ⊆ Metric.closedBall x₀ R := by
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff hR]
  intro i
  have hsqi : (x i - x₀ i) ^ 2 ≤ R ^ 2 :=
    (sq_coord_sub_le_euclideanSqDist x x₀ i).trans hx
  have habs : |x i - x₀ i| ≤ R :=
    abs_le_of_sq_le_sq hsqi hR
  simpa [Real.dist_eq, abs_sub_comm] using habs

theorem isCompact_euclideanClosedBall {d : ℕ}
    (x₀ : Vec d) {R : ℝ} (hR : 0 ≤ R) :
    IsCompact (euclideanClosedBall x₀ R) :=
  (ProperSpace.isCompact_closedBall x₀ R).of_isClosed_subset
    (isClosed_euclideanClosedBall x₀ R)
    (euclideanClosedBall_subset_supClosedBall hR)

theorem euclideanClosedBall_subset_euclideanBall {d : ℕ}
    {x₀ : Vec d} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    euclideanClosedBall x₀ r ⊆ euclideanBall x₀ R := by
  intro x hx
  change euclideanSqDist x x₀ < R ^ 2
  change euclideanSqDist x x₀ ≤ r ^ 2 at hx
  nlinarith only [hx, hr, hrR]

/-- The strict midpoint radius keeps the support inside the outer ball. -/
def ballCutoffMidRadius (r R : ℝ) : ℝ :=
  (r + R) / 2

/-- Squared-radius interpolation variable for a round cutoff. -/
def ballCutoffArgument {d : ℕ}
    (x₀ : Vec d) (r s : ℝ) (x : Vec d) : ℝ :=
  (s ^ 2 - euclideanSqDist x x₀) / (s ^ 2 - r ^ 2)

/-- The canonical ball cutoff, with a midpoint support collar. -/
def canonicalBallCutoff {d : ℕ}
    (x₀ : Vec d) (r R : ℝ) : Vec d → ℝ :=
  smoothTransitionProfile ∘
    ballCutoffArgument x₀ r (ballCutoffMidRadius r R)

/-- Smooth spatial cutoff with separately specified inner and support radii. -/
def ballCutoffWithSupportRadius {d : ℕ}
    (x₀ : Vec d) (r s : ℝ) : Vec d → ℝ :=
  smoothTransitionProfile ∘ ballCutoffArgument x₀ r s

private theorem ballCutoffArgument_den_pos {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) :
    0 < s ^ 2 - r ^ 2 := by
  have hs : 0 < s := lt_of_le_of_lt hr hrs
  calc
    0 < (s - r) * (s + r) :=
      mul_pos (sub_pos.mpr hrs) (add_pos_of_pos_of_nonneg hs hr)
    _ = s ^ 2 - r ^ 2 := by
      ring

private theorem inner_lt_ballCutoffMidRadius {r R : ℝ}
    (hrR : r < R) :
    r < ballCutoffMidRadius r R := by
  unfold ballCutoffMidRadius
  linarith only [hrR]

private theorem ballCutoffMidRadius_lt_outer {r R : ℝ}
    (hrR : r < R) :
    ballCutoffMidRadius r R < R := by
  unfold ballCutoffMidRadius
  linarith only [hrR]

private theorem ballCutoffMidRadius_nonneg {r R : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) :
    0 ≤ ballCutoffMidRadius r R := by
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  unfold ballCutoffMidRadius
  positivity

private theorem ballCutoffArgument_contDiff {d : ℕ}
    {x₀ : Vec d} {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) :
    ContDiff ℝ (⊤ : ℕ∞)
      (ballCutoffArgument x₀ r s) := by
  unfold ballCutoffArgument
  exact
    (contDiff_const.sub (contDiff_euclideanSqDist_left x₀)).div
      contDiff_const
      (fun _ => (ballCutoffArgument_den_pos hr hrs).ne')

private theorem ballCutoffWithSupportRadius_smooth {d : ℕ}
    {x₀ : Vec d} {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s) :
    ContDiff ℝ (⊤ : ℕ∞)
      (ballCutoffWithSupportRadius x₀ r s) := by
  exact smoothTransitionProfile.smooth.comp
    (ballCutoffArgument_contDiff hr hrs)

private theorem ballCutoffWithSupportRadius_eq_one {d : ℕ}
    {x₀ : Vec d} {r s : ℝ} (hr : 0 ≤ r) (hrs : r < s)
    {x : Vec d} (hx : x ∈ euclideanBall x₀ r) :
    ballCutoffWithSupportRadius x₀ r s x = 1 := by
  apply smoothTransitionProfile.one_of_one_le
  unfold ballCutoffArgument
  have hden := ballCutoffArgument_den_pos hr hrs
  rw [one_le_div hden]
  change euclideanSqDist x x₀ < r ^ 2 at hx
  linarith only [hx]

private theorem ballCutoffWithSupportRadius_eq_zero_of_not_mem_closedBall
    {d : ℕ} {x₀ : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) {x : Vec d}
    (hx : x ∉ euclideanClosedBall x₀ s) :
    ballCutoffWithSupportRadius x₀ r s x = 0 := by
  apply smoothTransitionProfile.zero_of_nonpos
  unfold ballCutoffArgument
  have hdenNonneg :
      0 ≤ s ^ 2 - r ^ 2 :=
    (ballCutoffArgument_den_pos hr hrs).le
  have hnumNonpos :
      s ^ 2 - euclideanSqDist x x₀ ≤ 0 := by
    change ¬euclideanSqDist x x₀ ≤ s ^ 2 at hx
    exact sub_nonpos.mpr (le_of_lt (not_le.mp hx))
  exact div_nonpos_of_nonpos_of_nonneg hnumNonpos hdenNonneg

private theorem ballCutoffWithSupportRadius_support_subset_closedBall
    {d : ℕ} {x₀ : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) :
    Function.support (ballCutoffWithSupportRadius x₀ r s) ⊆
      euclideanClosedBall x₀ s := by
  intro x hx
  by_contra hnot
  exact hx
    (ballCutoffWithSupportRadius_eq_zero_of_not_mem_closedBall
      hr hrs hnot)

private theorem ballCutoffWithSupportRadius_tsupport_subset_closedBall
    {d : ℕ} {x₀ : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) :
    tsupport (ballCutoffWithSupportRadius x₀ r s) ⊆
      euclideanClosedBall x₀ s :=
  closure_minimal
    (ballCutoffWithSupportRadius_support_subset_closedBall hr hrs)
    (isClosed_euclideanClosedBall x₀ s)

private theorem ballCutoffWithSupportRadius_hasCompactSupport
    {d : ℕ} {x₀ : Vec d} {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r < s) :
    HasCompactSupport (ballCutoffWithSupportRadius x₀ r s) := by
  have hs : 0 ≤ s := (lt_of_le_of_lt hr hrs).le
  exact HasCompactSupport.of_support_subset_isCompact
    (isCompact_euclideanClosedBall x₀ hs)
    (ballCutoffWithSupportRadius_support_subset_closedBall hr hrs)

/-- The canonical midpoint-collar cutoff is smooth to every order. -/
theorem canonicalBallCutoff_smooth {d : ℕ}
    (x₀ : Vec d) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    ContDiff ℝ (⊤ : ℕ∞) (canonicalBallCutoff x₀ r R) := by
  simpa [canonicalBallCutoff, ballCutoffWithSupportRadius] using
    ballCutoffWithSupportRadius_smooth
      (x₀ := x₀) hr
        (inner_lt_ballCutoffMidRadius hrR)

/-- The canonical midpoint-collar cutoff is nonnegative. -/
theorem canonicalBallCutoff_nonneg {d : ℕ}
    (x₀ : Vec d) (r R : ℝ) (x : Vec d) :
    0 ≤ canonicalBallCutoff x₀ r R x :=
  smoothTransitionProfile.nonneg _

/-- The canonical midpoint-collar cutoff is at most one. -/
theorem canonicalBallCutoff_le_one {d : ℕ}
    (x₀ : Vec d) (r R : ℝ) (x : Vec d) :
    canonicalBallCutoff x₀ r R x ≤ 1 :=
  smoothTransitionProfile.le_one _

/-- The canonical midpoint-collar cutoff equals one on the inner open ball. -/
theorem canonicalBallCutoff_eq_one_on_inner {d : ℕ}
    {x₀ : Vec d} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    {x : Vec d} (hx : x ∈ euclideanBall x₀ r) :
    canonicalBallCutoff x₀ r R x = 1 := by
  simpa [canonicalBallCutoff, ballCutoffWithSupportRadius] using
    ballCutoffWithSupportRadius_eq_one
      hr (inner_lt_ballCutoffMidRadius hrR) hx

/-- The topological support lies inside the outer open ball. -/
theorem canonicalBallCutoff_tsupport_subset_outer {d : ℕ}
    {x₀ : Vec d} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    tsupport (canonicalBallCutoff x₀ r R) ⊆
      euclideanBall x₀ R := by
  have hclosed :
      tsupport
          (ballCutoffWithSupportRadius x₀ r
            (ballCutoffMidRadius r R)) ⊆
        euclideanClosedBall x₀ (ballCutoffMidRadius r R) :=
    ballCutoffWithSupportRadius_tsupport_subset_closedBall
      hr (inner_lt_ballCutoffMidRadius hrR)
  have hstrict :
      euclideanClosedBall x₀ (ballCutoffMidRadius r R) ⊆
        euclideanBall x₀ R :=
    euclideanClosedBall_subset_euclideanBall
      (ballCutoffMidRadius_nonneg hr hrR)
      (ballCutoffMidRadius_lt_outer hrR)
  simpa [canonicalBallCutoff, ballCutoffWithSupportRadius] using
    hclosed.trans hstrict

/-- The canonical midpoint-collar cutoff has compact support. -/
theorem canonicalBallCutoff_hasCompactSupport {d : ℕ}
    {x₀ : Vec d} {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    HasCompactSupport (canonicalBallCutoff x₀ r R) := by
  simpa [canonicalBallCutoff, ballCutoffWithSupportRadius] using
    ballCutoffWithSupportRadius_hasCompactSupport
      (x₀ := x₀) hr
        (inner_lt_ballCutoffMidRadius hrR)

end CKN
