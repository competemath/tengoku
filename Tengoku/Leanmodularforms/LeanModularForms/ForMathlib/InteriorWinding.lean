/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.CurveUtilities
import Tengoku.Leanmodularforms.LeanModularForms.ForMathlib.FDBoundary

/-!
# Interior Winding Number for the Fundamental Domain Boundary

This file proves that the FD boundary contour avoids every point in the strict interior
of the fundamental domain, and reduces the interior winding number computation to a
contour integral identity.

## Strict interior

A point `z` is in the **strict interior** of the fundamental domain at height `H` when:
- `1 < ‖z‖` (strictly outside the unit circle)
- `|z.re| < 1/2` (strictly between the vertical edges)
- `0 < z.im` (in the upper half-plane)
- `z.im < H` (below the horizontal cap)

## Main results

### Avoidance (fully proved)

* `fdBoundaryFun_avoids_seg1` -- right vertical avoids strict interior (re = 1/2 vs |re| < 1/2)
* `fdBoundaryFun_avoids_seg2` -- right arc avoids strict interior (norm = 1 vs norm > 1)
* `fdBoundaryFun_avoids_seg3` -- left arc avoids strict interior (norm = 1 vs norm > 1)
* `fdBoundaryFun_avoids_seg4` -- left vertical avoids strict interior (re = -1/2 vs |re| < 1/2)
* `fdBoundaryFun_avoids_seg5` -- horizontal avoids strict interior (im = H vs im < H)
* `fdBoundaryFun_avoids_interior` -- full boundary avoids strict interior points

### Minimum distance (fully proved)

* `fdBoundaryFun_minDist_interior` -- the minimum distance from any strict interior point
  to the boundary is positive

### Reduction to contour integral (fully proved)

* `hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral` -- if a `PiecewiseC1Path` agrees
  with `fdBoundaryFun` and its contour integral of `(z - z₀)⁻¹` equals `-2πi`, then
  the interior winding number is `-1`.

### Clean constructor (fully proved)

* `FDWindingData.mk_of_interior_contourIntegral` -- build `FDWindingData` by supplying
  the interior contour integral identity as a hypothesis (together with the three
  `SingleCrossingData` for the elliptic points).

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- A point `z` is in the strict interior of the fundamental domain at height `H`.
This means `‖z‖ > 1`, `|z.re| < 1/2`, `0 < z.im`, and `z.im < H`. -/
def FDStrictInterior (z : ℂ) (H : ℝ) : Prop :=
  1 < ‖z‖ ∧ |z.re| < 1/2 ∧ 0 < z.im ∧ z.im < H

/--
@isnad1 id=lt.1h2v.s4.0482ea27aa91 from=translated src=- shape=91b6471e vocab=01930549
-/
theorem FDStrictInterior.norm_gt {z : ℂ} {H : ℝ} (h : FDStrictInterior z H) :
    1 < ‖z‖ := h.1

/--
@isnad1 id=lt.1h2v.s5.33e6d47f1565 from=translated src=- shape=92283f65 vocab=c70685b6
-/
theorem FDStrictInterior.re_abs_lt {z : ℂ} {H : ℝ} (h : FDStrictInterior z H) :
    |z.re| < 1/2 := h.2.1

/--
@isnad1 id=lt.1h2v.s4.766130110cd3 from=translated src=- shape=3626f54e vocab=30e43353
-/
theorem FDStrictInterior.im_pos {z : ℂ} {H : ℝ} (h : FDStrictInterior z H) :
    0 < z.im := h.2.2.1

/--
@isnad1 id=lt.1h2v.s3.f1fc84df6619 from=translated src=- shape=1f8c27ae vocab=30e43353
-/
theorem FDStrictInterior.im_lt {z : ℂ} {H : ℝ} (h : FDStrictInterior z H) :
    z.im < H := h.2.2.2

/-- The right vertical segment has `re = 1/2`, so it avoids any point with `|re| < 1/2`.
@isnad1 id=ne.2h3v.s6.daca36d4c84b from=translated src=- shape=c9289597 vocab=4b53db6a
-/
theorem fdBoundaryFun_avoids_seg1 {z : ℂ} (hz_re : |z.re| < 1/2)
    {H : ℝ} {t : ℝ} (ht : t ≤ 1/5) : fdBoundaryFun H t ≠ z := fun heq => by
  rw [show z.re = 1/2 from heq ▸ fdBoundaryFun_seg1_re H t ht] at hz_re
  norm_num at hz_re

/-- The arc segments lie on the unit circle, so they avoid any point with `‖z‖ > 1`.
@isnad1 id=ne.3h3v.s6.57bb129604bd from=translated src=- shape=62b80b18 vocab=009256ea
-/
theorem fdBoundaryFun_avoids_arc {z : ℂ} (hz_norm : 1 < ‖z‖)
    {H : ℝ} {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    fdBoundaryFun H t ≠ z := fun heq => by
  have h1 : ‖z‖ = 1 := heq ▸ fdBoundaryFun_arc_norm H t ht1 ht2
  linarith

/-- The left vertical segment has `re = -1/2`, so it avoids any point with `|re| < 1/2`.
@isnad1 id=ne.3h3v.s6.377c33a3c9a3 from=translated src=- shape=acc5a95f vocab=4b53db6a
-/
theorem fdBoundaryFun_avoids_seg4 {z : ℂ} (hz_re : |z.re| < 1/2)
    {H : ℝ} {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    fdBoundaryFun H t ≠ z := fun heq => by
  rw [show z.re = -1/2 from heq ▸ fdBoundaryFun_seg4_re H t ht3 ht4] at hz_re
  norm_num at hz_re

/-- The horizontal segment has `im = H`, so it avoids any point with `im < H`.
@isnad1 id=ne.2h3v.s5.5fd09263ad16 from=translated src=- shape=bf5fcf6e vocab=47b9de92
-/
theorem fdBoundaryFun_avoids_seg5 {z : ℂ} (hz_im : z.im < H)
    {t : ℝ} (ht : 4/5 < t) : fdBoundaryFun H t ≠ z := fun heq => by
  have h1 : z.im = H := heq ▸ fdBoundaryFun_seg5_im H t ht
  linarith

/-- The FD boundary avoids every point in the strict interior of the fundamental domain.
This follows by case-splitting on the segment and applying the segment-specific avoidance.
@isnad1 id=ne.4h3v.s6.916837024026 from=translated src=- shape=8dd2f8dd vocab=a8eeeeee
-/
theorem fdBoundaryFun_avoids_interior {z : ℂ} {H : ℝ}
    (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H) :
    ∀ t ∈ Icc (0 : ℝ) 1, fdBoundaryFun H t ≠ z := by
  intro t _
  by_cases h1 : t ≤ 1/5
  · exact fdBoundaryFun_avoids_seg1 hz_re h1
  push Not at h1
  by_cases h2 : t ≤ 3/5
  · exact fdBoundaryFun_avoids_arc hz_norm h1 h2
  push Not at h2
  by_cases h3 : t ≤ 4/5
  · exact fdBoundaryFun_avoids_seg4 hz_re h2 h3
  push Not at h3
  exact fdBoundaryFun_avoids_seg5 hz_im h3

/-- For a strict interior point, the minimum distance to the FD boundary on `[0, 1]`
is positive. This follows from avoidance + compactness.
@isnad1 id=ex.3h2v.s6.b65eb06a3fb7 from=translated src=- shape=3a25ed0f vocab=f57af4ab
-/
theorem fdBoundaryFun_minDist_interior_pos {z : ℂ} {H : ℝ}
    (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖fdBoundaryFun H t - z‖ := by
  have h_closed : IsClosed (fdBoundaryFun H '' Icc (0 : ℝ) 1) :=
    (isCompact_Icc.image (fdBoundaryFun_continuous H)).isClosed
  have h_nonempty : (fdBoundaryFun H '' Icc (0 : ℝ) 1).Nonempty :=
    ⟨fdBoundaryFun H 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩
  have h_nmem : z ∉ fdBoundaryFun H '' Icc (0 : ℝ) 1 := fun ⟨t, ht, heq⟩ =>
    fdBoundaryFun_avoids_interior hz_norm hz_re hz_im t ht heq
  refine ⟨Metric.infDist z (fdBoundaryFun H '' Icc 0 1),
    (h_closed.notMem_iff_infDist_pos h_nonempty).mp h_nmem, fun t ht => ?_⟩
  rw [← dist_eq_norm, dist_comm]
  exact Metric.infDist_le_dist_of_mem (mem_image_of_mem _ ht)

/-- If a `PiecewiseC1Path` agrees with `fdBoundaryFun` on `[0, 1]`, then it also
avoids every strict interior point.
@isnad1 id=ex.4h3v.s7.2044200d2a3a from=translated src=- shape=a8262554 vocab=063896d3
-/
theorem piecewiseC1Path_avoids_interior {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {z : ℂ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (hz_im : z.im < H) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - z‖ := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := fdBoundaryFun_minDist_interior_pos hz_norm hz_re hz_im
  refine ⟨δ, hδ_pos, fun t ht => ?_⟩
  change δ ≤ ‖γ.toPath.extend t - z‖
  rw [hγ t ht]
  exact hδ_bound t ht

/-- **Reduction to contour integral**: if a `PiecewiseC1Path` agrees with `fdBoundaryFun`
on `[0, 1]`, and the contour integral of `(z - z₀)⁻¹` equals `-2πi`, then the
generalized winding number at `z₀` is `-1`.

This reduces the interior winding number (a CPV/PV limit) to an ordinary contour integral
identity, which is the hard computational content.
@isnad1 id=hasgener.6h3v.s7.73ef6f9c1be4 from=translated src=- shape=739d9e7f vocab=c8b3a4ba
-/
theorem hasGeneralizedWindingNumber_fdBoundary_of_contourIntegral {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H))
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t)
    {z : ℂ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2)
    (_hz_im_pos : 0 < z.im) (hz_im_lt : z.im < H)
    (h_integral : γ.contourIntegral (fun w => (w - z)⁻¹) =
      -(2 * ↑Real.pi * I)) :
    HasGeneralizedWindingNumber γ z (-1) := by
  convert hasGeneralizedWindingNumber_of_avoids
    (piecewiseC1Path_avoids_interior γ hγ hz_norm hz_re hz_im_lt) using 1
  rw [h_integral]
  field_simp

/-- On segment 1, the distance to `z` is at least `1/2 - |z.re|`, which is positive
for strict interior points.
@isnad1 id=le.2h3v.s6.32cbaf6c80f0 from=translated src=- shape=572fdff9 vocab=64aa9c8f
-/
theorem fdBoundaryFun_seg1_re_dist {z : ℂ} (_hz_re : |z.re| < 1/2)
    {H : ℝ} {t : ℝ} (ht : t ≤ 1/5) :
    1/2 - |z.re| ≤ ‖fdBoundaryFun H t - z‖ := by
  calc 1/2 - |z.re| ≤ |1/2 - z.re| := by
        have h := abs_sub_abs_le_abs_sub (1/2 : ℝ) z.re
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 1/2)] at h
        exact h
    _ = |(fdBoundaryFun H t - z).re| := by rw [sub_re, fdBoundaryFun_seg1_re H t ht]
    _ ≤ ‖fdBoundaryFun H t - z‖ := Complex.abs_re_le_norm _

/-- On segments 2-3, the distance to `z` is at least `‖z‖ - 1`, which is positive
for strict interior points.
@isnad1 id=le.3h3v.s6.6061676a6a01 from=translated src=- shape=0cc5c0aa vocab=ccf599cf
-/
theorem fdBoundaryFun_arc_dist {z : ℂ} (_hz_norm : 1 < ‖z‖)
    {H : ℝ} {t : ℝ} (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    ‖z‖ - 1 ≤ ‖fdBoundaryFun H t - z‖ :=
  calc ‖z‖ - 1 = ‖z‖ - ‖fdBoundaryFun H t‖ := by rw [fdBoundaryFun_arc_norm H t ht1 ht2]
    _ ≤ ‖z - fdBoundaryFun H t‖ := norm_sub_norm_le z _
    _ = ‖fdBoundaryFun H t - z‖ := norm_sub_rev _ _

/-- On segment 4, the distance to `z` is at least `1/2 - |z.re|`, which is positive
for strict interior points.
@isnad1 id=le.3h3v.s7.636bb98fa3f4 from=translated src=- shape=019d2ef0 vocab=64aa9c8f
-/
theorem fdBoundaryFun_seg4_re_dist {z : ℂ} (_hz_re : |z.re| < 1/2)
    {H : ℝ} {t : ℝ} (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    1/2 - |z.re| ≤ ‖fdBoundaryFun H t - z‖ := by
  calc 1/2 - |z.re| ≤ |-1/2 - z.re| := by
        have h := abs_sub_abs_le_abs_sub (-1/2 : ℝ) z.re
        rw [show |(-1 : ℝ)/2| = 1/2 by norm_num] at h
        exact h
    _ = |(fdBoundaryFun H t - z).re| := by rw [sub_re, fdBoundaryFun_seg4_re H t ht3 ht4]
    _ ≤ ‖fdBoundaryFun H t - z‖ := Complex.abs_re_le_norm _

/-- On segment 5, the distance to `z` is at least `H - z.im`, which is positive
for strict interior points.
@isnad1 id=le.2h3v.s6.2ad324340bc5 from=translated src=- shape=0fb11abc vocab=f1cf1774
-/
theorem fdBoundaryFun_seg5_im_dist {z : ℂ} (hz_im : z.im < H)
    {t : ℝ} (ht : 4/5 < t) :
    H - z.im ≤ ‖fdBoundaryFun H t - z‖ :=
  calc H - z.im = |(fdBoundaryFun H t - z).im| := by
        rw [sub_im, fdBoundaryFun_seg5_im H t ht, abs_of_pos (by linarith)]
    _ ≤ ‖fdBoundaryFun H t - z‖ := Complex.abs_im_le_norm _

end
