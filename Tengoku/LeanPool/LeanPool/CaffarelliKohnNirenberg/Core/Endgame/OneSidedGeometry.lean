/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Tengoku

/-!
# One-sided cylinder covering

The truncated time shift of Step 2 in the proof of `thm:A`. For a cylinder
`𝒞_ϱ(w)` meeting the one-sided cylinder of admissible centres, and a point
`w'` of the intersection, the new centre is
`w'' = (x_{w'}, min {t_w + ϱ², 0})`: the spatial centre of `w'` and the
forward time shift truncated at the top face. It stays among the admissible
centres, and `𝒞_ϱ(w) ∩ {t ≤ 0} ⊆ 𝒞_{2ϱ}(w'')`. The covering itself needs no
upper bound on the radius.
-/

@[expose] public section

open Set
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Endgame

/-- Shift the time coordinate forward by the squared radius, stopping at
the prescribed upper time, and use the selected point as spatial center. -/
def truncatedCylinderCenter (w w' : ParabolicPoint) (ρ T : ℝ) : ParabolicPoint :=
  (w'.1, min (w.2 + ρ ^ 2) T)

/-- The truncated center stays in any cylinder of upper time `T` that
contains the selected intersection point.
@isnad1 id=mem.2h6v.s5.1387c0242cdb from=translated src=- shape=d873426b vocab=4b2adf8b
-/
theorem truncatedCylinderCenter_mem
    {w w' : ParabolicPoint} {x : Vec3} {T R ρ : ℝ}
    (hw : w' ∈ parabolicCylinder w.1 w.2 ρ)
    (hinner : w' ∈ parabolicCylinder x T R) :
    truncatedCylinderCenter w w' ρ T ∈ parabolicCylinder x T R := by
  change vec3EuclideanNorm (w'.1 - x) < R ∧
    T - R ^ 2 < min (w.2 + ρ ^ 2) T ∧ min (w.2 + ρ ^ 2) T ≤ T
  change vec3EuclideanNorm (w'.1 - w.1) < ρ ∧
    w.2 - ρ ^ 2 < w'.2 ∧ w'.2 ≤ w.2 at hw
  change vec3EuclideanNorm (w'.1 - x) < R ∧
    T - R ^ 2 < w'.2 ∧ w'.2 ≤ T at hinner
  refine ⟨hinner.1, hinner.2.1.trans_le ?_, min_le_right _ _⟩
  exact le_min (le_trans hw.2.2 (le_add_of_nonneg_right (sq_nonneg ρ))) hinner.2.2

/-- The portion below time `T` is covered by a cylinder of twice the radius
whose spatial center is any point of the original cylinder.
@isnad1 id=le.1h4v.s6.703a6e0e52c4 from=translated src=- shape=ec74e29f vocab=21734929
-/
theorem parabolicCylinder_inter_le_subset_truncated
    {w w' : ParabolicPoint} {ρ T : ℝ}
    (hw : w' ∈ parabolicCylinder w.1 w.2 ρ) :
    parabolicCylinder w.1 w.2 ρ ∩ {z : ParabolicPoint | z.2 ≤ T} ⊆
      parabolicCylinder (truncatedCylinderCenter w w' ρ T).1
        (truncatedCylinderCenter w w' ρ T).2 (2 * ρ) := by
  intro z hz
  obtain ⟨hz, hzT⟩ := hz
  change vec3EuclideanNorm (z.1 - w.1) < ρ ∧
    w.2 - ρ ^ 2 < z.2 ∧ z.2 ≤ w.2 at hz
  change vec3EuclideanNorm (w'.1 - w.1) < ρ ∧
    w.2 - ρ ^ 2 < w'.2 ∧ w'.2 ≤ w.2 at hw
  change vec3EuclideanNorm (z.1 - w'.1) < 2 * ρ ∧
    min (w.2 + ρ ^ 2) T - (2 * ρ) ^ 2 < z.2 ∧
    z.2 ≤ min (w.2 + ρ ^ 2) T
  refine ⟨?_, ?_, le_min ?_ hzT⟩
  · have htriangle : vec3EuclideanNorm (z.1 - w'.1) ≤
        vec3EuclideanNorm (z.1 - w.1) + vec3EuclideanNorm (w'.1 - w.1) := by
      simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_sub]
      simpa only [dist_eq_norm,
        norm_sub_rev (WithLp.toLp 2 w.1) (WithLp.toLp 2 w'.1)] using
        dist_triangle (WithLp.toLp 2 z.1) (WithLp.toLp 2 w.1) (WithLp.toLp 2 w'.1)
    linarith only [htriangle, hz.1, hw.1]
  · have hmin := min_le_left (w.2 + ρ ^ 2) T
    nlinarith only [hz.2.1, hmin, sq_nonneg ρ]
  · exact le_trans hz.2.2 (le_add_of_nonneg_right (sq_nonneg ρ))

/-- A positive smaller concentric cylinder lies among the admissible centers.
@isnad1 id=le.2h1v.s7.927c2745c811 from=translated src=- shape=18eedd10 vocab=81926ecb
-/
theorem parabolicCylinder_subset_three_quarters {a : ℝ}
    (ha : 0 < a) (ha34 : a < 3 / 4) :
    parabolicCylinder (0 : Vec3) 0 a ⊆
      parabolicCylinder (0 : Vec3) 0 (3 / 4) := by
  intro z hz
  refine ⟨hz.1.trans ha34, ?_, hz.2.2⟩
  have hsq : a ^ 2 < (3 / 4 : ℝ) ^ 2 := by
    nlinarith only [ha, ha34]
  change 0 - (3 / 4 : ℝ) ^ 2 < z.2
  exact (sub_lt_sub_left hsq 0).trans hz.2.1

/-- Any cylinder meeting a smaller one-sided cylinder has a truncated
admissible center covering its entire portion below time zero.
@isnad1 id=ex.3h3v.s8.95ac7f868f30 from=translated src=- shape=45e01cf0 vocab=79ab0e84
-/
theorem exists_one_sided_covering_cylinder_on_cylinder
    {a : ℝ} (ha : 0 < a) (ha34 : a < 3 / 4)
    {w : ParabolicPoint} {ρ : ℝ}
    (hmeet : (parabolicCylinder w.1 w.2 ρ ∩
      parabolicCylinder (0 : Vec3) 0 a).Nonempty) :
    ∃ w' ∈ parabolicCylinder w.1 w.2 ρ ∩ parabolicCylinder (0 : Vec3) 0 a,
      truncatedCylinderCenter w w' ρ 0 ∈ parabolicCylinder (0 : Vec3) 0 (3 / 4) ∧
      parabolicCylinder w.1 w.2 ρ ∩ {z : ParabolicPoint | z.2 ≤ 0} ⊆
        parabolicCylinder (truncatedCylinderCenter w w' ρ 0).1
          (truncatedCylinderCenter w w' ρ 0).2 (2 * ρ) := by
  obtain ⟨w', hw'⟩ := hmeet
  exact ⟨w', hw', parabolicCylinder_subset_three_quarters ha ha34
    (truncatedCylinderCenter_mem hw'.1 hw'.2),
    parabolicCylinder_inter_le_subset_truncated hw'.1⟩

end CKN.Core.Endgame
