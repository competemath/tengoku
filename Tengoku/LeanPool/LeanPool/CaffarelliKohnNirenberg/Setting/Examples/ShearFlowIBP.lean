/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import Tengoku

/-!
# Smooth space-time integration by parts

Directional integration by parts for a smooth field and a compactly supported
test on the raw product of space and time, expressed using factor derivatives.
-/

@[expose] public section

open MeasureTheory Set
open CKN.Foundation.Parabolic

namespace CKN
namespace ShearCalculus

local instance : Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  infer_instance

/-- The spatial factor derivative is the joint derivative in a spatial direction.
@isnad1 id=eq.1h3v.s9.532e779e80fc from=translated src=- shape=ba91ab67 vocab=cbf65e8f
-/
theorem spatial_eq_joint {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : Vec3 × ℝ) (i : Fin 3) :
    spatialPartial g i z = fderiv ℝ g z (basisVec i, 0) := by
  have h := ((hg.differentiable (by simp)) z).hasFDerivAt.comp z.1
    ((hasFDerivAt_id z.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) z.2 z.1))
  change (fderiv ℝ (g ∘ fun x : Vec3 => (id x, z.2)) z.1) (basisVec i) = _
  rw [h.fderiv]
  simp

/-- The time factor derivative is the joint derivative in the time direction.
@isnad1 id=eq.1h2v.s9.df8860520c85 from=translated src=- shape=bfc91764 vocab=1b9a0455
-/
theorem time_eq_joint {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : Vec3 × ℝ) :
    timePartial g z = fderiv ℝ g z (0, 1) := by
  have h := ((hg.differentiable (by simp)) z).hasFDerivAt.comp z.2
    ((hasFDerivAt_const (𝕜 := ℝ) z.1 z.2).prodMk (hasFDerivAt_id z.2))
  change (fderiv ℝ (g ∘ fun s : ℝ => (z.1, id s)) z.2) 1 = _
  rw [h.fderiv]
  simp

/-- A directional derivative of a smooth scalar function is smooth.
@isnad1 id=contdiff.1h2v.s10.23414cabc67f from=translated src=- shape=3b18337a vocab=12a48b77
-/
theorem directional_smooth {g : Vec3 × ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (v : Vec3 × ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ g z v) := by
  exact ((contDiff_infty_iff_fderiv.mp hg).2).clm_apply contDiff_const

/-- Integration by parts in an arbitrary space-time direction.
@isnad1 id=eq.3h3v.s10.1dec9f431d06 from=translated src=- shape=35ff49b0 vocab=8cf45abf
-/
theorem integral_directional {F G : Vec3 × ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) (v : Vec3 × ℝ) :
    (∫ z, F z * fderiv ℝ G z v) = -∫ z, fderiv ℝ F z v * G z := by
  have hDG := directional_smooth hG v
  have hDF := directional_smooth hF v
  have hcDG := hGc.fderiv_apply (𝕜 := ℝ) v
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hDF.continuous.mul hG.continuous).integrable_of_hasCompactSupport
      (hGc.mul_left (f := fun z => fderiv ℝ F z v))
  · exact (hF.continuous.mul hDG.continuous).integrable_of_hasCompactSupport
      (hcDG.mul_left (f := F))
  · exact (hF.continuous.mul hG.continuous).integrable_of_hasCompactSupport
      (hGc.mul_left (f := F))
  · intro z hz
    exact (hF.differentiable (by simp)) z
  · intro z hz
    exact (hG.differentiable (by simp)) z

/-- Space-time integration by parts for a spatial factor derivative.
@isnad1 id=eq.3h3v.s9.ef3280ecc703 from=translated src=- shape=9ac344b3 vocab=ab4f9e94
-/
theorem integral_spatial {F G : Vec3 × ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) (i : Fin 3) :
    (∫ z : Vec3 × ℝ, F z * spatialPartial G i z) =
      -∫ z : Vec3 × ℝ, spatialPartial F i z * G z := by
  simp_rw [spatial_eq_joint hG, spatial_eq_joint hF]
  exact integral_directional hF hG hGc (basisVec i, 0)

/-- Space-time integration by parts for the time factor derivative.
@isnad1 id=eq.3h2v.s9.b281cbdd1795 from=translated src=- shape=7087b646 vocab=eed42aba
-/
theorem integral_time {F G : Vec3 × ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) :
    (∫ z : Vec3 × ℝ, F z * timePartial G z) =
      -∫ z : Vec3 × ℝ, timePartial F z * G z := by
  simp_rw [time_eq_joint hG, time_eq_joint hF]
  exact integral_directional hF hG hGc (0, 1)

/-- Smoothness of a spatial factor derivative.
@isnad1 id=contdiff.1h2v.s8.98e02c541744 from=translated src=- shape=311eaee5 vocab=10e7a6df
-/
theorem spatial_smooth {F : Vec3 × ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => spatialPartial F i z) := by
  simp_rw [spatial_eq_joint hF]
  exact directional_smooth hF (basisVec i, 0)

/-- A spatial derivative has no larger support than its smooth input.
@isnad1 id=le.1h2v.s8.3ea5df65484b from=translated src=- shape=99edbe85 vocab=6a2da674
-/
theorem spatial_support {F : Vec3 × ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i : Fin 3) :
    tsupport (fun z : Vec3 × ℝ => spatialPartial F i z) ⊆ tsupport F := by
  simp_rw [spatial_eq_joint hF]
  exact tsupport_fderiv_apply_subset ℝ (basisVec i, 0)

/-- A time derivative has no larger support than its smooth input.
@isnad1 id=le.1h1v.s8.440dacef4830 from=translated src=- shape=02cc4437 vocab=50ccef93
-/
theorem time_support {F : Vec3 × ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    tsupport (fun z : Vec3 × ℝ => timePartial F z) ⊆ tsupport F := by
  simp_rw [time_eq_joint hF]
  exact tsupport_fderiv_apply_subset ℝ (0, 1)

/-- A smooth field times a compactly supported test is integrable.
@isnad1 id=integrab.3h2v.s9.a2ba7adafeac from=translated src=- shape=04784637 vocab=012b99df
-/
theorem integrable_product {F G : Vec3 × ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) : Integrable (fun z => F z * G z) :=
  (hF.continuous.mul hG.continuous).integrable_of_hasCompactSupport hGc.mul_left

/-- Products with spatial test derivatives are integrable.
@isnad1 id=integrab.3h3v.s9.a6c7893ff6d5 from=translated src=- shape=c1626ba2 vocab=4a27f42a
-/
theorem integrable_spatial {F G : Vec3 × ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) (i : Fin 3) :
    Integrable (fun z : Vec3 × ℝ => F z * spatialPartial G i z) := by
  exact integrable_product hF (spatial_smooth hG i)
    (hGc.isCompact.of_isClosed_subset (isClosed_tsupport _) (spatial_support hG i))

/-- Products with time test derivatives are integrable.
@isnad1 id=integrab.3h2v.s9.2b3fb9e9da2c from=translated src=- shape=ac6191cf vocab=a8330262
-/
theorem integrable_time {F G : Vec3 × ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) :
    Integrable (fun z : Vec3 × ℝ => F z * timePartial G z) := by
  simp_rw [time_eq_joint hG]
  exact integrable_product hF (directional_smooth hG (0, 1))
    (hGc.fderiv_apply (𝕜 := ℝ) (0, 1))

/-- Product rule for spatial factor derivatives.
@isnad1 id=eq.2h4v.s8.12765b134d23 from=translated src=- shape=7ac6a70e vocab=63e60657
-/
theorem spatial_mul {F G : Vec3 × ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (i : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (fun w : Vec3 × ℝ => F w * G w) i z =
      spatialPartial F i z * G z + F z * spatialPartial G i z := by
  rw [spatial_eq_joint (hF.mul hG), spatial_eq_joint hF, spatial_eq_joint hG,
    fderiv_fun_mul ((hF.differentiable (by simp)) z) ((hG.differentiable (by simp)) z)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Product rule for time factor derivatives.
@isnad1 id=eq.2h3v.s8.c1bc52e560a8 from=translated src=- shape=66640f24 vocab=b6ad7e1f
-/
theorem time_mul {F G : Vec3 × ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (z : Vec3 × ℝ) :
    timePartial (fun w : Vec3 × ℝ => F w * G w) z =
      timePartial F z * G z + F z * timePartial G z := by
  rw [time_eq_joint (hF.mul hG), time_eq_joint hF, time_eq_joint hG,
    fderiv_fun_mul ((hF.differentiable (by simp)) z) ((hG.differentiable (by simp)) z)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Two spatial integrations by parts against a compactly supported test.
@isnad1 id=eq.3h3v.s9.9e5fe4351d4a from=translated src=- shape=01fd60d4 vocab=f232cd2c
-/
theorem integral_second {F G : Vec3 × ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGc : HasCompactSupport G) (i : Fin 3) :
    (∫ z : Vec3 × ℝ, F z * spatialPartial (fun w : Vec3 × ℝ => spatialPartial G i w) i z) =
      ∫ z : Vec3 × ℝ, spatialPartial (fun w : Vec3 × ℝ => spatialPartial F i w) i z * G z := by
  rw [integral_spatial hF (spatial_smooth hG i)
      (hGc.isCompact.of_isClosed_subset (isClosed_tsupport _) (spatial_support hG i)) i,
    integral_spatial (spatial_smooth hF i) hG hGc i, neg_neg]

end ShearCalculus
end CKN
