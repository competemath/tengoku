/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.ScalingQuantities
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Tengoku

/-!
# Scaling Invariance Basic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology Pointwise
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- Spatial part of the parabolic change of variables. -/
def scalingSpace (μ : ℝ) (x₀ : Vec3) : Vec3 → Vec3 :=
  fun y => x₀ + μ • y

/-- Temporal part of the parabolic change of variables. -/
def scalingTime (μ : ℝ) (t₀ : ℝ) : ℝ → ℝ :=
  fun s => t₀ + μ ^ 2 * s

/-- Parabolic dilation followed by space-time translation. -/
def scalingParabolic (μ : ℝ) (z₀ : ParabolicPoint) :
    ParabolicPoint → ParabolicPoint :=
  fun z => parabolicTranslate z₀.1 z₀.2 (parabolicScale μ z)

/-- Spatial domain pulled back under the parabolic change of variables. -/
def rescaledSpace (μ : ℝ) (x₀ : Vec3) (Ω : Set Vec3) : Set Vec3 :=
  scalingSpace μ x₀ ⁻¹' Ω

/-- Time domain pulled back under the parabolic change of variables. -/
def rescaledTime (μ : ℝ) (t₀ : ℝ) (I : Set ℝ) : Set ℝ :=
  scalingTime μ t₀ ⁻¹' I

/--
@isnad1 id=eq.0h2v.s5.0e893557e3d1 from=translated src=- shape=e800f8b3 vocab=b27fa512
-/
theorem scalingParabolic_eq (μ : ℝ) (z₀ : ParabolicPoint) :
    scalingParabolic μ z₀ =
      fun z => (scalingSpace μ z₀.1 z.1, scalingTime μ z₀.2 z.2) := by
  funext z
  rfl

/--
@isnad1 id=eq.0h4v.s5.3fd5b4b30e10 from=translated src=- shape=24a328fd vocab=0c9f3175
-/
theorem rescaledSpaceTimeSet_eq_preimage (μ : ℝ) (z₀ : ParabolicPoint)
    (Ω : Set Vec3) (I : Set ℝ) :
    spaceTimeSet (rescaledSpace μ z₀.1 Ω) (rescaledTime μ z₀.2 I) =
      scalingParabolic μ z₀ ⁻¹' spaceTimeSet Ω I := by
  ext z
  rcases z with ⟨y, s⟩
  rfl

private theorem scalingSpace_continuous (μ : ℝ) (x₀ : Vec3) :
    Continuous (scalingSpace μ x₀) := by
  change Continuous (fun y : Vec3 => x₀ + μ • y)
  fun_prop

private theorem scalingTime_continuous (μ : ℝ) (t₀ : ℝ) :
    Continuous (scalingTime μ t₀) := by
  change Continuous (fun s : ℝ => t₀ + μ ^ 2 * s)
  fun_prop

/--
@isnad1 id=isopen.1h3v.s6.097514ba5b4d from=translated src=- shape=02a4fa13 vocab=a5c87cea
-/
theorem rescaledSpace_isOpen {μ : ℝ} (x₀ : Vec3) {Ω : Set Vec3}
    (hΩ : IsOpen Ω) : IsOpen (rescaledSpace μ x₀ Ω) :=
  hΩ.preimage (scalingSpace_continuous μ x₀)

/--
@isnad1 id=isopen.1h3v.s4.7b8362f6a859 from=translated src=- shape=69e8fdd7 vocab=3e52ff66
-/
theorem rescaledTime_isOpen {μ : ℝ} (t₀ : ℝ) {I : Set ℝ}
    (hI : IsOpen I) : IsOpen (rescaledTime μ t₀ I) :=
  hI.preimage (scalingTime_continuous μ t₀)

/--
@isnad1 id=ordconne.2h3v.s4.dcac095b05d1 from=translated src=- shape=8714683b vocab=314dab71
-/
theorem rescaledTime_ordConnected {μ : ℝ} (_ : 0 < μ) (t₀ : ℝ)
    {I : Set ℝ} (hI : I.OrdConnected) :
    (rescaledTime μ t₀ I).OrdConnected := by
  apply hI.preimage_mono
  intro a b hab
  dsimp [scalingTime]
  simpa [add_comm] using
    (add_le_add_left (mul_le_mul_of_nonneg_left hab (sq_nonneg μ)) t₀)

/-- Homeomorphism underlying the spatial scaling map. -/
def scalingSpaceHomeomorph (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) :
    Vec3 ≃ₜ Vec3 :=
  (Homeomorph.smulOfNeZero μ hμ.ne').trans (Homeomorph.addLeft x₀)

private theorem scalingSpace_eq_homeomorph (μ : ℝ) (hμ : 0 < μ) (x₀ : Vec3) :
    scalingSpace μ x₀ = scalingSpaceHomeomorph μ hμ x₀ := by
  funext y
  simp [scalingSpace, scalingSpaceHomeomorph]

/-- Homeomorphism underlying the temporal scaling map. -/
def scalingTimeHomeomorph (μ : ℝ) (hμ : 0 < μ) (t₀ : ℝ) :
    ℝ ≃ₜ ℝ :=
  (Homeomorph.smulOfNeZero (μ ^ 2) (sq_pos_of_pos hμ).ne').trans
    (Homeomorph.addLeft t₀)

private theorem scalingTime_eq_homeomorph (μ : ℝ) (hμ : 0 < μ) (t₀ : ℝ) :
    scalingTime μ t₀ = scalingTimeHomeomorph μ hμ t₀ := by
  funext s
  simp [scalingTime, scalingTimeHomeomorph, smul_eq_mul]

/-- Inverse temporal affine map used in scaling the weak equations. -/
def scalingTimeInv (μ : ℝ) (t₀ : ℝ) : ℝ → ℝ :=
  fun s => (μ ^ 2)⁻¹ * (s - t₀)

private theorem scalingTime_left_inverse (μ : ℝ) (hμ : 0 < μ) (t₀ s : ℝ) :
    scalingTimeInv μ t₀ (scalingTime μ t₀ s) = s := by
  dsimp [scalingTimeInv, scalingTime]
  field_simp [hμ.ne']
  ring

private theorem scalingTime_right_inverse (μ : ℝ) (hμ : 0 < μ) (t₀ s : ℝ) :
    scalingTime μ t₀ (scalingTimeInv μ t₀ s) = s := by
  dsimp [scalingTimeInv, scalingTime]
  field_simp [hμ.ne']
  ring

private theorem scalingTime_image_eq_preimage {μ : ℝ} (hμ : 0 < μ) (t₀ : ℝ)
    (J : Set ℝ) :
    scalingTime μ t₀ '' J = scalingTimeInv μ t₀ ⁻¹' J := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    change scalingTimeInv μ t₀ (scalingTime μ t₀ t) ∈ J
    simpa only [scalingTime_left_inverse μ hμ t₀ t] using ht
  · intro hs
    change scalingTimeInv μ t₀ s ∈ J at hs
    exact ⟨scalingTimeInv μ t₀ s, hs,
      scalingTime_right_inverse μ hμ t₀ s⟩

private theorem scalingTimeInv_monotone {μ : ℝ} (_ : 0 < μ) (t₀ : ℝ) :
    Monotone (scalingTimeInv μ t₀) := by
  intro a b hab
  dsimp [scalingTimeInv]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hab t₀)
    (inv_nonneg.mpr (sq_nonneg μ))

/--
@isnad1 id=localbox.2h6v.s6.b5a5ee2210c5 from=translated src=- shape=4b900e02 vocab=79f910a6
-/
theorem localBox_forward {μ : ℝ} (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {Ω' : Set Vec3} {J : Set ℝ}
    (hbox : localBox (rescaledSpace μ z₀.1 Ω)
      (rescaledTime μ z₀.2 I) Ω' J) :
    localBox Ω I (scalingSpace μ z₀.1 '' Ω')
      (scalingTime μ z₀.2 '' J) := by
  rcases hbox with ⟨hΩ'op, hΩ'c, hΩ'Ω, hJord, hJc, hJI⟩
  let eΩ := scalingSpaceHomeomorph μ hμ z₀.1
  let eI := scalingTimeHomeomorph μ hμ z₀.2
  have heΩ : scalingSpace μ z₀.1 = eΩ := scalingSpace_eq_homeomorph μ hμ z₀.1
  have heI : scalingTime μ z₀.2 = eI := scalingTime_eq_homeomorph μ hμ z₀.2
  have hΩclosure :
      closure (scalingSpace μ z₀.1 '' Ω') = eΩ '' closure Ω' := by
    rw [heΩ, ← eΩ.image_closure]
  have hJclosure :
      closure (scalingTime μ z₀.2 '' J) = eI '' closure J := by
    rw [heI, ← eI.image_closure]
  refine ⟨eΩ.isOpenMap Ω' hΩ'op, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hΩclosure]
    exact hΩ'c.image eΩ.continuous
  · rw [hΩclosure]
    rintro y ⟨x, hx, rfl⟩
    rw [← heΩ]
    exact hΩ'Ω hx
  · rw [scalingTime_image_eq_preimage hμ z₀.2 J]
    exact hJord.preimage_mono (scalingTimeInv_monotone hμ z₀.2)
  · rw [hJclosure]
    exact hJc.image eI.continuous
  · rw [hJclosure]
    rintro s ⟨t, ht, rfl⟩
    rw [← heI]
    exact hJI ht

end CKN
