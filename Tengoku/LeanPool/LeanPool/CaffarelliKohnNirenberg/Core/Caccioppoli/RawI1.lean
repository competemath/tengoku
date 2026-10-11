/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.I1
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Covering
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.Finiteness
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds

/-!
# Raw I1

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

theorem caccioppoli_timePartial_contDiff
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => timePartial ψ z) := by
  let F : (Vec3 × ℝ) → ℝ → ℝ := fun z s => ψ (z.1, s)
  have hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : (Vec3 × ℝ) × ℝ => (q.1.1, q.2)) := by
    fun_prop
  have hF : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) := by
    convert hψ.comp hmap using 1
    funext q
    rfl
  have hderiv := hF.fderiv_apply
    (contDiff_snd (𝕜 := ℝ) (n := (⊤ : ℕ∞)))
    (contDiff_const (𝕜 := ℝ) (n := (⊤ : ℕ∞)) (c := (1 : ℝ)))
    (by simp)
  simpa only [F, timePartial, Function.uncurry] using hderiv

/-- Raw energy contribution from the time derivative and Laplacian of the heat cutoff. -/
def caccioppoliI1HeatCutoffRaw
    {u : ParabolicPoint → Vec3} {x₀ : Vec3} {t₀ ρ ε r : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) :
    ℝ :=
  (∫⁻ z in parabolicCylinder x₀ t₀ ρ,
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ (2 : ℝ) *
        ENNReal.ofReal |timePartial (fun w : ParabolicPoint =>
          backwardHeatCutoff
            (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) z +
          ∑ i, spatialSecondPartial (fun w : ParabolicPoint =>
            backwardHeatCutoff
              (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r w) i i z|).toReal

/-- Existence of an admissible time increment for the Caccioppoli heat cut-off,
matching the choice of `ε₀` at the start of the proof of Lemma `lem:caccioppoli`
(paper/ckn.tex §13): if a parabolic cylinder lies in the space-time domain
`spaceTimeSet Ω I` and `I` is open, then there is `0 < ε < r ^ 2` whose forward
time interval `Icc t₀ (t₀ + ε)` lies in `I`. The witness is a function of the
geometry alone, so no suitable-weak-solution data enters its construction. -/
theorem caccioppoli_admissible_heat_cutoff_exists
    {Ω : Set Vec3} {I : Set ℝ}
    {z₀ : ParabolicPoint} {ρ r : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hI : IsOpen I)
    (hsub : closure (parabolicCylinder z₀.1 z₀.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∃ ε : ℝ, 0 < ε ∧ ε < r ^ 2 ∧
      Icc z₀.2 (z₀.2 + ε) ⊆ I := by
  have hzI : z₀.2 ∈ I := by
    apply (hsub ?_).2
    rw [closure_parabolicCylinder hρ]
    exact ⟨by simp [vec3EuclideanNorm_zero, hρ.le],
      ⟨by linarith only [sq_pos_of_pos hρ], le_rfl⟩⟩
  obtain ⟨δ, hδ, hδI⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hzI)
  refine ⟨min (r ^ 2 / 2) (δ / 2), ?_, ?_, ?_⟩
  · exact lt_min (by positivity) (by positivity)
  · exact lt_of_le_of_lt (min_le_left _ _)
      (by nlinarith only [sq_pos_of_pos hr])
  · intro t ht
    apply hδI
    rw [Metric.mem_ball]
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    calc
      t - z₀.2 ≤ min (r ^ 2 / 2) (δ / 2) := by linarith only [ht.2]
      _ ≤ δ / 2 := min_le_right _ _
      _ < δ := by linarith only [hδ]

private theorem caccioppoli_heat_cutoff_support_in_carrier
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (_ : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (_ : ε < r ^ 2)
    (hsub : closure (parabolicCylinder (x₀) t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hfuture : Icc t₀ (t₀ + ε) ⊆ I) :
    tsupport (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) ⊆
      spaceTimeSet Ω I := by
  have hsp : ∀ z ∈ tsupport (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε),
      z.1 ∈ Ω := by
    intro z hz
    have hclosed : Function.support (caccioppoliHeatCutoff
        x₀ t₀ ρ ε hρ hε) ⊆
        euclideanClosedBall x₀ (3 * ρ / 4) ×ˢ
          Icc (t₀ - ρ ^ 2) (t₀ + ε) := by
      intro w hw
      have hmem := caccioppoli_heat_cutoff_support_subset x₀ t₀ ρ ε hρ hε hw
      refine ⟨?_, ?_⟩
      · exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
          (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity) |>.1 hmem.1 |>.le)
      · exact ⟨hmem.2.1.le, hmem.2.2.le⟩
    have hz' := closure_minimal hclosed
      (IsClosed.prod (isClosed_euclideanClosedBall x₀ (3 * ρ / 4)) isClosed_Icc) hz
    have hball : vec3EuclideanNorm (z.1 - x₀) ≤ ρ := by
      have hsmall' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (by positivity)).1 hz'.1
      have hnorm : vec3EuclideanNorm (z.1 - x₀) =
          CKN.vecEuclideanNorm (z.1 - x₀) := by
        simp [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot, pow_two]
      have hsmall : vec3EuclideanNorm (z.1 - x₀) ≤ 3 * ρ / 4 := by
        rw [hnorm]
        exact hsmall'
      linarith only [hsmall, hρ]
    have hmem : (z.1, t₀) ∈ closure (parabolicCylinder x₀ t₀ ρ) := by
      rw [closure_parabolicCylinder hρ]
      exact ⟨hball, ⟨by linarith only [sq_pos_of_pos hρ], le_rfl⟩⟩
    exact (hsub hmem).1
  intro z hz
  refine ⟨hsp z hz, ?_⟩
  have hclosed : Function.support (caccioppoliHeatCutoff
      x₀ t₀ ρ ε hρ hε) ⊆
      euclideanClosedBall x₀ (3 * ρ / 4) ×ˢ
        Icc (t₀ - ρ ^ 2) (t₀ + ε) := by
    intro w hw
    have hmem := caccioppoli_heat_cutoff_support_subset x₀ t₀ ρ ε hρ hε hw
    refine ⟨?_, ?_⟩
    · exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
        (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity) |>.1 hmem.1 |>.le)
    · exact ⟨hmem.2.1.le, hmem.2.2.le⟩
  have hz' := closure_minimal hclosed
    (IsClosed.prod (isClosed_euclideanClosedBall x₀ (3 * ρ / 4)) isClosed_Icc) hz
  rcases le_total z.2 t₀ with hle | hge
  · exact (hsub (by
      rw [closure_parabolicCylinder hρ]
      exact ⟨by
        have hsmall' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
          (by positivity)).1 hz'.1
        have hnorm : vec3EuclideanNorm (z.1 - x₀) =
            CKN.vecEuclideanNorm (z.1 - x₀) := by
          simp [vec3EuclideanNorm, CKN.vecEuclideanNorm, vecNormSq, vecDot, pow_two]
        have hsmall : vec3EuclideanNorm (z.1 - x₀) ≤ 3 * ρ / 4 := by
          rw [hnorm]
          exact hsmall'
        calc
          vec3EuclideanNorm (z.1 - x₀) ≤ 3 * ρ / 4 := hsmall
          _ ≤ ρ := by nlinarith only [hρ],
        ⟨by linarith only [hz'.2.1], hle⟩⟩)).2
  · exact hfuture ⟨hge, hz'.2.2⟩

theorem caccioppoli_heat_cutoff_testFunction
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {x₀ : Vec3} {t₀ ρ ε r : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hεr : ε < r ^ 2)
    (hsub : closure (parabolicCylinder x₀ t₀ ρ) ⊆ spaceTimeSet Ω I)
    (hfuture : Icc t₀ (t₀ + ε) ⊆ I) :
    backwardHeatCutoff
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r ∈
      spaceTimeTestFunction (V := ℝ) Ω I ∧
      (∀ z, 0 ≤ backwardHeatCutoff
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r z) := by
  exact backwardHeat_cutoff_testFunction
    (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) x₀ t₀ r hr
    (caccioppoli_heat_cutoff_smooth x₀ t₀ ρ ε hρ hε)
    (caccioppoli_heat_cutoff_hasCompactSupport x₀ t₀ ρ ε hρ hε)
    (caccioppoli_heat_cutoff_support_in_carrier hsol hρ hε hεr hsub hfuture)
    (caccioppoli_heat_cutoff_time_support_bound x₀ t₀ ρ ε r hρ hε hr hεr)
    (fun z => caccioppoli_heat_cutoff_nonneg x₀ t₀ ρ ε hρ hε z)

end CKN
