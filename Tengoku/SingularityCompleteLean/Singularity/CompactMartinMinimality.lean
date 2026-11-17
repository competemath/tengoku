import Tengoku.SingularityCompleteLean.Singularity.CompactMartinCovariance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Minimality of every compact geometric Martin kernel

Normalized translation preserves minimality in the positive harmonic cone.
The finite-chart minimality theorem therefore applies at infinity as well,
and surjectivity identifies the entire abstract Martin boundary as minimal.
-/

noncomputable section
open Set OnePoint
open scoped Topology Classical MatrixGroups UpperHalfPlane
namespace Singularity

/-- Minimality in the positive harmonic cone is preserved by the normalized
Martin translation action.
@isnad1 id=ex.4h6v.s8.381dd6734fcf from=translated src=- shape=7dc083a1 vocab=7b21f21d
-/
theorem harmonic_minimal_martinTranslate {Γ : Type*} [Group Γ]
    (s : Finset Γ) (μ : Γ → ℝ) (H : Γ → ℝ) (hHp : ∀ x, 0 < H x)
    (hmin : ∀ f : Γ → ℝ, (∀ x, 0 ≤ f x ∧ f x ≤ H x) →
      (∀ x, ∑ a ∈ s, μ a * f (x * a) = f x) →
      ∃ c ∈ Icc (0 : ℝ) 1, ∀ x, f x = c * H x)
    (g : Γ) (f : Γ → ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ martinTranslate 1 g H x)
    (hfh : ∀ x, ∑ a ∈ s, μ a * f (x * a) = f x) :
    ∃ c ∈ Icc (0 : ℝ) 1, ∀ x, f x = c * martinTranslate 1 g H x := by
  let d := H g⁻¹
  have hd : 0 < d := hHp g⁻¹
  let F : Γ → ℝ := fun x => d * f (g * x)
  have hF (x : Γ) : 0 ≤ F x ∧ F x ≤ H x := by
    refine ⟨mul_nonneg hd.le (hf (g * x)).1, ?_⟩
    have hh := (hf (g * x)).2
    simp only [martinTranslate, inv_mul_cancel_left, mul_one] at hh
    have hh' := (le_div_iff₀ hd).mp hh
    simpa only [F, mul_comm d] using hh'
  have hFh (x : Γ) : ∑ a ∈ s, μ a * F (x * a) = F x := by
    calc
      _ = d * (∑ a ∈ s, μ a * f ((g * x) * a)) := by
        simp only [F, Finset.mul_sum, mul_assoc, mul_left_comm]
      _ = F x := by rw [hfh]
  obtain ⟨c, hc, hFc⟩ := hmin F hF hFh
  refine ⟨c, hc, fun x => ?_⟩
  have he := hFc (g⁻¹ * x)
  simp only [F, mul_inv_cancel_left] at he
  calc
    f x = (c * H (g⁻¹ * x)) / d := (eq_div_iff (ne_of_gt hd)).mpr (by nlinarith [he])
    _ = c * martinTranslate 1 g H x := by simp only [martinTranslate, mul_one, mul_div_assoc, d]

variable (Γ : Subgroup SL(2, ℝ)) [DiscreteTopology Γ]
  [CompactSpace (Quotient (MulAction.orbitRel Γ ℍ))]
  [MeasurableSpace Γ] [MeasurableMul Γ] [MeasurableSingletonClass Γ]
  (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g)
  (hmass : ∑ g ∈ s, μ g = 1) (hgen : Submonoid.closure (s : Set Γ) = ⊤)
  (hgap : spectralRadius ℂ (rightMarkov s μ) < 1)
  (horbit : (MulAction.orbit Γ (∞ : OnePoint ℝ)).Infinite)

end Singularity
