import Tengoku.OpenaiMath.OAI.Analysis.LiebThirring.BoundaryParity

namespace OAI

universe u143 u144 u145 u146 u147

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

/-- A continuous cutoff equal to one on the inner half ball. -/
def radialCut (R t : ℝ) : ℝ := max 0 (min 1 (2 - 2*t/R))

lemma radialCut_nonneg (R t : ℝ) : 0 ≤ radialCut R t := le_max_left _ _
lemma radialCut_le_one (R t : ℝ) : radialCut R t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)
lemma radialCut_eq_zero (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : R ≤ t) : radialCut R t = 0 := by
  classical
  apply max_eq_left
  apply (min_le_right _ _).trans
  have hd : 2 ≤ 2*t/R := (le_div_iff₀ hR).mpr (by linarith)
  linarith
lemma radialCut_eq_one (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : t ≤ R/2) : radialCut R t = 1 := by
  classical
  have hd : 2*t/R ≤ 1 := (div_le_iff₀ hR).mpr (by linarith)
  simp only [radialCut, min_eq_left (by linarith : 1 ≤ 2 - 2*t/R), max_eq_right zero_le_one]
lemma continuous_radialCut (R : ℝ) : Continuous (radialCut R) := by
  classical
  unfold radialCut
  fun_prop

section Flatten
variable {d : ℕ} (H : Subgroup (Signs (d + 1)))
variable {V : Type u143} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
variable (p : Fin d → ℝ) (R : ℝ) (f : (Fin (d + 1) → ℝ) → V)

def localAffine (s : H) (x : Fin (d + 1) → ℝ) : V :=
  ρ s (L (spatial (s⁻¹ • x) - p))

def flattenTerm (s : H) (x : Fin (d + 1) → ℝ) : V :=
  radialCut R (dist x (s • embedSpatial p)) • (localAffine H ρ L p s x - f x)

def flattenInitial (x : Fin (d + 1) → ℝ) : V := by
  classical
  exact f x + ∑ s : H, flattenTerm H ρ L p R f s x

end Flatten
end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity
section FlattenCompact
variable {d : ℕ} (H : Subgroup (Signs (d + 1)))
variable {V : Type u144} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
variable (p : Fin d → ℝ) (R : ℝ) (f : (Fin (d + 1) → ℝ) → V)

end FlattenCompact
end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
lemma hasFDerivAt_relative_error {E : Type u145} {V : Type u146}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : E → V) (p : E) (L : E ≃L[ℝ] V) (hf0 : f p = 0)
    (hd : HasFDerivAt f L.toContinuousLinearMap p) :
    ∃ δ > 0, ∀ u : E, dist u p < δ → ‖f u - L (u-p)‖ ≤ ‖L (u-p)‖ / 2 := by
  let M := ‖L.symm.toContinuousLinearMap‖
  have hM : 0 ≤ M := norm_nonneg _
  let c := 1 / (2*(M+1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcM : c*M ≤ 1/2 := by
    dsimp [c]
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity : 0 < 2*(M+1))]
    linarith
  obtain ⟨δ,hδ,he⟩ := Metric.eventually_nhds_iff.mp (hd.isLittleO.def hc)
  refine ⟨δ,hδ,fun u hu ↦ ?_⟩
  have hsmall : ‖f u - L (u-p)‖ ≤ c * ‖u-p‖ := by simpa only [hf0,sub_zero,ContinuousLinearEquiv.coe_coe] using he hu
  have hnorm : ‖u-p‖ ≤ M * ‖L (u-p)‖ := by
    have h := L.symm.toContinuousLinearMap.le_opNorm (L (u-p))
    simpa only [ContinuousLinearEquiv.coe_coe,L.symm_apply_apply] using h
  calc
    ‖f u - L (u-p)‖ ≤ c*‖u-p‖ := hsmall
    _ ≤ c*(M*‖L (u-p)‖) := mul_le_mul_of_nonneg_left hnorm hc.le
    _ = (c*M)*‖L (u-p)‖ := by ring
    _ ≤ (1/2)*‖L (u-p)‖ := mul_le_mul_of_nonneg_right hcM (norm_nonneg _)
    _ = ‖L (u-p)‖/2 := by ring
end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

end SharpLiebThirring.CubeFlags

end
end
end

end OAI
