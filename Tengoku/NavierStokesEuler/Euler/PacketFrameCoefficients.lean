import Tengoku.NavierStokesEuler.Euler.PacketMovingFrame

/-!
The physical parent decomposition and moving-frame coefficient bounds in
source (23).  Frame motion and primary shear motion are derived from the
actual homogeneous ray and velocity equations.
-/

noncomputable section

namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketCrossProduct
  EulerPacketRay InnerProductSpace ContinuousLinearMap

theorem abs_inner_map_le (B : Space →L[ℝ] Space) {p q : Space}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) : |⟪p,B q⟫_ℝ| ≤ ‖B‖ := by
  have h := (abs_real_inner_le_norm p (B q)).trans
    (mul_le_mul_of_nonneg_left (B.le_opNorm q) (norm_nonneg p))
  simpa only [hp, hq, mul_one, one_mul] using h

theorem rayRate_norm_le (B : Space →L[ℝ] Space) {p : Space} (hp : ‖p‖ = 1) :
    ‖rayRate B p‖ ≤ 2*‖B‖ := by
  have hB : ‖B.adjoint p‖ ≤ ‖B‖ := by
    simpa only [hp, mul_one, LinearIsometryEquiv.norm_map] using B.adjoint.le_opNorm p
  have hi := abs_inner_map_le B hp hp
  have h := norm_add_le (-B.adjoint p) (⟪p,B p⟫_ℝ • p)
  simp only [norm_neg, norm_smul, Real.norm_eq_abs, hp, mul_one] at h
  exact h.trans (by linarith only [hB, hi])

theorem velocityRate_norm_le (B : Space →L[ℝ] Space) {p q : Space}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) : ‖velocityRate B p q‖ ≤ 4*‖B‖ := by
  have hB : ‖B q‖ ≤ ‖B‖ := by simpa only [hq, mul_one] using B.le_opNorm q
  have hi := abs_inner_map_le B hp hq
  have hj := abs_inner_map_le B hq hq
  have h1 := norm_add_le (-B q) ((2*⟪p,B q⟫_ℝ) • p)
  have h2 := norm_add_le (-B q+(2*⟪p,B q⟫_ℝ) • p) (⟪q,B q⟫_ℝ • q)
  simp only [norm_neg, norm_smul, Real.norm_eq_abs, hp, hq, mul_one, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 2)] at h1 h2
  change ‖-B q+(2*⟪p,B q⟫_ℝ) • p+⟪q,B q⟫_ℝ • q‖ ≤ 4*‖B‖
  linarith only [h1, h2, hB, hi, hj]

theorem frameRate_norm_le (B : Space →L[ℝ] Space) (p q : Space)
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (i : Fin 3) :
    ‖frameRate B p q i‖ ≤ 6*‖B‖ := by
  have hr := rayRate_norm_le B hp
  have hv := velocityRate_norm_le B hp hq
  fin_cases i
  · change ‖rayRate B p‖ ≤ 6*‖B‖
    linarith only [hr, norm_nonneg B]
  · change ‖velocityRate B p q‖ ≤ 6*‖B‖
    linarith only [hv, norm_nonneg B]
  · change ‖cross (rayRate B p) q+cross p (velocityRate B p q)‖ ≤ 6*‖B‖
    have h := (norm_add_le _ _).trans (add_le_add
      (cross_norm_le (rayRate B p) q) (cross_norm_le p (velocityRate B p q)))
    simp only [hp, hq, mul_one, one_mul] at h
    linarith only [h, hr, hv]

def frameMatrixRate (B B₁ : Space →L[ℝ] Space) (p q : Space) (i j : Fin 3) : ℝ :=
  ⟪frameRate B p q i,B (frame p q j)⟫_ℝ +
    ⟪frame p q i,B₁ (frame p q j)+B (frameRate B p q j)⟫_ℝ

theorem frameMatrix_hasDerivWithinAt {B : ℝ → Space →L[ℝ] Space}
    {B₁ : Space →L[ℝ] Space} {m v : ℝ → Space} {t : ℝ} {S : Set ℝ}
    (hB : HasDerivWithinAt B B₁ S t)
    (hm : HasDerivWithinAt m (-(B t).adjoint (m t)) S t)
    (hv : HasDerivWithinAt v (-(B t) (v t) +
      (2*⟪m t,(B t) (v t)⟫_ℝ / ‖m t‖^2) • m t) S t)
    (hm0 : m t ≠ 0) (hv0 : v t ≠ 0) (hmv : ⟪m t,v t⟫_ℝ = 0) (i j : Fin 3) :
    HasDerivWithinAt (fun s => frameMatrix (B s) (unit (m s)) (unit (v s)) i j)
      (frameMatrixRate (B t) B₁ (unit (m t)) (unit (v t)) i j) S t := by
  have hi := normalizedFrame_hasDerivWithinAt (B t) hm hv hm0 hv0 hmv i
  have hj := normalizedFrame_hasDerivWithinAt (B t) hm hv hm0 hv0 hmv j
  exact (hi.inner ℝ (hB.clm_apply hj)).congr_deriv (add_comm _ _)

def primaryShear (c : ℝ) (m v : ℝ → Space) (t : ℝ) : ℝ := c*(‖m t‖*‖v t‖)

end EulerPacketMovingFrame
