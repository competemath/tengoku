import Tengoku.NavierStokesEuler.Euler.PacketNormalizedPrimary
import Tengoku

/-!
The oriented orthonormal frame built from the actual normalized primary.
Its angular-velocity entries are derived from the physical ODEs and agree
with the `frameSkew` matrix used in the source propagation estimates.
-/

noncomputable section

namespace EulerPacketMovingFrame

open EulerSmoothLimit EulerPacketCrossProduct EulerPacketNormalizedPrimary
  InnerProductSpace ContinuousLinearMap Matrix WithLp

def crossBilinear : Space →L[ℝ] Space →L[ℝ] Space :=
  ({ toFun := crossLeft
     map_add' a b := by
       apply ContinuousLinearMap.ext
       intro x
       simp [crossLeft_apply, cross, map_add]
     map_smul' r a := by
       apply ContinuousLinearMap.ext
       intro x
       simp [crossLeft_apply, cross, map_smul] } : Space →ₗ[ℝ] (Space →L[ℝ] Space)).mkContinuous 1
    (fun a => by
      change ‖crossLeft a‖ ≤ 1*‖a‖
      simpa only [one_mul] using crossLeft_norm_le a)

theorem crossBilinear_apply (a b : Space) : crossBilinear a b = cross a b := rfl

theorem cross_hasDerivAt {p q : ℝ → Space} {p' q' : Space} {t : ℝ}
    (hp : HasDerivAt p p' t) (hq : HasDerivAt q q' t) :
    HasDerivAt (fun s => cross (p s) (q s)) (cross p' (q t) + cross (p t) q') t := by
  have h := (crossBilinear.hasFDerivAt.comp_hasDerivAt t hp).clm_apply hq
  simpa only [Function.comp_def, crossBilinear_apply] using h

theorem cross_hasDerivWithinAt {p q : ℝ → Space} {p' q' : Space} {t : ℝ} {S : Set ℝ}
    (hp : HasDerivWithinAt p p' S t) (hq : HasDerivWithinAt q q' S t) :
    HasDerivWithinAt (fun s => cross (p s) (q s)) (cross p' (q t) + cross (p t) q') S t := by
  have h := (crossBilinear.hasFDerivAt.comp_hasDerivWithinAt t hp).clm_apply hq
  simpa only [Function.comp_def, crossBilinear_apply] using h

theorem inner_cross_first (p q : Space) : ⟪p,cross p q⟫_ℝ = 0 := by
  rw [← dot_eq_inner]
  exact dot_self_cross (ofLp p) (ofLp q)

theorem inner_cross_second (p q : Space) : ⟪q,cross p q⟫_ℝ = 0 := by
  rw [← dot_eq_inner]
  exact dot_cross_self (ofLp p) (ofLp q)

theorem inner_cross_exchange_first (p q r : Space) :
    ⟪p,cross q r⟫_ℝ = -⟪q,cross p r⟫_ℝ := by
  simp only [← dot_eq_inner, cross]
  rw [triple_product_permutation, ← cross_anticomm (ofLp p) (ofLp r), dotProduct_neg]

theorem inner_cross_exchange_last (p q r : Space) :
    ⟪p,cross q r⟫_ℝ = -⟪r,cross q p⟫_ℝ := by
  simp only [← dot_eq_inner, cross]
  rw [triple_product_permutation, triple_product_permutation (ofLp q) (ofLp r) (ofLp p),
    ← cross_anticomm (ofLp q) (ofLp p), dotProduct_neg]

def frame (p q : Space) : Fin 3 → Space := ![p, q, cross p q]

def frameRate (B : Space →L[ℝ] Space) (p q : Space) : Fin 3 → Space :=
  ![rayRate B p, velocityRate B p q,
    cross (rayRate B p) q + cross p (velocityRate B p q)]

def frameMatrix (B : Space →L[ℝ] Space) (p q : Space) (i j : Fin 3) : ℝ :=
  ⟪frame p q i, B (frame p q j)⟫_ℝ

def normalizedFrame (m v : ℝ → Space) (t : ℝ) : Fin 3 → Space := frame (unit (m t)) (unit (v t))

theorem normalizedFrame_hasDerivAt (B : Space →L[ℝ] Space) {m v : ℝ → Space} {t : ℝ}
    (hm : HasDerivAt m (-B.adjoint (m t)) t)
    (hv : HasDerivAt v (-B (v t) + (2*⟪m t,B (v t)⟫_ℝ / ‖m t‖^2) • m t) t)
    (hm0 : m t ≠ 0) (hv0 : v t ≠ 0) (hmv : ⟪m t,v t⟫_ℝ = 0) (i : Fin 3) :
    HasDerivAt (fun s => normalizedFrame m v s i)
      (frameRate B (unit (m t)) (unit (v t)) i) t := by
  have hp := normalized_ray_hasDerivAt B hm hm0
  have hq := normalized_velocity_hasDerivAt B hv hv0 hmv
  fin_cases i
  · exact hp
  · exact hq
  · exact cross_hasDerivAt hp hq

theorem normalizedFrame_hasDerivWithinAt (B : Space →L[ℝ] Space)
    {m v : ℝ → Space} {t : ℝ} {S : Set ℝ}
    (hm : HasDerivWithinAt m (-B.adjoint (m t)) S t)
    (hv : HasDerivWithinAt v (-B (v t) + (2*⟪m t,B (v t)⟫_ℝ / ‖m t‖^2) • m t) S t)
    (hm0 : m t ≠ 0) (hv0 : v t ≠ 0) (hmv : ⟪m t,v t⟫_ℝ = 0) (i : Fin 3) :
    HasDerivWithinAt (fun s => normalizedFrame m v s i)
      (frameRate B (unit (m t)) (unit (v t)) i) S t := by
  have hp := normalized_ray_hasDerivWithinAt B hm hm0
  have hq := normalized_velocity_hasDerivWithinAt B hv hv0 hmv
  fin_cases i
  · exact hp
  · exact hq
  · exact cross_hasDerivWithinAt hp hq

end EulerPacketMovingFrame
