/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/
module

public import Tengoku.LeanPool.LeanPool.PLAcceleratedNesterovLean.Core.NesterovSeqGen

/-!
# Coercivity Step 1: Extract Component Bounds from Lyapunov Definition

From L_n = (f(x_n) - f⋆) + ½‖u_n‖² + λ‖Pv_n‖², we directly read off:
  - f(x_n) - f⋆ ≤ L_n
  - ‖u_n‖² ≤ 2 L_n
  - ‖P v_n‖² ≤ L_n / λ

Then from u_n = P⊥v_n + √μ' e_n (triangle inequality):
  A_n := ‖P⊥v_n‖ ≤ ‖u_n‖ + √μ'‖e_n‖ ≤ √(2L_n) + B_n

And T_n := ‖P v_n‖ ≤ √(L_n/λ).
-/

@[expose] public section

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped NNReal

/-- From the Lyapunov definition, f(x) - f⋆ ≤ L when L = gap + ½‖u‖² + λ‖Pv‖².
@isnad1 id=le.5h5v.s6.a27c4af018df from=translated src=- shape=f6c90543 vocab=70d00927
-/
theorem lyapunov_gap_bound (gap u_sq lam Pv_sq L : ℝ)
    (_hgap : 0 ≤ gap) (hu : 0 ≤ u_sq) (hlam : 0 < lam) (hPv : 0 ≤ Pv_sq)
    (hL : L = gap + u_sq / 2 + lam * Pv_sq) :
    gap ≤ L := by
  nlinarith [mul_nonneg (le_of_lt hlam) hPv]

/-- Variant: gap ≤ L when λ ≥ 0 (weak inequality, handles a = 1 edge case).
    Unfolds the Lyapunov definition directly; requires √(μ'·η) ≤ 1.
    State-based version: works for arbitrary NesterovState.
@isnad1 id=le.1h7v.s8.c5650817e95b from=translated src=- shape=885c8398 vocab=37dc94f9
-/
theorem gap_le_lyapunovOfState_of_sqrt_le {d : ℕ} (P : E d →L[ℝ] E d) (μ' : ℝ) (π : E d → E d)
    (f : E d → ℝ) (η : ℝ) (s : NesterovState d)
    (ha_le1 : Real.sqrt (μ' * η) ≤ 1) :
    f s.x - fStar f ≤ lyapunovOfState P μ' π f η s := by
  simp only [lyapunovOfState]
  have hlam_nn : 0 ≤ (1 + Real.sqrt (μ' * η)) ^ 2 / (2 * (1 - Real.sqrt (μ' * η))) :=
    div_nonneg (sq_nonneg _) (by nlinarith)
  nlinarith [sq_nonneg ‖auxVarOfState P μ' π η s‖,
             mul_nonneg hlam_nn (sq_nonneg ‖P s.v‖)]

/-- Variant: gap ≤ L when λ ≥ 0 (weak inequality, handles a = 1 edge case).
    Unfolds the Lyapunov definition directly; requires √(μ'·η) ≤ 1.
@isnad1 id=le.1h9v.s8.da72994b0ed9 from=translated src=- shape=116b7faf vocab=53e3dbb6
-/
theorem gap_le_lyapunov_of_sqrt_le {d : ℕ} (P : E d →L[ℝ] E d) (μ' : ℝ) (π : E d → E d)
    (f : E d → ℝ) (η ρ : ℝ) (x₁ : E d) (n : ℕ)
    (ha_le1 : Real.sqrt (μ' * η) ≤ 1) :
    f (nesterovSeq f η ρ x₁ n).x - fStar f ≤ lyapunov P μ' π f η ρ x₁ n := by
  rw [← lyapunovOfState_eq_lyapunov P μ' π f η ρ x₁ n]
  exact gap_le_lyapunovOfState_of_sqrt_le P μ' π f η _ ha_le1

/-- From the Lyapunov definition, ‖u‖² ≤ 2L.
@isnad1 id=le.5h5v.s6.06a43e1557d6 from=translated src=- shape=73b4aa37 vocab=70d00927
-/
theorem lyapunov_u_bound (gap u_sq lam Pv_sq L : ℝ)
    (hgap : 0 ≤ gap) (_hu : 0 ≤ u_sq) (hlam : 0 < lam) (hPv : 0 ≤ Pv_sq)
    (hL : L = gap + u_sq / 2 + lam * Pv_sq) :
    u_sq ≤ 2 * L := by
  nlinarith [mul_nonneg (le_of_lt hlam) hPv]

/-- From the Lyapunov definition, ‖Pv‖² ≤ L/λ.
@isnad1 id=le.5h5v.s6.a20269697a03 from=translated src=- shape=e5ca5ec2 vocab=70d00927
-/
theorem lyapunov_Pv_bound (gap u_sq lam Pv_sq L : ℝ)
    (hgap : 0 ≤ gap) (hu : 0 ≤ u_sq) (hlam : 0 < lam) (_hPv : 0 ≤ Pv_sq)
    (hL : L = gap + u_sq / 2 + lam * Pv_sq) :
    Pv_sq ≤ L / lam := by
  rw [le_div_iff₀ hlam]
  nlinarith

/-- Triangle inequality on u = Pperp_v + √μ' · e gives ‖Pperp_v‖ ≤ ‖u‖ + √μ'·‖e‖.
@isnad1 id=le.1h5v.s7.f8960c320993 from=translated src=- shape=da02d8b5 vocab=ef31a4cf
-/
theorem perp_v_bound_from_u (u Pperp_v e : E d) (sqrtmu : ℝ)
    (hu_def : u = Pperp_v + sqrtmu • e) :
    ‖Pperp_v‖ ≤ ‖u‖ + |sqrtmu| * ‖e‖ := by
  have h : Pperp_v = u - sqrtmu • e := by
    rw [hu_def]; abel
  calc ‖Pperp_v‖ = ‖u - sqrtmu • e‖ := by rw [h]
    _ ≤ ‖u‖ + ‖sqrtmu • e‖ := norm_sub_le u (sqrtmu • e)
    _ = ‖u‖ + |sqrtmu| * ‖e‖ := by rw [norm_smul, Real.norm_eq_abs]

end PLAcceleratedNesterovLean
