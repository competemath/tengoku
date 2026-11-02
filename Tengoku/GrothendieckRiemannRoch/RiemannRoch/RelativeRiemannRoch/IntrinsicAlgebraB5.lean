/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.RelativeRiemannRoch.WeightAlgebraRG6B

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# B5 (algebra): from the intrinsic Adams–Riemann–Roch identity to the RG6B shapes

Pure algebra.  `K` plays `K₀(X)_ℚ`, `L` plays `K₀(Y)_ℚ`, `psiK`, `psiL` the Adams operations
`ψʲ`, `F` the pushforward `f_!`, and `t` the class `θʲ(T_f^∨)⁻¹`.  From the *intrinsic ARR*
`ψʲ (F x) = F (t · ψʲ x)` we derive

* `B5.E1_of_arr`: for `χ : L →ₗ ℚ` with `χ ∘ ψ = χ`, the functional `χ ∘ F` satisfies (E1)
  `χ' x = χ' (t * ψ x)` of `RG6B`;
* `B5.Phi`: the operator `Φ w = F (τ⁻¹ * w)`, and `B5.Phi_psi`: `Φ (ψ w) = jᵈ • ψ (Φ w)`
  whenever `ψ τ = s τ`, `s = jᵈ • t`, `τ τ⁻¹ = 1` (the weight-shift relation).
-/

set_option autoImplicit false

namespace B5

section Alg

variable {K L : Type*} [CommRing K] [Algebra ℚ K] [CommRing L] [Algebra ℚ L]

/-- The intrinsic ARR identity in abstract form.-/
def ARRAbs (psiK : K →ₐ[ℚ] K) (psiL : L →ₐ[ℚ] L) (F : K →ₗ[ℚ] L) (t : K) : Prop :=
  ∀ x, psiL (F x) = F (t * psiK x)

/-- (E1) of `RG6B` for `χ ∘ F`, from the ARR identity and `ψ`-invariance of `χ`.-/
theorem E1_of_arr {psiK : K →ₐ[ℚ] K} {psiL : L →ₐ[ℚ] L} {F : K →ₗ[ℚ] L} {t : K}
    (h : ARRAbs psiK psiL F t) (chi : L →ₗ[ℚ] ℚ) (hchi : ∀ y, chi (psiL y) = chi y) (x : K) :
    (chi.comp F) x = (chi.comp F) (t * psiK x) := by
  simp only [LinearMap.comp_apply]
  rw [← h x, hchi]

/-- The operator `Φ w = F (τ⁻¹ * w)`.-/
def Phi (F : K →ₗ[ℚ] L) (τi : K) : K →ₗ[ℚ] L := F.comp (LinearMap.mulLeft ℚ τi)

theorem Phi_apply (F : K →ₗ[ℚ] L) (τi w : K) : Phi F τi w = F (τi * w) := rfl

/-- **Weight-shift relation** `Φ (ψ w) = jᵈ • ψ (Φ w)`.-/
theorem Phi_psi {psiK : K →ₐ[ℚ] K} {psiL : L →ₐ[ℚ] L} {F : K →ₗ[ℚ] L} {t : K}
    (h : ARRAbs psiK psiL F t) {j d : ℕ} {s τ τi : K} (hs : s = (j : ℚ) ^ d • t)
    (hτ : psiK τ = s * τ) (hi : τ * τi = 1) (w : K) :
    Phi F τi (psiK w) = (j : ℚ) ^ d • psiL (Phi F τi w) := by
  have e : s * psiK τi = τi :=
    RG6B.s_mul_psi_inv (psi := (psiK : K →+* K)) hτ hi
  rw [Phi_apply, Phi_apply, h, ← map_smul]
  congr 1
  calc τi * psiK w = psiK w * (s * psiK τi) := by rw [e]; ring
    _ = psiK w * (((j : ℚ) ^ d • t) * psiK τi) := by rw [hs]
    _ = (j : ℚ) ^ d • (t * psiK (τi * w)) := by
        rw [map_mul, smul_mul_assoc, mul_smul_comm]; congr 1; ring

end Alg

end B5
