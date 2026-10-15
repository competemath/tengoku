/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku

/-!
# Valence Formula Definitions

Definitions for the valence formula for SL₂(ℤ): elliptic points i and ρ,
orbifold coefficients, the order of vanishing, and the canonical fundamental domain.

We use `ModularGroup.fd` (notation `𝒟`) from mathlib for the standard fundamental domain.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular

noncomputable section

/-- The elliptic point `i` as an element of ℍ. -/
def ellipticPointI' : UpperHalfPlane := ⟨I, by simp [Complex.I_im]⟩

/-- The elliptic point `ρ = e^{2πi/3} = -1/2 + (√3/2)i` as an element of ℍ. -/
def ellipticPointRho' : UpperHalfPlane :=
  ⟨-1/2 + (Real.sqrt 3 / 2) * I, by
    simp only [add_im, neg_im, one_im, div_im, mul_im, I_re, I_im]
    norm_num⟩

/-- The elliptic point `ρ` as a complex number. -/
abbrev ellipticPointRho : ℂ := (ellipticPointRho' : ℂ)

/-- The T-translate `ρ + 1 = e^{πi/3} = 1/2 + (√3/2)i`. -/
def ellipticPointRhoPlusOne' : UpperHalfPlane :=
  ⟨1/2 + (Real.sqrt 3 / 2) * I, by
    simp only [add_im, one_im, div_im, mul_im, I_re, I_im]
    norm_num⟩

/-- The T-translate `ρ + 1` as a complex number. -/
abbrev ellipticPointRhoPlusOne : ℂ := (ellipticPointRhoPlusOne' : ℂ)

/--
@isnad1 id=eq.0h0v.s4.89a177338431 from=translated src=- shape=7132d4c4 vocab=6ba92002
-/
theorem ellipticPointRho_add_one_eq :
    ellipticPointRho + 1 = ellipticPointRhoPlusOne := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) + 1 = 1/2 + (Real.sqrt 3 / 2) * I
  ring

private lemma rho_normSq_eq_one : Complex.normSq (ellipticPointRho' : ℂ) = 1 := by
  change Complex.normSq (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  have h1 : (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) =
      ((-1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, Complex.normSq_add_mul_I]
  nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]

private lemma rho_plus_one_normSq_eq_one :
    Complex.normSq (ellipticPointRhoPlusOne' : ℂ) = 1 := by
  change Complex.normSq (1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  have h1 : (1/2 + (Real.sqrt 3 / 2) * I : ℂ) =
      ((1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, Complex.normSq_add_mul_I]
  nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]

/--
@isnad1 id=eq.0h0v.s3.480f0c1ea6d1 from=translated src=- shape=b3c4969c vocab=a53fd7f8
-/
theorem ellipticPointRhoPlusOne_norm : ‖ellipticPointRhoPlusOne‖ = 1 := by
  change Real.sqrt (Complex.normSq _) = 1
  rw [rho_plus_one_normSq_eq_one, Real.sqrt_one]

/--
@isnad1 id=eq.0h0v.s3.01ec8b6351ca from=translated src=- shape=b3c4969c vocab=725b3984
-/
theorem ellipticPointRho_norm : ‖ellipticPointRho‖ = 1 := by
  change Real.sqrt (Complex.normSq _) = 1
  rw [rho_normSq_eq_one, Real.sqrt_one]

/--
@isnad1 id=mem.0h0v.s3.bf5b186d5093 from=translated src=- shape=d1530203 vocab=16257a5d
-/
theorem ellipticPointI_mem_fd : ellipticPointI' ∈ 𝒟 := by
  refine ⟨?_, ?_⟩
  · simp [ellipticPointI', Complex.normSq_I]
  · simp only [ellipticPointI', UpperHalfPlane.re]; norm_num

/--
@isnad1 id=mem.0h0v.s3.a4098fe64ae5 from=translated src=- shape=d1530203 vocab=33936d57
-/
theorem ellipticPointRho_mem_fd : ellipticPointRho' ∈ 𝒟 := by
  refine ⟨rho_normSq_eq_one.ge, ?_⟩
  simp only [ellipticPointRho', UpperHalfPlane.re]; norm_num

/--
@isnad1 id=ne.0h0v.s2.44003e1f10cb from=translated src=- shape=54c8eceb vocab=30211f67
-/
lemma ellipticPointI_ne_rho : ellipticPointI' ≠ ellipticPointRho' := by
  intro h
  have h1 : (ellipticPointI' : ℂ).re = (ellipticPointRho' : ℂ).re := by rw [h]
  simp only [ellipticPointI', ellipticPointRho'] at h1
  norm_num at h1

/-- Order of vanishing of `f` at a point in ℍ. -/
def orderOfVanishingAt' (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℤ :=
  (meromorphicOrderAt (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (z : ℂ)).untop₀

/-- The order of vanishing at the cusp (in the q-expansion). -/
noncomputable def orderAtCusp' {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma 1) k) : ℤ :=
  (UpperHalfPlane.qExpansion 1 f).order.toNat

end
