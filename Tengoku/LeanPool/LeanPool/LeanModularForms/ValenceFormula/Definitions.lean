/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Seed.NumberTheory.Modular
public import Tengoku.Seed.NumberTheory.ModularForms.QExpansion
public import Tengoku.Seed.RingTheory.PowerSeries.Order

namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Valence Formula Definitions

Definitions for the valence formula for SL₂(ℤ): elliptic points i and ρ,
orbifold coefficients, the order of vanishing, and the canonical fundamental domain.

We use `ModularGroup.fd` (notation `𝒟`) from mathlib for the standard fundamental domain.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The elliptic point i as an element of ℍ. -/
def ellipticPointI' : UpperHalfPlane := ⟨I, by simp [Complex.I_im]⟩

/-- The elliptic point `i` as a complex number. -/
abbrev ellipticPointI : ℂ := (ellipticPointI' : ℂ)

/-- The elliptic point ρ = e^{2πi/3} = -1/2 + (√3/2)i as an element of ℍ. -/
def ellipticPointRho' : UpperHalfPlane :=
  ⟨-1/2 + (Real.sqrt 3 / 2) * I, by
    simp_all⟩

/-- The elliptic point `ρ` as a complex number. -/
abbrev ellipticPointRho : ℂ := (ellipticPointRho' : ℂ)

/-- The T-translate ρ+1 = e^{πi/3} = 1/2 + (√3/2)i. -/
def ellipticPointRhoPlusOne' : UpperHalfPlane :=
  ⟨1/2 + (Real.sqrt 3 / 2) * I, by
    simp_all⟩

/-- The T-translate `ρ + 1` as a complex number. -/
abbrev ellipticPointRhoPlusOne : ℂ := (ellipticPointRhoPlusOne' : ℂ)

/--
@isnad1 id=eq.0h0v.s4.e0202f1befe3 from=translated src=- shape=7132d4c4 vocab=03e478ab
-/
theorem ellipticPointRho_add_one_eq :
    ellipticPointRho + 1 = ellipticPointRhoPlusOne := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) + 1 = 1/2 + (Real.sqrt 3 / 2) * I; ring

private lemma normSq_half_add_sqrt3_half_I (a : ℝ) (ha : a ^ 2 = 1 / 4) :
    Complex.normSq ((a : ℂ) + (Real.sqrt 3 / 2) * I) = 1 := by
  have h1 : ((a : ℝ) : ℂ) + (Real.sqrt 3 / 2) * I =
      ((a : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, Complex.normSq_add_mul_I, ha,
    show (Real.sqrt 3 / 2) ^ 2 = 3 / 4 from by
      rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num]
  ring

private lemma rho_normSq_eq_one : Complex.normSq (ellipticPointRho' : ℂ) = 1 := by
  change Complex.normSq (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  rw [show (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) = ((-1/2 : ℝ) : ℂ) + (Real.sqrt 3 / 2) * I from by
    push_cast; ring]
  exact normSq_half_add_sqrt3_half_I (-1/2) (by norm_num)

private lemma rho_plus_one_normSq_eq_one :
    Complex.normSq (ellipticPointRhoPlusOne' : ℂ) = 1 := by
  change Complex.normSq (1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  rw [show (1/2 + (Real.sqrt 3 / 2) * I : ℂ) = ((1/2 : ℝ) : ℂ) + (Real.sqrt 3 / 2) * I from by
    push_cast; ring]
  exact normSq_half_add_sqrt3_half_I (1/2) (by norm_num)

/--
@isnad1 id=eq.0h0v.s3.b3248dbdab9e from=translated src=- shape=b3c4969c vocab=1e15f2b7
-/
theorem ellipticPointRhoPlusOne_norm : ‖ellipticPointRhoPlusOne‖ = 1 := by
  rw [Complex.norm_def, rho_plus_one_normSq_eq_one, Real.sqrt_one]

/--
@isnad1 id=eq.0h0v.s3.0daa47d23b07 from=translated src=- shape=b3c4969c vocab=824e2a2b
-/
theorem ellipticPointRho_norm : ‖ellipticPointRho‖ = 1 := by
  rw [Complex.norm_def, rho_normSq_eq_one, Real.sqrt_one]

/--
@isnad1 id=mem.0h0v.s3.d88261b62f32 from=translated src=- shape=d1530203 vocab=a7dcafc0
-/
theorem ellipticPointI_mem_fd : ellipticPointI' ∈ 𝒟 := by
  simp only [ModularGroup.fd, ellipticPointI', mem_ofPred_eq]
  constructor
  · norm_num [Complex.normSq]
  · change |(I : ℂ).re| ≤ (1 : ℝ) / 2
    norm_num

/--
@isnad1 id=mem.0h0v.s3.86786725d2be from=translated src=- shape=d1530203 vocab=7b7be35e
-/
theorem ellipticPointRho_mem_fd : ellipticPointRho' ∈ 𝒟 := by
  simp only [ModularGroup.fd, ellipticPointRho', mem_ofPred_eq]
  exact ⟨rho_normSq_eq_one ▸ le_refl _, by simp only [UpperHalfPlane.re]; norm_num⟩

/--
@isnad1 id=ne.0h0v.s2.d3fd53ac4628 from=translated src=- shape=54c8eceb vocab=aae6552c
-/
lemma ellipticPointI_ne_rho : ellipticPointI' ≠ ellipticPointRho' := by
  intro h
  have h1 : (ellipticPointI' : ℂ).re = (ellipticPointRho' : ℂ).re := by rw [h]
  simp only [ellipticPointI', ellipticPointRho'] at h1; norm_num at h1

/-- Order of vanishing of f at a point in ℍ. -/
def orderOfVanishingAt' (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℤ :=
  (meromorphicOrderAt (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (z : ℂ)).untop₀

/-- The order of vanishing at the cusp (in the q-expansion). -/
noncomputable def orderAtCusp' {k : ℤ} (f : ModularForm (CongruenceSubgroup.Gamma 1) k) : ℤ :=
  (UpperHalfPlane.qExpansion 1 f).order.toNat

end
