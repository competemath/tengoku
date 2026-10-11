/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Integrability
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.Energy.TimeCutoff
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import Tengoku

/-!
# AELocal Energy

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private lemma spatialPartial_eq_zero_of_not_mem_tsupport
    {ψ : Vec3 × ℝ → ℝ} (_ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) (i : Fin 3) :
    spatialPartialProd ψ i z = 0 := by
  change (fderiv ℝ (fun x : Vec3 => ψ (x, z.2)) z.1) (basisVec i) = 0
  have hopen : (tsupport ψ)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport ψ).isOpen_compl.mem_nhds hz
  have hmap : Continuous (fun x : Vec3 => (x, z.2)) :=
    Continuous.prodMk continuous_id continuous_const
  have hev : (fun x : Vec3 => ψ (x, z.2)) =ᶠ[𝓝 z.1] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds hopen] with x hx
    by_contra hne
    exact hx (subset_tsupport (f := ψ) (Function.mem_support.mpr hne))
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

private lemma timePartial_eq_zero_of_not_mem_tsupport
    {ψ : Vec3 × ℝ → ℝ} (_ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) :
    timePartialProd ψ z = 0 := by
  change (fderiv ℝ (fun s : ℝ => ψ (z.1, s)) z.2) 1 = 0
  have hopen : (tsupport ψ)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport ψ).isOpen_compl.mem_nhds hz
  have hmap : Continuous (fun s : ℝ => (z.1, s)) :=
    Continuous.prodMk continuous_const continuous_id
  have hev : (fun s : ℝ => ψ (z.1, s)) =ᶠ[𝓝 z.2] (fun _ => (0 : ℝ)) := by
    filter_upwards [hmap.continuousAt.preimage_mem_nhds hopen] with s hs
    by_contra hne
    exact hs (subset_tsupport (f := ψ) (Function.mem_support.mpr hne))
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

private lemma spatialSecondPartial_eq_zero_of_not_mem_tsupport
    {ψ : Vec3 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {z : Vec3 × ℝ} (hz : z ∉ tsupport ψ) (i j : Fin 3) :
    spatialSecondPartialProd ψ i j z = 0 := by
  change spatialPartialProd (fun w => spatialPartialProd ψ i w) j z = 0
  change (fderiv ℝ (fun x : Vec3 => spatialPartialProd ψ i (x, z.2)) z.1)
      (basisVec j) = 0
  have hopen : (tsupport ψ)ᶜ ∈ 𝓝 z :=
    (isClosed_tsupport ψ).isOpen_compl.mem_nhds hz
  have hzero :
      (fun w : Vec3 × ℝ => spatialPartialProd ψ i w) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen] with w hw
    exact spatialPartial_eq_zero_of_not_mem_tsupport hψ hw i
  have hmap : Continuous (fun x : Vec3 => (x, z.2)) :=
    Continuous.prodMk continuous_id continuous_const
  have hev :
      (fun x : Vec3 => spatialPartialProd ψ i (x, z.2)) =ᶠ[𝓝 z.1]
        (fun _ => (0 : ℝ)) := hmap.continuousAt.preimage_mem_nhds hzero
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp

private theorem tsupport_parabolic_eq_energy (g : ParabolicPoint → ℝ) :
    tsupport g = parabolicHomeomorph ⁻¹' (tsupport fun q : Vec3 × ℝ => g q) := by
  have hsupp : Function.support g =
      parabolicHomeomorph ⁻¹' (Function.support fun q : Vec3 × ℝ => g q) := by
    ext z
    rw [Set.mem_preimage, Function.mem_support, Function.mem_support]
    rfl
  rw [tsupport, tsupport, hsupp, ← parabolicHomeomorph.preimage_closure]

private lemma localEnergyRhs_eq_zero_of_not_mem_tsupport
    {u : Vec3 × ℝ → Vec3} {p : Vec3 × ℝ → ℝ}
    {f : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {z : Vec3 × ℝ}
    (hz : z ∉ tsupport ψ) : localEnergyRhs u p f ψ z = 0 := by
  have hψ0 : ψ z = 0 := by
    by_contra hne
    exact hz (subset_tsupport (f := ψ) (Function.mem_support.mpr hne))
  have ht : timePartialProd ψ z = 0 := timePartial_eq_zero_of_not_mem_tsupport hψ hz
  have hs : ∀ i : Fin 3, spatialPartialProd ψ i z = 0 := fun i =>
    spatialPartial_eq_zero_of_not_mem_tsupport hψ hz i
  have hss : ∀ i : Fin 3, spatialSecondPartialProd ψ i i z = 0 := fun i =>
    spatialSecondPartial_eq_zero_of_not_mem_tsupport hψ hz i i
  simp [localEnergyRhs, hψ0, ht, hs, hss]

theorem localEnergyRhs_eq_zero_of_not_mem_tsupport_public
    {u : Vec3 × ℝ → Vec3} {p : Vec3 × ℝ → ℝ}
    {f : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {z : Vec3 × ℝ}
    (hz : z ∉ tsupport ψ) : localEnergyRhs u p f ψ z = 0 :=
  localEnergyRhs_eq_zero_of_not_mem_tsupport hψ hz

private lemma localEnergyRhs_eq_zero_of_not_mem_parabolic_tsupport
    {u : Vec3 × ℝ → Vec3} {p : Vec3 × ℝ → ℝ}
    {f : Vec3 × ℝ → Vec3} {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {z : ParabolicPoint}
    (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) :
    localEnergyRhs u p f ψ z = 0 := by
  have hz' : (show Vec3 × ℝ from z) ∉ tsupport ψ := by
    intro hmem
    apply hz
    rw [tsupport_parabolic_eq_energy (show ParabolicPoint → ℝ from ψ)]
    exact hmem
  exact localEnergyRhs_eq_zero_of_not_mem_tsupport hψ hz'

private lemma diss_integrable_and_rhs_integrable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hψ_nonneg : ∀ z, 0 ≤ ψ z) :
    Integrable (fun z => spatialGradientSq u Du z * ψ z) volume ∧
      Integrable (fun z => localEnergyRhs u p f ψ z) volume ∧
      Integrable (fun z => (vec3EuclideanNorm (u z)) ^ 2 * ψ z) volume := by
  have he : Integrable (fun z => (vec3EuclideanNorm (u z)) ^ 2 * ψ z) volume :=
    u_sq_mul_test_integrable hsol hψ
  rcases hsol with ⟨_, _, _, _, _, _, _, _, henergy⟩
  obtain ⟨hdiss, hrhs, -⟩ := henergy ψ hψ hψ_nonneg
  have hdiss_support : Function.support
      (fun z : ParabolicPoint => spatialGradientSq u Du z * ψ z) ⊆
        tsupport (show ParabolicPoint → ℝ from ψ) := by
    intro z hz
    by_contra hnot
    apply hz
    simp only [mul_eq_zero]
    right
    exact not_not.mp (fun hne => hnot (subset_tsupport
      (f := (show ParabolicPoint → ℝ from ψ)) (Function.mem_support.mpr hne)))
  have hrhs_support : Function.support
      (fun z : ParabolicPoint => localEnergyRhs u p f ψ z) ⊆
        tsupport (show ParabolicPoint → ℝ from ψ) := by
    intro z hz
    by_contra hnot
    apply hz
    exact localEnergyRhs_eq_zero_of_not_mem_parabolic_tsupport
      hψ.1 hnot
  have hdiss' : IntegrableOn
      (fun z : ParabolicPoint => spatialGradientSq u Du z * ψ z)
      (tsupport (show ParabolicPoint → ℝ from ψ)) volume := hdiss
  have hrhs' : IntegrableOn
      (fun z : ParabolicPoint => localEnergyRhs u p f ψ z)
      (tsupport (show ParabolicPoint → ℝ from ψ)) volume := by
    simpa only [localEnergyRhs, timePartialProd, spatialSecondPartialProd,
      spatialPartialProd] using hrhs
  refine ⟨(integrableOn_iff_integrable_of_support_subset hdiss_support).mp hdiss',
    (integrableOn_iff_integrable_of_support_subset hrhs_support).mp hrhs', ?_⟩
  exact he

theorem suitableWeakSolution_energy_integrable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    (hψ_nonneg : ∀ z, 0 ≤ ψ z) :
    Integrable (fun z => spatialGradientSq u Du z * ψ z) volume ∧
      Integrable (fun z => localEnergyRhs u p f ψ z) volume ∧
      Integrable (fun z => (vec3EuclideanNorm (u z)) ^ 2 * ψ z) volume :=
  diss_integrable_and_rhs_integrable hsol hψ hψ_nonneg

end CKN
