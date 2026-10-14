/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Tengoku

/-!
# Param Extension

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The scalar pairing of a parameterized test family with zeroth, first, and
second order slice data on a fixed compact set. -/
def parametricPairing {X : Type} (Ψ : X → Vec3 → ℝ)
    (g₀ : Vec3 → ℝ) (g₁ : Vec3 → Vec3)
    (g₂ : Vec3 → Fin 3 → Fin 3 → ℝ) (x : X) : ℝ :=
  (∫ y, g₀ y * Ψ x y) +
    ∑ i, (∫ y, g₁ y i * spatialDeriv (Ψ x) i y) +
    ∑ i, ∑ j, (∫ y, g₂ y i j * mixedSecond (Ψ x) i j y)

/-- A continuous scalar pairing which vanishes on a dense parameter set
vanishes for every parameter.
@isnad1 id=eq.3h7v.s6.6977de7d4c41 from=translated src=- shape=cd443aba vocab=e7dcfa05
-/
theorem parametricPairing_eq_zero_of_dense {X : Type} [TopologicalSpace X]
    {Ψ : X → Vec3 → ℝ}
    {g₀ : Vec3 → ℝ} {g₁ : Vec3 → Vec3}
    {g₂ : Vec3 → Fin 3 → Fin 3 → ℝ} {D : Set X}
    (hD : Dense D)
    (hcont : Continuous (parametricPairing Ψ g₀ g₁ g₂))
    (hzero : ∀ x ∈ D, parametricPairing Ψ g₀ g₁ g₂ x = 0) :
    ∀ x, parametricPairing Ψ g₀ g₁ g₂ x = 0 := by
  have heq : parametricPairing Ψ g₀ g₁ g₂ = fun _ => 0 :=
    Continuous.ext_on hD hcont continuous_const hzero
  intro x
  exact congrFun heq x

/-- A continuous scalar pairing which vanishes on a countable dense parameter
set vanishes for every parameter.
@isnad1 id=eq.4h7v.s6.57d75f8ac6c1 from=translated src=- shape=fb1640dd vocab=80fa46c5
-/
theorem parametricPairing_eq_zero_of_countable_dense
    {X : Type} [TopologicalSpace X]
    {Ψ : X → Vec3 → ℝ}
    {g₀ : Vec3 → ℝ} {g₁ : Vec3 → Vec3}
    {g₂ : Vec3 → Fin 3 → Fin 3 → ℝ} {D : Set X}
    (_ : D.Countable) (hD : Dense D)
    (hcont : Continuous (parametricPairing Ψ g₀ g₁ g₂))
    (hzero : ∀ x ∈ D, parametricPairing Ψ g₀ g₁ g₂ x = 0) :
    ∀ x, parametricPairing Ψ g₀ g₁ g₂ x = 0 := by
  exact parametricPairing_eq_zero_of_dense hD hcont hzero

end CKN
