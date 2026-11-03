/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.Seed.Algebra.Module.LocalizedModule.Submodule
import Tengoku.Seed.Algebra.Module.LocalizedModule.Exact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Cohomology of a localized three-term complex

Three degreewise module localizations that commute with consecutive differentials
induce a localization of the kernel modulo the preceding image. This is a
module-level cohomology statement; it does not identify a particular derived
category Hom or assert geometric base change.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace IsLocalizedModule

variable {R : Type*} [CommRing R] (S : Submonoid R)

variable {M₀ M₁ M₂ N₀ N₁ N₂ : Type*}
  [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
  [AddCommGroup N₀] [AddCommGroup N₁] [AddCommGroup N₂]
  [Module R M₀] [Module R M₁] [Module R M₂]
  [Module R N₀] [Module R N₁] [Module R N₂]
  (f₀ : M₀ →ₗ[R] N₀) (f₁ : M₁ →ₗ[R] N₁) (f₂ : M₂ →ₗ[R] N₂)
  [IsLocalizedModule S f₀] [IsLocalizedModule S f₁] [IsLocalizedModule S f₂]
  (d₀ : M₀ →ₗ[R] M₁) (d₁ : M₁ →ₗ[R] M₂) (hd : d₁.comp d₀ = 0)

/-- The first differential, with codomain restricted to cycles of the second.-/
def boundaryToCycles : M₀ →ₗ[R] d₁.ker :=
  d₀.codRestrict d₁.ker (fun x => by
    have h := LinearMap.congr_fun hd x
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.mem_ker] using h)

/-- The localized second differential.-/
def localizedDifferential : N₁ →ₗ[R] N₂ :=
  (IsLocalizedModule.map S f₁ f₂) d₁

/-- The canonical localization map on cycles.-/
def localizedCyclesMap :
    d₁.ker →ₗ[R] (localizedDifferential S f₁ f₂ d₁).ker :=
  LinearMap.toKerIsLocalized S f₁ f₂ d₁

private def localizedBoundaryToCyclesViaMap :
    N₀ →ₗ[R] (localizedDifferential S f₁ f₂ d₁).ker :=
  letI : Module (Localization S) N₁ := IsLocalizedModule.module S f₁
  letI : IsScalarTower R (Localization S) N₁ :=
    IsLocalizedModule.isScalarTower_module S f₁
  letI : Module (Localization S) N₂ := IsLocalizedModule.module S f₂
  letI : IsScalarTower R (Localization S) N₂ :=
    IsLocalizedModule.isScalarTower_module S f₂
  letI : IsLocalizedModule S (localizedCyclesMap S f₁ f₂ d₁) :=
    LinearMap.toKerLocalized_isLocalizedModule (Localization S) S f₁ f₂ d₁
  (IsLocalizedModule.map S f₀ (localizedCyclesMap S f₁ f₂ d₁))
    (boundaryToCycles d₀ d₁ hd)

include hd in
private theorem localized_comp_zero :
    ((IsLocalizedModule.map S f₁ f₂) d₁).comp
      ((IsLocalizedModule.map S f₀ f₁) d₀) = 0 := by
  rw [← IsLocalizedModule.map_comp' S f₀ f₁ f₂ d₀ d₁, hd]
  simp

/-- The localized first differential, with codomain restricted to cycles of
the localized second differential.-/
def localizedBoundaryToCycles :
    N₀ →ₗ[R] (localizedDifferential S f₁ f₂ d₁).ker :=
  ((IsLocalizedModule.map S f₀ f₁) d₀).codRestrict
    (localizedDifferential S f₁ f₂ d₁).ker (fun x => by
      have h := LinearMap.congr_fun (localized_comp_zero S f₀ f₁ f₂ d₀ d₁ hd) x
      simpa only [localizedDifferential, LinearMap.comp_apply, LinearMap.zero_apply,
        LinearMap.mem_ker] using h)

end IsLocalizedModule
