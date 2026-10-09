/-
Copyright (c) 2023 Ziyu Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ziyu Wang, Chenyi Li, Sébastien Gouëzel, Penghao Yu, Zhipeng Cao
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.InnerProductSpace.Dual
public import Tengoku.Seed.Analysis.Calculus.FDeriv.Basic
public import Tengoku.Seed.Analysis.Calculus.Deriv.Basic

/-!
# Gradient

## Main Definitions

Let `f` be a function from a Hilbert Space `F` to `𝕜` (`𝕜` is `ℝ` or `ℂ`), `x` be a point in `F`
and `f'` be a vector in F. Then

  `HasGradientWithinAt f f' s x`

says that `f` has a gradient `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `HasGradientAt f f' x := HasGradientWithinAt f f' x univ`

## Main results

This file develops the following aspects of the theory of gradients:
* definitions of gradients, both within a set and on the whole space.
* translating between `HasGradientAtFilter` and `HasFDerivAtFilter`,
  `HasGradientWithinAt` and `HasFDerivWithinAt`, `HasGradientAt` and `HasFDerivAt`,
  `gradient` and `fderiv`.
* uniqueness of gradients.
* translating between `HasGradientAtFilter` and `HasDerivAtFilter`,
  `HasGradientAt` and `HasDerivAt`, `gradient` and `deriv` when `F = 𝕜`.
* the theorems about the inner product of the gradient.
* the congruence of the gradient.
* the gradient of constant functions.
* the continuity of a function admitting a gradient.
-/

@[expose] public section

@[expose] public section

open ComplexConjugate Topology InnerProductSpace Function Set

noncomputable section

variable {𝕜 F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable {f : F → 𝕜} {f' x y : F}

/-- A function `f` has the gradient `f'` as derivative along the filter `L` if
  `f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` when `x'` converges along the filter `L`. -/
def HasGradientAtFilter (f : F → 𝕜) (f' x : F) (L : Filter F) :=
  HasFDerivAtFilter f (toDual 𝕜 F f') (L ×ˢ pure x)

/-- `f` has the gradient `f'` at the point `x` within the subset `s` if
  `f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x` inside `s`. -/
def HasGradientWithinAt (f : F → 𝕜) (f' : F) (s : Set F) (x : F) :=
  HasGradientAtFilter f f' x (𝓝[s] x)

/-- `f` has the gradient `f'` at the point `x` if
  `f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x`. -/
def HasGradientAt (f : F → 𝕜) (f' x : F) :=
  HasGradientAtFilter f f' x (𝓝 x)

/-- Gradient of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', HasGradientWithinAt f f' s x`), then
`f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x` inside `s`. -/
def gradientWithin (f : F → 𝕜) (s : Set F) (x : F) : F :=
  (toDual 𝕜 F).symm (fderivWithin 𝕜 f s x)

/-- Gradient of `f` at the point `x`, if it exists.  Zero otherwise.
Denoted as `∇` within the Gradient namespace.

If the derivative exists (i.e., `∃ f', HasGradientAt f f' x`), then
`f x' = f x + ⟨f', x' - x⟩ + o (x' - x)` where `x'` converges to `x`. -/
def gradient (f : F → 𝕜) (x : F) : F :=
  (toDual 𝕜 F).symm (fderiv 𝕜 f x)

@[inherit_doc]
scoped[Gradient] notation "∇" => gradient

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open scoped Gradient

variable {s : Set F} {L : Filter F}

/--
@isnad1 id=iff.0h6v.s10.78e25c58f037 from=seed src=0 shape=3113bf91 vocab=53737a1a
-/
theorem hasGradientWithinAt_iff_hasFDerivWithinAt {s : Set F} :
    HasGradientWithinAt f f' s x ↔ HasFDerivWithinAt f (toDual 𝕜 F f') s x :=
  Iff.rfl

/--
@isnad1 id=iff.0h6v.s10.47579c91e777 from=seed src=0 shape=1e6f9c19 vocab=45b3b528
-/
theorem hasFDerivWithinAt_iff_hasGradientWithinAt {frechet : StrongDual 𝕜 F} {s : Set F} :
    HasFDerivWithinAt f frechet s x ↔ HasGradientWithinAt f ((toDual 𝕜 F).symm frechet) s x := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt, (toDual 𝕜 F).apply_symm_apply frechet]

/--
@isnad1 id=iff.0h5v.s10.45901c81e627 from=seed src=0 shape=3c7a93bf vocab=b2762581
-/
theorem hasGradientAt_iff_hasFDerivAt :
    HasGradientAt f f' x ↔ HasFDerivAt f (toDual 𝕜 F f') x :=
  Iff.rfl

/--
@isnad1 id=iff.0h5v.s10.c574f12621c9 from=seed src=0 shape=97604ed0 vocab=b55cb44b
-/
theorem hasFDerivAt_iff_hasGradientAt {frechet : StrongDual 𝕜 F} :
    HasFDerivAt f frechet x ↔ HasGradientAt f ((toDual 𝕜 F).symm frechet) x := by
  rw [hasGradientAt_iff_hasFDerivAt, (toDual 𝕜 F).apply_symm_apply frechet]

/--
@isnad1 id=hasfderi.1h6v.s10.0c64aa79ce10 from=seed src=0 shape=239de69a vocab=53737a1a
-/
alias ⟨HasGradientWithinAt.hasFDerivWithinAt, _⟩ := hasGradientWithinAt_iff_hasFDerivWithinAt

/--
@isnad1 id=hasgradi.1h6v.s10.02ea2336712b from=seed src=0 shape=16f344e6 vocab=45b3b528
-/
alias ⟨HasFDerivWithinAt.hasGradientWithinAt, _⟩ := hasFDerivWithinAt_iff_hasGradientWithinAt

/--
@isnad1 id=hasfderi.1h5v.s10.61e2c9bf6dd5 from=seed src=0 shape=a8c3a4ad vocab=b2762581
-/
alias ⟨HasGradientAt.hasFDerivAt, _⟩ := hasGradientAt_iff_hasFDerivAt

/--
@isnad1 id=hasgradi.1h5v.s10.9cbcc6323d57 from=seed src=0 shape=9ef209ff vocab=b55cb44b
-/
alias ⟨HasFDerivAt.hasGradientAt, _⟩ := hasFDerivAt_iff_hasGradientAt

/--
@isnad1 id=eq.1h4v.s7.15472ffc1f0a from=seed src=0 shape=516406fb vocab=fd7a422d
-/
theorem gradient_eq_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : ∇ f x = 0 := by
  rw [gradient, fderiv_zero_of_not_differentiableAt h, map_zero]

/--
@isnad1 id=eq.0h5v.s10.09b7d4695f30 from=seed src=0 shape=77eb38ea vocab=10c0eaec
-/
@[simp]
lemma toDual_gradientWithin :
    (toDual 𝕜 F) (gradientWithin f s x) = fderivWithin 𝕜 f s x := by
  rw [gradientWithin, (toDual 𝕜 F).apply_symm_apply]

/--
@isnad1 id=eq.0h4v.s10.c5607cd850b1 from=seed src=0 shape=29ba6aac vocab=a30e5420
-/
@[simp]
lemma toDual_gradient : (toDual 𝕜 F) (∇ f x) = fderiv 𝕜 f x := by
  rw [gradient, (toDual 𝕜 F).apply_symm_apply]

/--
@isnad1 id=eq.0h4v.s10.321ef3c5aa12 from=seed src=0 shape=80bfbdb9 vocab=2502fc2c
-/
@[simp]
lemma toDual_comp_gradientWithin :
    (toDual 𝕜 F) ∘ gradientWithin f s = fderivWithin 𝕜 f s :=
  funext fun _ => toDual_gradientWithin

/--
@isnad1 id=eq.0h3v.s10.7eaaf19e24bd from=seed src=0 shape=ab0dee2d vocab=b8232113
-/
@[simp]
lemma toDual_comp_gradient : (toDual 𝕜 F) ∘ ∇ f = fderiv 𝕜 f :=
  funext fun _ => toDual_gradient

/--
@isnad1 id=eq.2h6v.s6.ddb53a01883e from=seed src=0 shape=bd2a2ddd vocab=19a77b7b
-/
theorem HasGradientAt.unique {gradf gradg : F}
    (hf : HasGradientAt f gradf x) (hg : HasGradientAt f gradg x) :
    gradf = gradg :=
  (toDual 𝕜 F).injective (hf.hasFDerivAt.unique hg.hasFDerivAt)

/--
@isnad1 id=hasgradi.1h4v.s7.e8ade914a0d6 from=seed src=0 shape=998d532d vocab=ca550975
-/
theorem DifferentiableAt.hasGradientAt (h : DifferentiableAt 𝕜 f x) :
    HasGradientAt f (∇ f x) x := by
  simpa [hasGradientAt_iff_hasFDerivAt] using h.hasFDerivAt

/--
@isnad1 id=differen.1h5v.s7.a3d453abf6f1 from=seed src=0 shape=2efcbec8 vocab=54a014d8
-/
theorem HasGradientAt.differentiableAt (h : HasGradientAt f f' x) :
    DifferentiableAt 𝕜 f x :=
  h.hasFDerivAt.differentiableAt

/--
@isnad1 id=hasgradi.1h5v.s7.4012f3567279 from=seed src=0 shape=6cdf13fa vocab=396f86d8
-/
theorem DifferentiableWithinAt.hasGradientWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasGradientWithinAt f (gradientWithin f s x) s x := by
  simpa [hasGradientWithinAt_iff_hasFDerivWithinAt] using h.hasFDerivWithinAt

/--
@isnad1 id=differen.1h6v.s7.43c7974ebbaa from=seed src=0 shape=ec129ffa vocab=6e5245a6
-/
theorem HasGradientWithinAt.differentiableWithinAt (h : HasGradientWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.hasFDerivWithinAt.differentiableWithinAt

/--
@isnad1 id=iff.0h5v.s5.bd7afc9ba07a from=seed src=0 shape=9f9bbee5 vocab=48b6807c
-/
@[simp]
theorem hasGradientWithinAt_univ : HasGradientWithinAt f f' univ x ↔ HasGradientAt f f' x := by
  rw [hasGradientWithinAt_iff_hasFDerivWithinAt, hasGradientAt_iff_hasFDerivAt]
  exact hasFDerivWithinAt_univ

/--
@isnad1 id=eq.0h3v.s5.5dfd3eabfd6f from=seed src=0 shape=a8efdc40 vocab=dd495ca2
-/
@[simp]
lemma gradientWithin_univ : gradientWithin f univ = gradient f := by
  ext; simp [gradientWithin, gradient]

/--
@isnad1 id=hasgradi.2h5v.s7.8d9a6e4012e0 from=seed src=0 shape=acff8533 vocab=d1febe3d
-/
theorem DifferentiableOn.hasGradientAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasGradientAt f (∇ f x) x :=
  (h.hasFDerivAt hs).hasGradientAt

/--
@isnad1 id=eq.1h5v.s5.8adddb4e502d from=seed src=0 shape=a50d999e vocab=e0a524a9
-/
theorem HasGradientAt.gradient (h : HasGradientAt f f' x) : ∇ f x = f' :=
  h.differentiableAt.hasGradientAt.unique h

/--
@isnad1 id=eq.1h4v.s6.8fb0f53d7e19 from=seed src=0 shape=ba3c3f50 vocab=e0a524a9
-/
theorem gradient_eq {f' : F → F} (h : ∀ x, HasGradientAt f (f' x) x) : ∇ f = f' :=
  funext fun x => (h x).gradient

section OneDimension

variable {g : 𝕜 → 𝕜} {g' u : 𝕜} {L' : Filter 𝕜}

/--
@isnad1 id=hasderiv.1h5v.s7.c981a10504b6 from=seed src=0 shape=188d0e52 vocab=2316222d
-/
theorem HasGradientAtFilter.hasDerivAtFilter (h : HasGradientAtFilter g g' u L') :
    HasDerivAtFilter g (conj g') (L' ×ˢ pure u) :=
  h

/--
@isnad1 id=hasgradi.1h5v.s7.912f856d012a from=seed src=0 shape=21895dc3 vocab=2316222d
-/
theorem HasDerivAtFilter.hasGradientAtFilter (h : HasDerivAtFilter g g' (L' ×ˢ pure u)) :
    HasGradientAtFilter g (conj g') u L' := by
  have : ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) g' = (toDual 𝕜 𝕜) (conj g') := by
    ext; simp
  rwa [HasGradientAtFilter, ← this]

/--
@isnad1 id=hasderiv.1h4v.s7.6132041a20a6 from=seed src=0 shape=8278a19b vocab=8115508a
-/
theorem HasGradientAt.hasDerivAt (h : HasGradientAt g g' u) : HasDerivAt g (conj g') u := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt] at h
  simpa using h

/--
@isnad1 id=hasgradi.1h4v.s7.dc4309c14e71 from=seed src=0 shape=8278a19b vocab=8115508a
-/
theorem HasDerivAt.hasGradientAt (h : HasDerivAt g g' u) : HasGradientAt g (conj g') u := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_hasDerivAt]
  simpa

/--
@isnad1 id=eq.0h3v.s7.e2bf514abf1f from=seed src=0 shape=724b640c vocab=b3f74385
-/
theorem gradient_eq_deriv : ∇ g u = conj (deriv g u) := by
  by_cases h : DifferentiableAt 𝕜 g u
  · rw [h.hasGradientAt.hasDerivAt.deriv, RCLike.conj_conj]
  · rw [gradient_eq_zero_of_not_differentiableAt h, deriv_zero_of_not_differentiableAt h, map_zero]

end OneDimension

section OneDimensionReal

variable {g : ℝ → ℝ} {g' u : ℝ} {L' : Filter ℝ}

/--
@isnad1 id=hasderiv.1h4v.s6.8b6c1ec0b23d from=seed src=0 shape=11f2ba35 vocab=0faed138
-/
theorem HasGradientAtFilter.hasDerivAtFilter' (h : HasGradientAtFilter g g' u L') :
    HasDerivAtFilter g g' (L' ×ˢ pure u) := h.hasDerivAtFilter

/--
@isnad1 id=hasgradi.1h4v.s6.eaffa14d2a04 from=seed src=0 shape=6e76a757 vocab=0faed138
-/
theorem HasDerivAtFilter.hasGradientAtFilter' (h : HasDerivAtFilter g g' (L' ×ˢ pure u)) :
    HasGradientAtFilter g g' u L' := h.hasGradientAtFilter

/--
@isnad1 id=hasderiv.1h3v.s5.ecedb57beb4f from=seed src=0 shape=243f9554 vocab=dd76ed76
-/
theorem HasGradientAt.hasDerivAt' (h : HasGradientAt g g' u) :
    HasDerivAt g g' u := h.hasDerivAt

/--
@isnad1 id=hasgradi.1h3v.s5.8c22db57a776 from=seed src=0 shape=243f9554 vocab=dd76ed76
-/
theorem HasDerivAt.hasGradientAt' (h : HasDerivAt g g' u) :
    HasGradientAt g g' u := h.hasGradientAt

/--
@isnad1 id=eq.0h2v.s5.75bc51161013 from=seed src=0 shape=aaf1064f vocab=426420ba
-/
theorem gradient_eq_deriv' : ∇ g u = deriv g u := gradient_eq_deriv

end OneDimensionReal

open Filter

section GradientProperties

/--
@isnad1 id=iff.0h6v.s7.a07334b2e6f1 from=seed src=0 shape=c9b92419 vocab=8dda6639
-/
theorem hasGradientAtFilter_iff_isLittleO :
    HasGradientAtFilter f f' x L ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[L] fun x' => x' - x :=
  hasFDerivAtFilter_iff_isLittleO.trans <| by simp [Function.comp_def]

/--
@isnad1 id=iff.0h6v.s7.76bc7d6c5641 from=seed src=0 shape=893ec41d vocab=f58a9668
-/
theorem hasGradientWithinAt_iff_isLittleO :
    HasGradientWithinAt f f' s x ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[𝓝[s] x] fun x' => x' - x :=
  hasGradientAtFilter_iff_isLittleO

/--
@isnad1 id=iff.0h6v.s7.07c469265762 from=seed src=0 shape=2d6e9deb vocab=aa0c0402
-/
theorem hasGradientWithinAt_iff_tendsto :
    HasGradientWithinAt f f' s x ↔
    Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - ⟪f', x' - x⟫‖) (𝓝[s] x) (𝓝 0) :=
  hasFDerivWithinAt_iff_tendsto

/--
@isnad1 id=iff.0h5v.s7.52121ae7a35e from=seed src=0 shape=f5c64668 vocab=b0718276
-/
theorem hasGradientAt_iff_isLittleO : HasGradientAt f f' x ↔
    (fun x' : F => f x' - f x - ⟪f', x' - x⟫) =o[𝓝 x] fun x' => x' - x :=
  hasGradientAtFilter_iff_isLittleO

/--
@isnad1 id=iff.0h5v.s7.6caa5336ecf6 from=seed src=0 shape=1436294e vocab=6e1f4e3e
-/
theorem hasGradientAt_iff_tendsto :
    HasGradientAt f f' x ↔
    Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - ⟪f', x' - x⟫‖) (𝓝 x) (𝓝 0) :=
  hasFDerivAt_iff_tendsto

/--
@isnad1 id=isbigo.1h6v.s6.0390753147eb from=seed src=0 shape=659a10ce vocab=b51a6023
-/
theorem HasGradientAtFilter.isBigO_sub (h : HasGradientAtFilter f f' x L) :
    (fun x' => f x' - f x) =O[L] fun x' => x' - x :=
  HasFDerivAtFilter.isBigO_sub h |>.comp_tendsto prod_pure.ge

/--
@isnad1 id=iff.1h8v.s6.74d51bcb585a from=seed src=0 shape=1bf03df9 vocab=aff7c556
-/
theorem hasGradientWithinAt_congr_set' {s t : Set F} (y : F) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set' y h

/--
@isnad1 id=iff.1h7v.s6.0bba6833da02 from=seed src=0 shape=58ada3ad vocab=751c9d88
-/
theorem hasGradientWithinAt_congr_set {s t : Set F} (h : s =ᶠ[𝓝 x] t) :
    HasGradientWithinAt f f' s x ↔ HasGradientWithinAt f f' t x :=
  hasFDerivWithinAt_congr_set h

/--
@isnad1 id=iff.0h5v.s7.9cccbb3e4489 from=seed src=0 shape=a6585e40 vocab=6c81128c
-/
theorem hasGradientAt_iff_isLittleO_nhds_zero : HasGradientAt f f' x ↔
    (fun h => f (x + h) - f x - ⟪f', h⟫) =o[𝓝 0] fun h => h :=
  hasFDerivAt_iff_isLittleO_nhds_zero

end GradientProperties

section Inner

/--
@isnad1 id=eq.2h7v.s8.0e28e139fb8c from=seed src=0 shape=51503ff7 vocab=d34afd98
-/
lemma HasGradientWithinAt.fderivWithin_apply
    (h : HasGradientWithinAt f f' s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 f s x y = ⟪f', y⟫ := by
  rw [h.hasFDerivWithinAt.fderivWithin hs, toDual_apply_apply]

/--
@isnad1 id=eq.1h6v.s8.90af6cc3ddb4 from=seed src=0 shape=c489ac2b vocab=2583e570
-/
lemma HasGradientAt.fderiv_apply (h : HasGradientAt f f' x) : fderiv 𝕜 f x y = ⟪f', y⟫ := by
  rw [h.hasFDerivAt.fderiv, toDual_apply_apply]

/--
@isnad1 id=eq.0h6v.s8.9eb0f105b7e1 from=seed src=0 shape=376ce728 vocab=1a85c8d1
-/
@[simp]
lemma inner_gradientWithin_left :
    ⟪gradientWithin f s x, y⟫ = fderivWithin 𝕜 f s x y := by
  rw [gradientWithin, ← toDual_apply_apply (𝕜 := 𝕜) (E := F),
      LinearIsometryEquiv.apply_symm_apply]

/--
@isnad1 id=eq.0h5v.s8.89ec34a23685 from=seed src=0 shape=b135becd vocab=40911442
-/
@[simp]
lemma inner_gradient_left : ⟪∇ f x, y⟫ = fderiv 𝕜 f x y := by
  simp [← gradientWithin_univ]

/--
@isnad1 id=eq.0h6v.s9.b6a34f047187 from=seed src=0 shape=1a84481c vocab=69266724
-/
@[simp]
lemma inner_gradientWithin_right :
    ⟪x, gradientWithin f s y⟫ = conj (fderivWithin 𝕜 f s y x) := by
  rw [← inner_conj_symm, inner_gradientWithin_left]

/--
@isnad1 id=eq.0h5v.s9.29e295d1aa4a from=seed src=0 shape=25d86d17 vocab=3e96a284
-/
@[simp]
lemma inner_gradient_right : ⟪x, ∇ f y⟫ = conj (fderiv 𝕜 f y x) := by
  rw [← inner_conj_symm, inner_gradient_left]

end Inner

section congr

/-! ### Congruence properties of the Gradient -/

variable {f₀ f₁ : F → 𝕜} {f₀' f₁' : F} {t : Set F}

/--
@isnad1 id=iff.3h8v.s6.e45cede11a4f from=seed src=0 shape=ea119b23 vocab=c32a6c95
-/
theorem Filter.EventuallyEq.hasGradientAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
    (h₁ : f₀' = f₁') : HasGradientAtFilter f₀ f₀' x L ↔ HasGradientAtFilter f₁ f₁' x L :=
  (h₀.prodMap <| by assumption).hasFDerivAtFilter_iff <| by simp [h₁]

/--
@isnad1 id=hasgradi.3h7v.s6.cabdb9ab863c from=seed src=0 shape=a0dd3c1c vocab=c32a6c95
-/
theorem HasGradientAtFilter.congr_of_eventuallyEq (h : HasGradientAtFilter f f' x L)
    (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) : HasGradientAtFilter f₁ f' x L := by
  rwa [hL.hasGradientAtFilter_iff hx rfl]

/--
@isnad1 id=hasgradi.4h8v.s6.35f802db574e from=seed src=0 shape=a09e6beb vocab=d9d7445e
-/
theorem HasGradientWithinAt.congr_mono (h : HasGradientWithinAt f f' s x) (ht : ∀ x ∈ t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasGradientWithinAt f₁ f' t x :=
  HasFDerivWithinAt.congr_mono h ht hx h₁

/--
@isnad1 id=hasgradi.3h7v.s6.6f307d5778ce from=seed src=0 shape=fab7e4da vocab=edbfddbc
-/
theorem HasGradientWithinAt.congr (h : HasGradientWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x :=
  h.congr_mono hs hx (by tauto)

/--
@isnad1 id=hasgradi.3h7v.s6.5ca8d48f2934 from=seed src=0 shape=b0dfc93a vocab=edbfddbc
-/
theorem HasGradientWithinAt.congr_of_mem (h : HasGradientWithinAt f f' s x)
    (hs : ∀ x ∈ s, f₁ x = f x) (hx : x ∈ s) : HasGradientWithinAt f₁ f' s x :=
  h.congr hs (hs _ hx)

/--
@isnad1 id=hasgradi.3h7v.s6.08217b18071c from=seed src=0 shape=816768cf vocab=738ddc1a
-/
theorem HasGradientWithinAt.congr_of_eventuallyEq (h : HasGradientWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasGradientWithinAt f₁ f' s x :=
  HasGradientAtFilter.congr_of_eventuallyEq h h₁ hx

/--
@isnad1 id=hasgradi.3h7v.s6.5ce291d8d231 from=seed src=0 shape=75b4e26c vocab=8e8e91e3
-/
theorem HasGradientWithinAt.congr_of_eventuallyEq_of_mem (h : HasGradientWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : HasGradientWithinAt f₁ f' s x :=
  h.congr_of_eventuallyEq h₁ (h₁.eq_of_nhdsWithin hx)

/--
@isnad1 id=hasgradi.2h6v.s6.82f34d13eabd from=seed src=0 shape=ab4419ad vocab=a13b9fe2
-/
theorem HasGradientAt.congr_of_eventuallyEq (h : HasGradientAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasGradientAt f₁ f' x :=
  HasGradientAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ :)

/--
@isnad1 id=eq.1h5v.s6.60711145b36d from=seed src=0 shape=2ac3ff96 vocab=e9fa957e
-/
theorem Filter.EventuallyEq.gradient_eq (hL : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ x = ∇ f x := by
  unfold gradient
  rwa [Filter.EventuallyEq.fderiv_eq]

/--
@isnad1 id=eventual.1h5v.s6.6f04719713d9 from=seed src=0 shape=123cf4b3 vocab=e9fa957e
-/
protected theorem Filter.EventuallyEq.gradient (h : f₁ =ᶠ[𝓝 x] f) : ∇ f₁ =ᶠ[𝓝 x] ∇ f :=
  h.eventuallyEq_nhds.mono fun _ h => h.gradient_eq

end congr

/-! ### The Gradient of constant functions -/

section Const

variable (c : 𝕜) (s x L)

/--
@isnad1 id=hasgradi.0h5v.s6.d485e424c545 from=seed src=0 shape=3c7de653 vocab=da96f06d
-/
theorem hasGradientAtFilter_const : HasGradientAtFilter (fun _ => c) 0 x L := by
  rw [HasGradientAtFilter, map_zero]; exact hasFDerivAtFilter_const c _

/--
@isnad1 id=hasgradi.0h5v.s6.df6e3dc6c360 from=seed src=0 shape=459d360a vocab=dcca4b52
-/
theorem hasGradientWithinAt_const : HasGradientWithinAt (fun _ => c) 0 s x :=
  hasGradientAtFilter_const _ _ _

/--
@isnad1 id=hasgradi.0h4v.s5.2e5b681c37c3 from=seed src=0 shape=d103277a vocab=19a77b7b
-/
theorem hasGradientAt_const : HasGradientAt (fun _ => c) 0 x :=
  hasGradientAtFilter_const _ _ _

/--
@isnad1 id=eq.0h4v.s5.a1f672cf45b2 from=seed src=0 shape=dac52267 vocab=b30aac4e
-/
theorem gradient_fun_const : ∇ (fun _ => c) x = 0 := by simp [gradient]

/--
@isnad1 id=eq.0h4v.s6.4d40fc63bcd0 from=seed src=0 shape=82257a51 vocab=ca87a05a
-/
theorem gradient_const : ∇ (const F c) x = 0 := gradient_fun_const x c

/--
@isnad1 id=eq.0h3v.s6.4dd677d0ae42 from=seed src=0 shape=66e8c629 vocab=b30aac4e
-/
@[simp]
theorem gradient_fun_const' : (∇ fun _ : F => c) = fun _ => 0 :=
  funext fun x => gradient_const x c

/--
@isnad1 id=eq.0h3v.s6.578841104c54 from=seed src=0 shape=36731c3c vocab=ca87a05a
-/
@[simp]
theorem gradient_const' : ∇ (const F c) = 0 := gradient_fun_const' c

end Const

section Continuous

/-! ### Continuity of a function admitting a gradient -/

/--
@isnad1 id=tendsto.2h6v.s6.459d91bd10af from=seed src=0 shape=6549226f vocab=0f5deb79
-/
nonrec theorem HasGradientAtFilter.tendsto_nhds (hL : L ≤ 𝓝 x) (h : HasGradientAtFilter f f' x L) :
    Tendsto f L (𝓝 (f x)) :=
  h.tendsto_nhds hL

/--
@isnad1 id=continuo.1h6v.s6.38808ae7a05e from=seed src=0 shape=8c798eee vocab=02da8cfb
-/
theorem HasGradientWithinAt.continuousWithinAt (h : HasGradientWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasGradientAtFilter.tendsto_nhds inf_le_left h

/--
@isnad1 id=continuo.1h5v.s6.f0ca9c6876b8 from=seed src=0 shape=6616f01e vocab=41cd2ad2
-/
theorem HasGradientAt.continuousAt (h : HasGradientAt f f' x) : ContinuousAt f x :=
  HasGradientAtFilter.tendsto_nhds le_rfl h

/--
@isnad1 id=continuo.1h5v.s6.4991a426c42b from=seed src=0 shape=e3ecf045 vocab=c7042516
-/
protected theorem HasGradientAt.continuousOn {f' : F → F} (h : ∀ x ∈ s, HasGradientAt f (f' x) x) :
    ContinuousOn f s :=
  fun x hx => (h x hx).continuousAt.continuousWithinAt

end Continuous
