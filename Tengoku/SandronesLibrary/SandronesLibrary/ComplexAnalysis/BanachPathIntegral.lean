/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.PathIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Banach-valued path integrals

Mathlib's `curveIntegral` is already generic in the codomain: for a one-form
`ω : ℂ → ℂ →L[ℂ] F` and a path `γ` it produces an element of `F`.  The complex subject,
however, only exposes the scalar case through `scalarOneForm` / `pathIntegral`.  This file
packages the Banach-valued case as a faithful common carrier so that the later cycle and
winding layers can integrate `F`-valued integrands along paths and specialise to `F = ℂ`
without duplicating the whole interface.

The one-form attached to a Banach-valued integrand `f : ℂ → F` is
`banachOneForm f z = v ↦ v • f z`, the obvious generalisation of `scalarOneForm`.  With
`F = ℂ` it is definitionally the scalar one-form, so
`banachPathIntegral_complex_eq_pathIntegral` is a bridge by `rfl`, and the existing scalar
`pathIntegral` API is left untouched (no M2 migration in this batch).

Current entries:

* `complex-analysis.integral.banach-path-foundation`: the Banach one-form, integrability
  predicate, path integral, its ℂ bridge, and linearity / reversal / concatenation / cast
  lemmas.
-/

open MeasureTheory
open scoped Interval

noncomputable section

namespace SandronesLibrary.ComplexAnalysis

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The ℂ-linear one-form `v ↦ v • f z` for a Banach-valued integrand `f`.  For `F = ℂ` this is
definitionally the scalar one-form `scalarOneForm f`.

> **Entry**: complex-analysis.integral.banach-path-foundation-/
def banachOneForm (f : ℂ → F) : ℂ → ℂ →L[ℂ] F :=
  fun z => ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (f z)

/-- Evaluation of the Banach-valued one-form.

> **Entry**: complex-analysis.integral.banach-path-foundation
@isnad1 id=eq.0h4v.s7.3820eb54f2b2 from=translated src=- shape=c647cd5e vocab=6e521efc
-/
@[simp]
theorem banachOneForm_apply (f : ℂ → F) (z v : ℂ) : banachOneForm f z v = v • f z := by
  simp [banachOneForm]

/-- Integrability of a Banach-valued one-form along a path.

> **Entry**: complex-analysis.integral.banach-path-foundation-/
def BanachPathIntegrable (f : ℂ → F) {a b : ℂ} (γ : Path a b) : Prop :=
  CurveIntegrable (banachOneForm f) γ

/-- The Banach-valued path integral `∫_γ f(z) dz`, implemented by Mathlib's generic curve
integral.

> **Entry**: complex-analysis.integral.banach-path-foundation-/
def banachPathIntegral (f : ℂ → F) {a b : ℂ} (γ : Path a b) : F :=
  ∫ᶜ z in γ, banachOneForm f z

/-- Specialising the Banach-valued path integral to `F = ℂ` recovers the existing scalar
`pathIntegral`; the two one-forms are definitionally identical.

> **Entry**: complex-analysis.integral.banach-path-foundation
@isnad1 id=eq.0h4v.s5.5c9fad27d7b1 from=translated src=- shape=e8771dce vocab=72d69544
-/
@[simp]
theorem banachPathIntegral_complex_eq_pathIntegral (f : ℂ → ℂ) {a b : ℂ} (γ : Path a b) :
    banachPathIntegral (F := ℂ) f γ = pathIntegral f γ := by
  rfl

/-- The integral of the zero Banach-valued integrand vanishes.

> **Entry**: complex-analysis.integral.banach-path-foundation
@isnad1 id=eq.0h4v.s6.5fa32b6466a2 from=translated src=- shape=b391cb0a vocab=e0cc31ef
-/
theorem banachPathIntegral_zero {a b : ℂ} (γ : Path a b) :
    banachPathIntegral (fun _ : ℂ => (0 : F)) γ = 0 := by
  have h : banachOneForm (fun _ : ℂ => (0 : F)) = 0 := by
    funext z
    ext
    simp [banachOneForm]
  show curveIntegral (banachOneForm (fun _ : ℂ => (0 : F))) γ = 0
  rw [h]
  exact curveIntegral_zero

/-- The Banach-valued path integral is additive in the integrand.

> **Entry**: complex-analysis.integral.banach-path-foundation
@isnad1 id=eq.2h6v.s7.8d6917e7a6ed from=translated src=- shape=6b4b8235 vocab=74f1be29
-/
theorem banachPathIntegral_add {a b : ℂ} {f g : ℂ → F} {γ : Path a b}
    (hf : BanachPathIntegrable f γ) (hg : BanachPathIntegrable g γ) :
    banachPathIntegral (fun z => f z + g z) γ =
      banachPathIntegral f γ + banachPathIntegral g γ := by
  have h : banachOneForm (fun z => f z + g z) = banachOneForm f + banachOneForm g := by
    funext z
    ext
    simp [banachOneForm, smul_add]
  have hf' : CurveIntegrable (banachOneForm f) γ := hf
  have hg' : CurveIntegrable (banachOneForm g) γ := hg
  show curveIntegral (banachOneForm (fun z => f z + g z)) γ =
    curveIntegral (banachOneForm f) γ + curveIntegral (banachOneForm g) γ
  rw [h]
  exact curveIntegral_add hf' hg'

/-- The Banach-valued path integral is ℂ-homogeneous in the integrand.

> **Entry**: complex-analysis.integral.banach-path-foundation
@isnad1 id=eq.0h6v.s7.b801e82d6d0a from=translated src=- shape=cb84d147 vocab=114ef2d8
-/
theorem banachPathIntegral_smul {a b : ℂ} (c : ℂ) (f : ℂ → F) (γ : Path a b) :
    banachPathIntegral (fun z => c • f z) γ = c • banachPathIntegral f γ := by
  have h : banachOneForm (fun z => c • f z) = c • banachOneForm f := by
    funext z
    ext
    simp [banachOneForm, smul_comm]
  show curveIntegral (banachOneForm (fun z => c • f z)) γ =
    c • curveIntegral (banachOneForm f) γ
  rw [h]
  exact curveIntegral_smul (𝕝 := ℂ)

/-- Negating the Banach-valued integrand negates the integral.

> **Entry**: complex-analysis.integral.banach-path-foundation
@isnad1 id=eq.0h5v.s6.c47eb659a99d from=translated src=- shape=4fe9737c vocab=3230354d
-/
theorem banachPathIntegral_neg {a b : ℂ} (f : ℂ → F) (γ : Path a b) :
    banachPathIntegral (fun z => -f z) γ = -banachPathIntegral f γ := by
  have h : banachOneForm (fun z => -f z) = -banachOneForm f := by
    funext z
    ext
    simp [banachOneForm]
  show curveIntegral (banachOneForm (fun z => -f z)) γ = -curveIntegral (banachOneForm f) γ
  rw [h]
  exact curveIntegral_neg

/-- The integral along a constant path vanishes.

> **Entry**: complex-analysis.integral.banach-path-foundation
@isnad1 id=eq.0h3v.s5.168ea2ca804d from=translated src=- shape=57afdf08 vocab=fd33d218
-/
theorem banachPathIntegral_refl (f : ℂ → F) (a : ℂ) :
    banachPathIntegral f (Path.refl a) = 0 := by
  show curveIntegral (banachOneForm f) (Path.refl a) = 0
  exact curveIntegral_refl (banachOneForm f) a

/-- Reversing a path negates the Banach-valued path integral.

> **Entry**: complex-analysis.integral.banach-path-foundation
@isnad1 id=eq.0h5v.s6.4a2407ab0dcf from=translated src=- shape=21d69c8e vocab=9218badc
-/
theorem banachPathIntegral_symm {a b : ℂ} (f : ℂ → F) (γ : Path a b) :
    banachPathIntegral f γ.symm = -banachPathIntegral f γ := by
  show curveIntegral (banachOneForm f) γ.symm = -curveIntegral (banachOneForm f) γ
  exact curveIntegral_symm (banachOneForm f) γ

/-- Reversal preserves Banach-valued path integrability.

> **Entry**: complex-analysis.integral.banach-path-foundation
@isnad1 id=banachpa.1h5v.s6.a41867417105 from=translated src=- shape=c2ba999b vocab=3db62e62
-/
protected theorem BanachPathIntegrable.symm {a b : ℂ} {f : ℂ → F} {γ : Path a b}
    (h : BanachPathIntegrable f γ) : BanachPathIntegrable f γ.symm := by
  have h' : CurveIntegrable (banachOneForm f) γ := h
  exact CurveIntegrable.symm h'

/-- Two integrable Banach-valued paths with a common endpoint have an integrable
concatenation.

> **Entry**: complex-analysis.integral.banach-path-foundation
@isnad1 id=banachpa.2h7v.s6.733c2b4c54ff from=translated src=- shape=1b609653 vocab=253be37a
-/
protected theorem BanachPathIntegrable.trans {a b c : ℂ} {f : ℂ → F}
    {γ : Path a b} {δ : Path b c} (hγ : BanachPathIntegrable f γ) (hδ : BanachPathIntegrable f δ) :
    BanachPathIntegrable f (γ.trans δ) := by
  have hγ' : CurveIntegrable (banachOneForm f) γ := hγ
  have hδ' : CurveIntegrable (banachOneForm f) δ := hδ
  exact CurveIntegrable.trans hγ' hδ'

/-- The Banach-valued integral along a concatenation is the sum of the two integrals.

> **Entry**: complex-analysis.integral.banach-path-foundation
@isnad1 id=eq.2h7v.s7.d743b2dd203a from=translated src=- shape=aed55b60 vocab=3ee2ba66
-/
theorem banachPathIntegral_trans {a b c : ℂ} (f : ℂ → F) (γ : Path a b) (δ : Path b c)
    (hγ : BanachPathIntegrable f γ) (hδ : BanachPathIntegrable f δ) :
    banachPathIntegral f (γ.trans δ) = banachPathIntegral f γ + banachPathIntegral f δ := by
  have hγ' : CurveIntegrable (banachOneForm f) γ := hγ
  have hδ' : CurveIntegrable (banachOneForm f) δ := hδ
  show curveIntegral (banachOneForm f) (γ.trans δ) =
    curveIntegral (banachOneForm f) γ + curveIntegral (banachOneForm f) δ
  exact curveIntegral_trans hγ' hδ'

/-- The Banach-valued integral is invariant under casting the endpoints of a path.

> **Entry**: complex-analysis.integral.banach-path-foundation
@isnad1 id=eq.2h7v.s6.5a4d9602cb68 from=translated src=- shape=a9132c56 vocab=09fb1fad
-/
theorem banachPathIntegral_cast {a b c d : ℂ} (f : ℂ → F) (γ : Path a b) (hc : c = a)
    (hd : d = b) :
    banachPathIntegral f (γ.cast hc hd) = banachPathIntegral f γ := by
  show curveIntegral (banachOneForm f) (γ.cast hc hd) = curveIntegral (banachOneForm f) γ
  exact curveIntegral_cast (banachOneForm f) γ hc hd

end SandronesLibrary.ComplexAnalysis
