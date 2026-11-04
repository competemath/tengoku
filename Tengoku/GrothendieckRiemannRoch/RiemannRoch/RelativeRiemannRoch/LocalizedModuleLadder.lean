/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.Algebra.Module.LocalizedModule.Basic
import Tengoku.Seed.Algebra.Exact.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Localization of a ladder of exact rows

Quasicoherence of a direct image over an affine base is, by Mathlib's tilde comparison
(`Scheme.Modules.isQuasicoherent_iff_isIso_fromTildeΓ` together with
`isIso_fromTildeΓ_iff_isLocalizing`), exactly the statement that the restriction map
`Γ(X, F) ⟶ Γ(f⁻¹ D(r), F)` is a localization at the powers of `r` for every `r` in the base ring.
For a source that is covered by finitely many affine opens with affine pairwise intersections, the
sheaf condition presents that restriction map as the left column of a ladder whose middle and right
columns are finite products of *affine* restriction maps, which are localizations.

Mathlib already supplies the finite-product half (`IsLocalizedModule.pi`: localization of modules
commutes with finite products).  This file supplies the missing ladder half:

* `IsLocalizedModule.of_exact_ladder`: the **localization four lemma** — in a ladder of two exact
  rows `0 → A → B → C` and `0 → A' → B' → C'`, if the middle and the right vertical maps are
  localizations at `S`, then so is the left vertical map.

It is stated for an arbitrary localizing submonoid `S`, and is proved by verifying the three fields
of `IsLocalizedModule` directly, so it needs neither exactness of localization nor the construction
of a comparison isomorphism.  Invertibility of the action of `S` on `A'` uses exactness of the lower
row, the surjectivity field uses exactness of the upper row together with the kernel description of
the right localization, and the kernel field uses only injectivity of the upper row's first map.

The two auxiliary statements `IsLocalizedModule.injective_smul` and
`IsLocalizedModule.surjective_smul` unpack `IsLocalizedModule.map_units` into the two halves that
the four lemma's diagram chase actually uses.
-/

set_option autoImplicit false

universe u

namespace IsLocalizedModule

variable {R : Type u} [CommRing R] (S : Submonoid R)

section SMulBijective

/-- Multiplication by an element of the localizing submonoid is injective on a localized module.
@isnad1 id=eq.1h8v.s8.565db9929dd8 from=translated src=- shape=8dd42259 vocab=e88163b1
-/
theorem injective_smul {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (s : S) {x y : N}
    (h : (s : R) • x = (s : R) • y) : x = y := by
  have h' := IsLocalizedModule.map_units f s
  rw [Module.End.isUnit_iff] at h'
  exact h'.1 (a₁ := x) (a₂ := y) h

/-- Multiplication by an element of the localizing submonoid is surjective on a localized
module.
@isnad1 id=ex.0h7v.s8.6a7d0c2fdf06 from=translated src=- shape=f9f9fdf6 vocab=e88163b1
-/
theorem surjective_smul {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (s : S) (y : N) :
    ∃ x : N, (s : R) • x = y := by
  have h' := IsLocalizedModule.map_units f s
  rw [Module.End.isUnit_iff] at h'
  exact h'.2 y

end SMulBijective

section Ladder

variable {A B C A' B' C' : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B'] [AddCommGroup C'] [Module R C']

/-- **Localization four lemma.** In a ladder of two exact rows `0 → A → B → C` and
`0 → A' → B' → C'`, if the middle and the right vertical maps are localizations at `S`, then so is
the left vertical map.

All three fields of `IsLocalizedModule` are verified directly.  Invertibility of the action of `S`
on `A'` uses exactness of the lower row, the surjectivity field uses exactness of the upper row
together with the kernel description of the right localization, and the kernel field uses only
injectivity of the upper row's first map.
@isnad1 id=islocali.6h15v.s10.ed07bf758ab2 from=translated src=- shape=5070b4ee vocab=49ddd48e
-/
theorem of_exact_ladder
    (i : A →ₗ[R] B) (d : B →ₗ[R] C) (i' : A' →ₗ[R] B') (d' : B' →ₗ[R] C')
    (a : A →ₗ[R] A') (b : B →ₗ[R] B') (c : C →ₗ[R] C')
    (hi : Function.Injective i) (hex : Function.Exact i d)
    (hi' : Function.Injective i') (hex' : Function.Exact i' d')
    (hab : ∀ x, i' (a x) = b (i x)) (hbc : ∀ x, d' (b x) = c (d x))
    [IsLocalizedModule S b] [IsLocalizedModule S c] :
    IsLocalizedModule S a := by
  constructor
  · intro s
    rw [Module.End.isUnit_iff]
    show Function.Bijective (fun x : A' => (s : R) • x)
    constructor
    · intro x y hxy
      refine hi' (injective_smul S b s ?_)
      show (s : R) • i' x = (s : R) • i' y
      rw [← map_smul, ← map_smul]
      exact congrArg i' hxy
    · intro y
      obtain ⟨z, hz⟩ := surjective_smul S b s (i' y)
      have hdz : d' z = 0 := by
        refine injective_smul S c s ?_
        have hzero : d' ((s : R) • z) = 0 := by
          rw [hz]; exact hex'.apply_apply_eq_zero y
        rw [map_smul] at hzero
        rw [hzero, smul_zero]
      obtain ⟨x, hx⟩ := (hex' z).1 hdz
      exact ⟨x, hi' (by rw [map_smul, hx, hz])⟩
  · intro y
    obtain ⟨⟨z, s⟩, hz⟩ := IsLocalizedModule.surj S b (i' y)
    rw [Submonoid.smul_def] at hz
    have hcdz : c (d z) = c 0 := by
      rw [← hbc z, ← hz, map_smul, hex'.apply_apply_eq_zero y, smul_zero, map_zero]
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := c) hcdz
    rw [Submonoid.smul_def, Submonoid.smul_def, smul_zero] at ht
    have hdtz : d ((t : R) • z) = 0 := by rw [map_smul]; exact ht
    obtain ⟨x, hx⟩ := (hex ((t : R) • z)).1 hdtz
    refine ⟨⟨x, t * s⟩, hi' ?_⟩
    rw [Submonoid.smul_def, map_smul, hab x, hx, map_smul, ← hz, Submonoid.coe_mul, mul_smul]
  · intro x₁ x₂ h
    have hbi : b (i x₁) = b (i x₂) := by rw [← hab, ← hab, h]
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := b) hbi
    refine ⟨t, hi ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def] at ht
    rw [Submonoid.smul_def, Submonoid.smul_def, map_smul, map_smul, ht]

end Ladder

end IsLocalizedModule
