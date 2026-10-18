/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FunctionField.GenericPoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The composition law for the translation-by-a-point pullback

Let `W` be an elliptic curve over a field `F`, with function field `F(W)`. For a fixed affine point
`T = (x₂, y₂)` on `W` (`h₂ : W.Equation x₂ y₂`), the translation-by-`T` pullback
`translateEndo h₂ : F(W) →+* F(W)` (`FunctionField/TranslationEndomorphism.lean`) reads, on the
generic point `𝒫 = (genX, genY)`, as `+ 𝒯` in the group `(W ⁄ F(W)).Point`
(`genericPoint_add_translatePoint`, `FunctionField/GenericPoint.lean`).

This file proves the **contravariant functoriality** of that pullback with respect to the group law:
for affine points `P`, `Q`, `R` with `P ⊕ Q = R` (encoded as the identity
`translatePoint hP + translatePoint hQ = translatePoint hR` of the corresponding constant points
over `F(W)`),

```
translateEndo hP ∘ translateEndo hQ = translateEndo hR      (as F(W) →+* F(W)).
```

This is the keystone that bilinearity of the divisor-theoretic Weil pairing consumes (#419): with
`τ_{T} := translateEndo h_T`, bilinearity in `T` is
`e_n(S, T₁ ⊕ T₂) = τ_{T₁⊕T₂}(g_S)/g_S = τ_{T₁}(τ_{T₂}(g_S))/g_S = …`, which uses exactly the
composition law below.

## Why the proof is clean (no direct associativity computation)

The naive route — proving the identity by `field_simp; ring` on the raw `addX`/`addY`/`slope`
formulae — is the full affine associativity of the group law, which Mathlib deliberately avoids.
Instead we work in the Mathlib group `(W ⁄ F(W)).Point`:

* `translateEndo h` is an `F`-algebra ring hom fixing the base `algebraMap F F(W)`
  (`translateEndo_algebraMap_base`), so it **commutes with the affine addition operations**
  `addX`/`addY`/`slope` of `W ⁄ F(W)` (`translateEndo_addX`/`_addY`/`_slope`, via Mathlib's
  `map_addX`/`map_addY`/`map_slope`).
* The generic `x`-coordinate and each of its translates is **transcendental over `F`**
  (`transcendental_translateEndo_genX`), so it is never equal to a constant `algebraMap F F(W) c`
  (`translateEndo_genX_ne`). Hence every intermediate sum is a *secant* addition
  (`Point.add_of_X_ne`) — no vertical/doubling degeneracy ever occurs at the generic point.

Reading `translateEndo hP (translateEndo hQ (genX))` as the `x`-coordinate of
`(𝒫 + 𝒯_P) + 𝒯_Q = 𝒫 + (𝒯_P + 𝒯_Q) = 𝒫 + 𝒯_R`, the composition law is `Point.add_assoc` plus the
group relation `𝒯_P + 𝒯_Q = 𝒯_R`.

## Scope

The only hypothesis on `P`, `Q`, `R` is the group relation `hsum` above; it presupposes that
`P ⊕ Q` is again a non-vertical affine point `R` (the "generic secant" locus of #432). The
degenerate corner `P ⊕ Q = O` (off the affine chart) is out of scope, as is discharging `hsum` from
an `F`-level point identity (a mechanical base-change transport, left as a follow-on).

⚠️ Both are still out of scope *of this file*, and both are merged elsewhere; the `## Scope`
sentence is left word for word because `EllipticCurves.FunctionField.TranslationAutomorphism`
quotes it. That module, which imports this one, states the degenerate corner separately as
`translateEndo_comp_zero` — from `translatePoint hP + translatePoint hQ = 0`, and concluding
`RingHom.id` rather than a `translateEndo hR`, since `hR` here ranges over affine points and `O` is
not one. The base-change transport is `CoordinateRing.translatePoint_add`
(`EllipticCurves.FunctionField.WeilPairingBilinearBaseField`, also downstream), which turns the
`F`-level relation `torsionPoint hP + torsionPoint hQ = torsionPoint hR` into `hsum` verbatim.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.2, III.3.4, III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine
namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {x₂ y₂ : F}

/-! ### `translateEndo` fixes the base field, is an algebra hom, and preserves transcendence -/

/-- `translateEndo h₂` fixes the image of `F` in `F(W)`. -/
lemma translateEndo_algebraMap_base (h₂ : W.Equation x₂ y₂) (c : F) :
    translateEndo h₂ (algebraMap F W.FunctionField c) = algebraMap F W.FunctionField c := by
  rw [IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField c, translateEndo_algebraMap,
    translateCoordHom_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- `translateEndo h₂` packaged as an `F`-algebra endomorphism of `F(W)`. -/
noncomputable def translateEndoAlgHom (h₂ : W.Equation x₂ y₂) :
    W.FunctionField →ₐ[F] W.FunctionField where
  toRingHom := translateEndo h₂
  commutes' := translateEndo_algebraMap_base h₂

@[simp] lemma translateEndoAlgHom_apply (h₂ : W.Equation x₂ y₂) (t : W.FunctionField) :
    translateEndoAlgHom h₂ t = translateEndo h₂ t := rfl

/-- The image of the generic `x`-coordinate under `translateEndo` is transcendental over `F`: it is
the injective `F`-algebra image of the transcendental `genX`. -/
lemma transcendental_translateEndo_genX (h₂ : W.Equation x₂ y₂) :
    Transcendental F (translateEndo h₂ (genX W)) := by
  intro halg
  obtain ⟨p, hp0, hp⟩ := halg
  refine transcendental_genX (W := W) ⟨p, hp0, ?_⟩
  have h0 : translateEndoAlgHom h₂ (Polynomial.aeval (genX W) p) = 0 := by
    rw [← Polynomial.aeval_algHom_apply]; exact hp
  exact (translateEndo h₂).injective (by rw [← translateEndoAlgHom_apply]; rw [h0, map_zero])

/-- The image of the generic `x`-coordinate under `translateEndo` is never a constant. -/
lemma translateEndo_genX_ne (h₂ : W.Equation x₂ y₂) (c : F) :
    translateEndo h₂ (genX W) ≠ algebraMap F W.FunctionField c := fun heq =>
  transcendental_translateEndo_genX h₂ (heq ▸ isAlgebraic_algebraMap c)

/-! ### Naturality of the affine addition operations under `translateEndo` -/

/-- Base-changing `W ⁄ F(W)` again along `translateEndo h₂` returns the same curve, because
`translateEndo h₂` fixes the base `algebraMap F F(W)`. -/
private lemma map_translateEndo_curve (h₂ : W.Equation x₂ y₂) :
    (W.map (algebraMap F W.FunctionField)).map (translateEndo h₂)
      = W.map (algebraMap F W.FunctionField) := by
  have hcomp : (translateEndo h₂).comp (algebraMap F W.FunctionField)
      = algebraMap F W.FunctionField := RingHom.ext (translateEndo_algebraMap_base h₂)
  simp only [WeierstrassCurve.map_map, hcomp]

/-- `translateEndo h₂` commutes with the addition-law `x`-coordinate `addX` of `W ⁄ F(W)`. -/
lemma translateEndo_addX (h₂ : W.Equation x₂ y₂) (x₁ x₃ ℓ : W.FunctionField) :
    translateEndo h₂ ((W.map (algebraMap F W.FunctionField)).addX x₁ x₃ ℓ)
      = (W.map (algebraMap F W.FunctionField)).addX
          (translateEndo h₂ x₁) (translateEndo h₂ x₃) (translateEndo h₂ ℓ) := by
  have h := WeierstrassCurve.Affine.map_addX (W' := W.map (algebraMap F W.FunctionField))
    (translateEndo h₂) (x₁ := x₁) (x₂ := x₃) (ℓ := ℓ)
  rw [map_translateEndo_curve h₂] at h
  exact h.symm

/-- `translateEndo h₂` commutes with the addition-law `y`-coordinate `addY` of `W ⁄ F(W)`. -/
lemma translateEndo_addY (h₂ : W.Equation x₂ y₂) (x₁ x₃ y₁ ℓ : W.FunctionField) :
    translateEndo h₂ ((W.map (algebraMap F W.FunctionField)).addY x₁ x₃ y₁ ℓ)
      = (W.map (algebraMap F W.FunctionField)).addY
          (translateEndo h₂ x₁) (translateEndo h₂ x₃) (translateEndo h₂ y₁)
          (translateEndo h₂ ℓ) := by
  have h := WeierstrassCurve.Affine.map_addY (W' := W.map (algebraMap F W.FunctionField))
    (translateEndo h₂) (x₁ := x₁) (x₂ := x₃) (y₁ := y₁) (ℓ := ℓ)
  rw [map_translateEndo_curve h₂] at h
  exact h.symm

open Classical in
/-- `translateEndo h₂` commutes with the slope `slope` of `W ⁄ F(W)`. -/
lemma translateEndo_slope (h₂ : W.Equation x₂ y₂) (x₁ x₃ y₁ y₃ : W.FunctionField) :
    translateEndo h₂ ((W.map (algebraMap F W.FunctionField)).slope x₁ x₃ y₁ y₃)
      = (W.map (algebraMap F W.FunctionField)).slope
          (translateEndo h₂ x₁) (translateEndo h₂ x₃)
          (translateEndo h₂ y₁) (translateEndo h₂ y₃) := by
  have h := WeierstrassCurve.Affine.map_slope (W := W.map (algebraMap F W.FunctionField))
    (translateEndo h₂) x₁ x₃ y₁ y₃
  rw [map_translateEndo_curve h₂] at h
  exact h.symm

/-! ### The composition law -/

/-- `translatePoint h₂` unfolded to a `Point.some`, for rewriting into the addition law. -/
private lemma translatePoint_eq (h₂ : W.Equation x₂ y₂) :
    translatePoint h₂ = Point.some (algebraMap F W.FunctionField x₂)
      (algebraMap F W.FunctionField y₂) (nonsingular_translatePoint h₂) := rfl

open Classical in
/-- **The composition law on the coordinate generators.** For affine points `P`, `Q`, `R` with
`P ⊕ Q = R` (as the constant-point identity `𝒯_P + 𝒯_Q = 𝒯_R` over `F(W)`), the translation
pullbacks compose contravariantly on the generic point's coordinates. -/
theorem translateEndo_comp_apply_gen {xP yP xQ yQ xR yR : F}
    (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ) (hR : W.Equation xR yR)
    (hsum : translatePoint hP + translatePoint hQ = translatePoint hR) :
    translateEndo hP (translateEndo hQ (genX W)) = translateEndo hR (genX W)
      ∧ translateEndo hP (translateEndo hQ (genY W)) = translateEndo hR (genY W) := by
  have hAne : translateEndo hP (genX W) ≠ algebraMap F W.FunctionField xQ :=
    translateEndo_genX_ne hP xQ
  have hP' := genericPoint_add_translatePoint hP
  have hR' := genericPoint_add_translatePoint hR
  -- Compute `(𝒫 + 𝒯_P) + 𝒯_Q` two ways: as a secant sum, and as `𝒫 + 𝒯_R`.
  have hkey :
      (Point.some (translateEndo hP (genX W)) (translateEndo hP (genY W))
          (nonsingular_translateEndo_gen hP)) + translatePoint hQ
        = genericPoint + translatePoint hR := by
    rw [← hP', add_assoc, hsum]
  rw [translatePoint_eq hQ, Point.add_of_X_ne hAne, hR', Point.some.injEq] at hkey
  refine ⟨?_, ?_⟩
  · rw [translateEndo_genX hQ, translateEndo_addX, translateEndo_slope]
    simp only [translateEndo_algebraMap_base]
    exact hkey.1
  · rw [translateEndo_genY hQ, translateEndo_addY, translateEndo_slope]
    simp only [translateEndo_algebraMap_base]
    exact hkey.2

open Classical in
/-- **The composition law for `translateEndo`.** For affine points `P`, `Q`, `R` with `P ⊕ Q = R`
(as the constant-point identity `𝒯_P + 𝒯_Q = 𝒯_R` over `F(W)`),
`translateEndo hP ∘ translateEndo hQ = translateEndo hR`. This is the contravariant functoriality of
the translation pullback with respect to the group law — the keystone of `e_n` bilinearity
(#419). -/
theorem translateEndo_comp {xP yP xQ yQ xR yR : F}
    (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ) (hR : W.Equation xR yR)
    (hsum : translatePoint hP + translatePoint hQ = translatePoint hR) :
    (translateEndo hP).comp (translateEndo hQ) = translateEndo hR := by
  obtain ⟨hx, hy⟩ := translateEndo_comp_apply_gen hP hQ hR hsum
  -- Reduce to agreement on the coordinate ring, then to the two generators.
  have hcr : (translateEndo hP).comp (translateCoordHom hQ) = translateCoordHom hR := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · -- constants: both sides reduce to `algebraMap F F(W) c`
      have hofC : AdjoinRoot.of W.polynomial (C c) = algebraMap F W.CoordinateRing c := by
        rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq,
          ← Polynomial.C_eq_algebraMap]
      simp only [RingHom.comp_apply, hofC, translateCoordHom_algebraMap,
        translateEndo_algebraMap_base]
    · -- the `X`-generator: this is `hx`, read through `genX = algebraMap _ _ (mk (C X))`
      have hxc : translateEndo hP (translateCoordHom hQ (mk W (C X)))
          = translateCoordHom hR (mk W (C X)) := by
        have h := hx
        rw [genX, genPsi] at h
        simpa only [translateEndo_algebraMap] using h
      simpa only [RingHom.comp_apply,
        show AdjoinRoot.of W.polynomial X = mk W (C X) from rfl] using hxc
    · -- the root generator: this is `hy`, read through `genY = algebraMap _ _ root`
      have hyc : translateEndo hP (translateCoordHom hQ (AdjoinRoot.root W.polynomial))
          = translateCoordHom hR (AdjoinRoot.root W.polynomial) := by
        have h := hy
        rw [genY, genPsi] at h
        simpa only [translateEndo_algebraMap] using h
      simpa only [RingHom.comp_apply] using hyc
  refine IsFractionRing.ringHom_ext (A := W.CoordinateRing) (fun a => ?_)
  rw [RingHom.comp_apply, translateEndo_algebraMap, translateEndo_algebraMap,
    ← RingHom.comp_apply, hcr]

/-- The composition law in applied form:
`translateEndo hP (translateEndo hQ g) = translateEndo hR g` for every `g`. The form the `e_n`
bilinearity derivation uses directly. -/
theorem translateEndo_translateEndo_apply {xP yP xQ yQ xR yR : F}
    (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ) (hR : W.Equation xR yR)
    (hsum : translatePoint hP + translatePoint hQ = translatePoint hR) (g : W.FunctionField) :
    translateEndo hP (translateEndo hQ g) = translateEndo hR g := by
  have := translateEndo_comp hP hQ hR hsum
  exact congr($this g)

end CoordinateRing
end WeierstrassCurve.Affine
