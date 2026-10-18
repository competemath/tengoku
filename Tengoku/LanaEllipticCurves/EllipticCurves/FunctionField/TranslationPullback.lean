/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Formula

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The translation-by-a-point pullback on the function field of a Weierstrass curve

Let `W` be a Weierstrass curve over a field `F`, with affine coordinate ring
`F[W] = AdjoinRoot W.polynomial` and function field `F(W) = Frac F[W]`. For a fixed affine point
`T = (x₂, y₂)` on `W` (`h₂ : W.Equation x₂ y₂`), the translation map `P ↦ P + T` is a morphism of
the curve, and pulling back rational functions along it gives an `F`-algebra endomorphism of `F(W)`.
This file builds the *coordinate-ring half* of that pullback: the ring homomorphism

* `WeierstrassCurve.Affine.CoordinateRing.translateCoordHom h₂ : F[W] →+* F(W)`

sending the generic point `P = (x, y)` to `P + T`, i.e. realising on the coordinate generators

* `x ↦ addX x x₂ (slope x x₂ y y₂)` and
* `y ↦ addY x x₂ y (slope x x₂ y y₂)`

using Mathlib's affine chord-and-tangent addition formulae over the base-changed curve
`W ⁄ F(W)`. This is the second substrate consumed by a divisor-theoretic Weil pairing (the pairing
`e_n(S, T) = g_S(X + T) / g_S(X)` has `g_S ∘ (· + T)` as its numerator), and is a peer of the
multiplication-by-`n` pullback `[n]∗`.

## The construction

`W.CoordinateRing = AdjoinRoot W.polynomial` has base ring `F[X]`, so `AdjoinRoot.lift` needs
a ring hom `i : F[X] →+* F(W)` (the image of the `X`-variable), the image of the root `Y`, and a
proof of the single obligation `W.polynomial.eval₂ i (root image) = 0`. We take `i` and the root
image to be the `x`- and `y`-coordinates of `P + T`, and discharge the obligation by

* the **generic point on the curve** `equation_gen` — that the coordinate generators `(genX, genY)`
  satisfy the Weierstrass equation over `F(W)` (a transport of `AdjoinRoot.eval₂_root` through the
  bivariate evaluation bridge `Polynomial.eval₂_eval₂RingHom_apply`);
* Mathlib's on-curve **addition identity** `WeierstrassCurve.Affine.equation_add`, applied over the
  base-changed curve `W ⁄ F(W)` to the generic point and to `T` (transported by `Equation.map`);
* the **genericity** `genX_ne` — that the generic `x`-coordinate is not the constant `x₂`, so the
  secant slope is the applicable branch.

## Main definitions and statements

* `WeierstrassCurve.Affine.CoordinateRing.genX` / `genY`: the coordinate generators of `F(W)`.
* `WeierstrassCurve.Affine.CoordinateRing.equation_gen`: the generic point lies on `W ⁄ F(W)`.
* `WeierstrassCurve.Affine.CoordinateRing.genX_ne`: genericity of the `x`-coordinate.
* `WeierstrassCurve.Affine.CoordinateRing.translateCoordHom`: the translation pullback
  `F[W] →+* F(W)`, with generator images `translateCoordHom_X` and `translateCoordHom_root`.

## The endomorphism is built elsewhere, and the route predicted here was not taken

⚠️ **This section used to be headed `## Remaining work`** and to read:

> Extending `translateCoordHom : F[W] →+* F(W)` to the full endomorphism `F(W) →+* F(W)` needs
> `Function.Injective (translateCoordHom h₂)` (so that `IsFractionRing.lift` applies) — i.e. that
> the translation map is *dominant*. This is true because `T` is defined over `F`, so `P ↦ P + T`
> is an `F`-automorphism of the curve with inverse `P ↦ P + (-T)`; the clean route is to build the
> pullback along `-T` and compose. That is deferred to a follow-up (it requires the
> coordinate-level identity `(P + T) + (-T) = P`).

The extension is `WeierstrassCurve.Affine.CoordinateRing.translateEndo`
(`EllipticCurves.FunctionField.TranslationEndomorphism`), off `translateCoordHom_injective`.

⚠️ **The predicted route was not taken, and the difference is worth keeping.**  No pullback along
`-T` is ever built, and nothing is composed.  The cancellation `(P + T) + (-T) = P` is used
*inside the dominance argument* instead: `genX_mem_algebraicClosure_of` (again
`EllipticCurves.FunctionField.TranslationEndomorphism`) evaluates it at the generic
point to conclude that if the translated coordinates are algebraic over `F` then so is `genX`,
contradicting `transcendental_genX`; injectivity then comes from the kernel being a maximal ideal
of the one-dimensional domain `F[W]` and Zariski's lemma.  A `-T` pullback would have been a second
`AdjoinRoot.lift` with its own on-curve obligation; the identity turned out to be needed only as a
group relation.  The composition-with-`-T` statement does exist, but one layer higher and for a
different purpose — `translateEndo_comp_zero`
(`EllipticCurves.FunctionField.TranslationAutomorphism`), which upgrades the already-built
endomorphism to an `AlgEquiv`.

The reusable crux — the generic point on the curve and the on-curve identity for `P + T` — is what
this file establishes.

## ⚠️ One `@[simp]` attribute was removed here, and the lemma kept (`#1278`)

`translateCoordHom_X` carried `@[simp]` and **could never fire**: its LHS is `mk W (C X)`, and
`AdjoinRoot.mk_C` — itself `@[simp]` — rewrites that to `AdjoinRoot.of W.polynomial X` before the
pattern is tried. Measured with Mathlib's `simpNF` environment linter, which had never been run on
this tree. The lemma is unchanged and still used by name here and in
`EllipticCurves.FunctionField.TranslationEndomorphism`.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.2 (the addition law),
  III.8 (the Weil pairing).
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine
namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F}

/-- The structural algebra map `F[W] →+* F(W)` embedding the coordinate ring into its function
field. -/
noncomputable abbrev genPsi (W : Affine F) : W.CoordinateRing →+* W.FunctionField :=
  algebraMap W.CoordinateRing W.FunctionField

/-- The generic `x`-coordinate: the image of the class of `X` in `F(W)`. -/
noncomputable def genX (W : Affine F) : W.FunctionField := genPsi W (mk W (C X))

/-- The generic `y`-coordinate: the image of the root of `W.polynomial` in `F(W)`. -/
noncomputable def genY (W : Affine F) : W.FunctionField := genPsi W (AdjoinRoot.root W.polynomial)

/-- **The generic point lies on the curve.** The coordinate generators `(genX, genY)` of `F(W)`
satisfy the Weierstrass equation of the base-changed curve `W ⁄ F(W)`. -/
lemma equation_gen : (W.map (algebraMap F W.FunctionField)).Equation (genX W) (genY W) := by
  set φ := algebraMap F W.FunctionField with hφ
  set ψ := genPsi W with hψ
  have key : W.polynomial.eval₂ (ψ.comp (AdjoinRoot.of W.polynomial)) (genY W) = 0 := by
    rw [genY, ← hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
  have hcomp : (ψ.comp (AdjoinRoot.of W.polynomial)) = eval₂RingHom φ (genX W) := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, hφ, hψ, genPsi,
        ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
        Polynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
    · rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, genX, genPsi, hψ]
      rfl
  change (W.map φ).polynomial.evalEval (genX W) (genY W) = 0
  rw [map_polynomial, ← eval₂_eval₂RingHom_apply, ← hcomp, key]

/-- The image of a base constant `C (C c)` under `mk`, pushed into `F(W)`, is `algebraMap F _ c`. -/
lemma genPsi_mk_CC (c : F) :
    genPsi W (mk W (C (C c))) = algebraMap F W.FunctionField c := by
  have h1 : mk W (C (C c)) = algebraMap F W.CoordinateRing c := by
    rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq,
      ← Polynomial.C_eq_algebraMap]
    rfl
  rw [genPsi, h1, ← IsScalarTower.algebraMap_apply]

/-- **Genericity.** The generic `x`-coordinate is not the constant `x₂`. -/
lemma genX_ne (x₂ : F) : genX W ≠ algebraMap F W.FunctionField x₂ := by
  have hgen : genX W - algebraMap F W.FunctionField x₂ = genPsi W (XClass W x₂) := by
    rw [XClass, C_sub, map_sub, map_sub, ← genX, ← genPsi_mk_CC (W := W) x₂]
  intro h
  have hz : genPsi W (XClass W x₂) = 0 := by rw [← hgen, h, sub_self]
  exact XClass_ne_zero (W' := W) x₂ ((injective_iff_map_eq_zero _).mp
    (IsFractionRing.injective W.CoordinateRing W.FunctionField) _ hz)

variable {x₂ y₂ : F}

open Classical in
/-- **The translation pullback (coordinate-ring half).** The ring homomorphism `F[W] →+* F(W)`
sending the generic point `P = (x, y)` to `P + T` for the fixed point `T = (x₂, y₂)`. It is
`AdjoinRoot.lift` of the addition-law coordinates of `P + T`, whose well-definedness obligation
`W.polynomial.eval₂ _ _ = 0` is exactly that `P + T` lies on the curve, discharged by
`equation_add` applied to the generic point (`equation_gen`) and to `T`. -/
noncomputable def translateCoordHom (h₂ : W.Equation x₂ y₂) :
    W.CoordinateRing →+* W.FunctionField :=
  AdjoinRoot.lift
    (eval₂RingHom (algebraMap F W.FunctionField)
      ((W.map (algebraMap F W.FunctionField)).addX (genX W) (algebraMap F W.FunctionField x₂)
        ((W.map (algebraMap F W.FunctionField)).slope (genX W) (algebraMap F W.FunctionField x₂)
          (genY W) (algebraMap F W.FunctionField y₂))))
    ((W.map (algebraMap F W.FunctionField)).addY (genX W) (algebraMap F W.FunctionField x₂) (genY W)
      ((W.map (algebraMap F W.FunctionField)).slope (genX W) (algebraMap F W.FunctionField x₂)
        (genY W) (algebraMap F W.FunctionField y₂)))
    (by
      rw [eval₂_eval₂RingHom_apply, ← map_polynomial]
      exact equation_add equation_gen (h₂.map (algebraMap F W.FunctionField))
        (fun hh => genX_ne x₂ hh.1))

open Classical in
/-- Image of the `x`-generator under the translation pullback: the `x`-coordinate of `P + T`. -/
lemma translateCoordHom_X (h₂ : W.Equation x₂ y₂) :
    translateCoordHom h₂ (mk W (C X)) =
      (W.map (algebraMap F W.FunctionField)).addX (genX W) (algebraMap F W.FunctionField x₂)
        ((W.map (algebraMap F W.FunctionField)).slope (genX W) (algebraMap F W.FunctionField x₂)
          (genY W) (algebraMap F W.FunctionField y₂)) := by
  rw [translateCoordHom,
    show mk W (C X) = AdjoinRoot.of W.polynomial X from rfl,
    AdjoinRoot.lift_of, coe_eval₂RingHom, eval₂_X]

open Classical in
/-- Image of the `y`-generator (the root) under the translation pullback: the `y`-coordinate of
`P + T`. -/
@[simp] lemma translateCoordHom_root (h₂ : W.Equation x₂ y₂) :
    translateCoordHom h₂ (AdjoinRoot.root W.polynomial) =
      (W.map (algebraMap F W.FunctionField)).addY (genX W) (algebraMap F W.FunctionField x₂)
        (genY W)
        ((W.map (algebraMap F W.FunctionField)).slope (genX W) (algebraMap F W.FunctionField x₂)
          (genY W) (algebraMap F W.FunctionField y₂)) := by
  rw [translateCoordHom, AdjoinRoot.lift_root]

end CoordinateRing
end WeierstrassCurve.Affine
