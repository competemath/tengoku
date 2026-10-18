/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FunctionField.TranslationEndomorphism

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The generic point as a `Point` over `F(W)`, and the translation correspondence

Let `W` be an elliptic curve over a field `F`.  Its affine function field `F(W)` is again a field,
so the base-changed curve `W ⁄ F(W) = W.map (algebraMap F F(W))` is an elliptic curve over `F(W)`
(`(W.map f).IsElliptic` is automatic), and the **generic point** `(genX W, genY W)` — which
satisfies the Weierstrass equation (`equation_gen`) — is a *nonsingular* affine point, hence an
element of the Mathlib group `(W ⁄ F(W)).Point`.

This file packages that group-theoretic view of `F(W)`:

* `nonsingular_gen`  — the generic point is nonsingular (`equation_iff_nonsingular` on the elliptic
  base-changed curve);
* `genericPoint`     — the generic point `𝒫 := (genX W, genY W)` as a `(W ⁄ F(W)).Point`;
* `translatePoint`   — a fixed `F`-point `T = (x₂, y₂)` (`h₂ : W.Equation x₂ y₂`) as the constant
  `(W ⁄ F(W)).Point` `𝒯 := (x₂, y₂)`;
* `genericPoint_add_translatePoint` — the **translation correspondence**: the translation
  endomorphism `translateEndo h₂` acts on the coordinate generators exactly as `+ 𝒯` in the group,
  i.e. `𝒫 + 𝒯 = (translateEndo h₂ (genX W), translateEndo h₂ (genY W))`.

## Why this is the foundation for the `hcomm` discharge (#419 / #433)

The rung-6 Weil-pairing element (`WeilPairing.lean`, #419) still carries the hypothesis
`hcomm : translateEndo h₂ ([n]∗ f) = [n]∗ f`, geometrically `[n](P + T) = [n]P` for an `n`-torsion
point `T`.  Reading `translateEndo` as `+ 𝒯` (this file) and `mulBy{Two,Three}Endo` as `[n]•`
(the follow-on doubling/tripling bridge, cf. #251), `hcomm` becomes the group identity
`[n]•(𝒫 + 𝒯) = [n]•𝒫 + [n]•𝒯 = [n]•𝒫` from `[n]•𝒯 = 0`.  Everything here is Ward- and
normality-independent: it needs only `[Field F] [W.IsElliptic]`, no `IsDedekindDomain` and no
elliptic-net machinery.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.8.
-/

namespace WeierstrassCurve.Affine

namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic]

/-- **The generic point is nonsingular.** On the elliptic base-changed curve `W ⁄ F(W)`, every point
satisfying the Weierstrass equation is nonsingular; the generic point does (`equation_gen`). -/
theorem nonsingular_gen :
    (W.map (algebraMap F W.FunctionField)).Nonsingular (genX W) (genY W) :=
  (W.map (algebraMap F W.FunctionField)).equation_iff_nonsingular.mp equation_gen

/-- **The generic point** `𝒫 := (genX W, genY W)` as an element of the group `(W ⁄ F(W)).Point`. -/
noncomputable def genericPoint : (W.map (algebraMap F W.FunctionField)).Point :=
  .some (genX W) (genY W) nonsingular_gen

/-- A fixed `F`-point `T = (x₂, y₂)` on `W` is nonsingular after base change to `F(W)`
(`map_nonsingular` transports nonsingularity along the injective `algebraMap F F(W)`, and every
equation point of the elliptic curve `W` is nonsingular). -/
theorem nonsingular_translatePoint {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) :
    (W.map (algebraMap F W.FunctionField)).Nonsingular
      (algebraMap F W.FunctionField x₂) (algebraMap F W.FunctionField y₂) :=
  (W.map_nonsingular (algebraMap F W.FunctionField).injective x₂ y₂).mpr
    (W.equation_iff_nonsingular.mp h₂)

/-- **The translation point** `𝒯 := (x₂, y₂)` (the fixed `F`-point `T`) as a constant element of the
group `(W ⁄ F(W)).Point`. -/
noncomputable def translatePoint {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) :
    (W.map (algebraMap F W.FunctionField)).Point :=
  .some (algebraMap F W.FunctionField x₂) (algebraMap F W.FunctionField y₂)
    (nonsingular_translatePoint h₂)

/-- The coordinates of `𝒫 + 𝒯` are nonsingular — a repackaging of `translateEndo_genX`/`_genY`
against the sum-point coordinates produced by the affine addition law (`add_of_X_ne`, valid because
`genX W ≠ algebraMap F F(W) x₂` by `genX_ne`). -/
theorem nonsingular_translateEndo_gen {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) :
    (W.map (algebraMap F W.FunctionField)).Nonsingular
      (translateEndo h₂ (genX W)) (translateEndo h₂ (genY W)) := by
  rw [translateEndo_genX, translateEndo_genY]
  exact nonsingular_add nonsingular_gen (nonsingular_translatePoint h₂)
    (fun hxy => genX_ne x₂ hxy.left)

open Classical in
/-- **The translation correspondence.** The translation endomorphism `translateEndo h₂` acts on the
coordinate generators of `F(W)` exactly as `+ 𝒯` in the group `(W ⁄ F(W)).Point`:

```
𝒫 + 𝒯 = (translateEndo h₂ (genX W), translateEndo h₂ (genY W)).
```

Since `genX W ≠ algebraMap F F(W) x₂` (`genX_ne`), the affine sum takes the secant branch
(`add_of_X_ne`), whose coordinates are the `addX`/`addY` of the addition law — which are precisely
`translateEndo_genX`/`translateEndo_genY`.  This is the group-theoretic reading of `translateEndo`
that the `hcomm` discharge of #419 consumes. -/
theorem genericPoint_add_translatePoint {x₂ y₂ : F} (h₂ : W.Equation x₂ y₂) :
    genericPoint + translatePoint h₂
      = .some (translateEndo h₂ (genX W)) (translateEndo h₂ (genY W))
          (nonsingular_translateEndo_gen h₂) := by
  rw [genericPoint, translatePoint, Point.add_of_X_ne (genX_ne x₂), Point.some.injEq]
  exact ⟨(translateEndo_genX h₂).symm, (translateEndo_genY h₂).symm⟩

end CoordinateRing

end WeierstrassCurve.Affine
