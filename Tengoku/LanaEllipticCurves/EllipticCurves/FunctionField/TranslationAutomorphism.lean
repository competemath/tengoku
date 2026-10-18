/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FunctionField.TranslationComposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Translation by a point is an *automorphism* of the function field

For an elliptic curve `W` over a field `F` and an affine point `T = (x₂, y₂)` on `W`, the
translation pullback `translateEndo h₂ : F(W) →+* F(W)`
(`EllipticCurves.FunctionField.TranslationEndomorphism`) reads on the generic point as `+ 𝒯` in the
group `(W ⁄ F(W)).Point`.  This file shows it is **invertible**, with inverse the translation by
`-T`, and packages it as

```lean
translateAlgEquiv h₂ : W.FunctionField ≃ₐ[F] W.FunctionField.
```

## Why this is not already available

`EllipticCurves.FunctionField.TranslationComposition` proves the contravariant composition law

```lean
translateEndo_comp (hsum : translatePoint hP + translatePoint hQ = translatePoint hR) :
    (translateEndo hP).comp (translateEndo hQ) = translateEndo hR
```

but invertibility is the case `P ⊕ Q = O`, which **cannot be stated in that signature**: `hR` ranges
over affine points and `O` is not one.  That file's scope note says as much — *"The degenerate
corner `P ⊕ Q = O` (off the affine chart) is out of scope"*.  It is a hole in the indexing, not an
oversight, and it is filled here by a separate zero-sum composition law
(`translateEndo_comp_zero`).  The merged `translateEndo_comp` is left untouched: six `WeilPairing*`
files consume its signature.

## Why the `AlgEquiv` matters

A place of `F(W)` is formalised as a `ValuationSubring`, and what transports valuation subrings is a
ring *automorphism* of the field — an `→ₐ[F]` does not suffice.  So any statement of the form "`τ_T`
permutes the points of the projective curve" needs `τ_T` at this type.  The `→ₐ[F]` form
(`translateEndoAlgHom`, merged) is the strongest thing that existed before this file.

## Main statements

* `WeierstrassCurve.Affine.CoordinateRing.translatePoint_neg` — the constant point of `-T` is the
  negation of the constant point of `T`, hence `𝒯_T + 𝒯_{-T} = 0`;
* `WeierstrassCurve.Affine.CoordinateRing.translateEndo_comp_zero` — the composition law in the
  degenerate case `P ⊕ Q = O`: `translateEndo hP ∘ translateEndo hQ = id`;
* `WeierstrassCurve.Affine.CoordinateRing.translateEndo_bijective`;
* **`WeierstrassCurve.Affine.CoordinateRing.translateAlgEquiv`** — `τ_T` as an `F`-algebra
  automorphism of `F(W)`, with `translateAlgEquiv_apply` and `translateAlgEquiv_symm_apply`;
* `WeierstrassCurve.Affine.CoordinateRing.translateAlgEquiv_ne_one` and
  `…nontrivial_algEquiv_of_equation` — translation by an affine `T` is never the identity, so
  `Aut_F F(W)` is nontrivial whenever `W` has an affine `F`-point.  This is the non-vacuity
  certificate; note it is conditional on such a point existing, which is a condition on `F`.

## Scope

Nothing here mentions divisors, places, or `ProjPoint`; this file only supplies the type the
divisor pullback under translation is stated against.  ⚠️ That pullback is **not** gated and is
**not** `#465` deliverable 2, both of which this bullet used to say.  It is
`divisorProj_translateEndo` (`EllipticCurves.FunctionField.PlaceOrder`), on the projective divisor
group; only the affine `divisor W` fails to transport.  And deliverable 2 — the alternating
property — is proved at both `n = 2` and `n = 3` over `F̄`.  ⚠️ **That sentence used to end *"by a
route that needs no such pullback"*, and with `divisorProj_translateEndo` as the antecedent it was
false**: the route runs on the telescoping functions of
`EllipticCurves.FunctionField.WeilPairingTelescopeTwo` and
`EllipticCurves.FunctionField.WeilPairingTelescopeThree`, both downstream of this file, and their
divisor steps rewrite with exactly that theorem.  What the route never needs is the **affine**
formula, which is the one `EllipticCurves.FunctionField.DivisorTransport` records as undelivered.

## References

* [J. Silverman, *The arithmetic of elliptic curves*][silverman2009], III.2, III.4, III.8.
-/

open Polynomial

namespace WeierstrassCurve.Affine
namespace CoordinateRing

variable {F : Type*} [Field F] {W : Affine F} [W.IsElliptic] {x₂ y₂ : F}

/-! ### The negated translation point -/

/-- **The constant point of `-T` is the negation of the constant point of `T`.**  Both sides are
`Point.some` at the same `x`-coordinate; the `y`-coordinates agree by `map_negY`, which is the only
content. -/
theorem translatePoint_neg (h₂ : W.Equation x₂ y₂) :
    translatePoint ((W.equation_neg x₂ y₂).mpr h₂) = -translatePoint h₂ := by
  rw [translatePoint, translatePoint, Point.neg_some, Point.some.injEq]
  exact ⟨rfl, (map_negY _ _ _).symm⟩

/-- `𝒯_T + 𝒯_{-T} = 0` in `(W ⁄ F(W)).Point`. -/
theorem translatePoint_add_neg (h₂ : W.Equation x₂ y₂) :
    translatePoint h₂ + translatePoint ((W.equation_neg x₂ y₂).mpr h₂) = 0 := by
  rw [translatePoint_neg h₂, add_neg_cancel]

/-- `𝒯_{-T} + 𝒯_T = 0` in `(W ⁄ F(W)).Point`. -/
theorem translatePoint_neg_add (h₂ : W.Equation x₂ y₂) :
    translatePoint ((W.equation_neg x₂ y₂).mpr h₂) + translatePoint h₂ = 0 := by
  rw [translatePoint_neg h₂, neg_add_cancel]

/-! ### The composition law in the degenerate case `P ⊕ Q = O` -/

/-- `translatePoint h₂` unfolded to a `Point.some`, for rewriting into the addition law. -/
private lemma translatePoint_eq_some (h₂ : W.Equation x₂ y₂) :
    translatePoint h₂ = Point.some (algebraMap F W.FunctionField x₂)
      (algebraMap F W.FunctionField y₂) (nonsingular_translatePoint h₂) := rfl

open Classical in
/-- **The composition law on the coordinate generators, degenerate case.**  For affine points `P`,
`Q` with `P ⊕ Q = O` (as the constant-point identity `𝒯_P + 𝒯_Q = 0` over `F(W)`), the two
translation pullbacks compose to the identity on the generic point's coordinates.

The proof is `translateEndo_comp_apply_gen` with `𝒯_R` replaced by `0`: reading
`(𝒫 + 𝒯_P) + 𝒯_Q` as a secant sum on one side (legitimate because
`translateEndo hP (genX W)` is transcendental over `F`, hence never the constant `xQ`) and as
`𝒫 + (𝒯_P + 𝒯_Q) = 𝒫 + 0 = 𝒫` on the other. -/
theorem translateEndo_comp_apply_gen_zero {xP yP xQ yQ : F}
    (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ)
    (hsum : translatePoint hP + translatePoint hQ = 0) :
    translateEndo hP (translateEndo hQ (genX W)) = genX W
      ∧ translateEndo hP (translateEndo hQ (genY W)) = genY W := by
  have hAne : translateEndo hP (genX W) ≠ algebraMap F W.FunctionField xQ :=
    translateEndo_genX_ne hP xQ
  have hP' := genericPoint_add_translatePoint hP
  -- Compute `(𝒫 + 𝒯_P) + 𝒯_Q` two ways: as a secant sum, and as `𝒫 + 0 = 𝒫`.
  have hkey :
      (Point.some (translateEndo hP (genX W)) (translateEndo hP (genY W))
          (nonsingular_translateEndo_gen hP)) + translatePoint hQ
        = genericPoint := by
    rw [← hP', add_assoc, hsum, add_zero]
  rw [translatePoint_eq_some hQ, Point.add_of_X_ne hAne, genericPoint, Point.some.injEq] at hkey
  refine ⟨?_, ?_⟩
  · rw [translateEndo_genX hQ, translateEndo_addX, translateEndo_slope]
    simp only [translateEndo_algebraMap_base]
    exact hkey.1
  · rw [translateEndo_genY hQ, translateEndo_addY, translateEndo_slope]
    simp only [translateEndo_algebraMap_base]
    exact hkey.2

open Classical in
/-- **The composition law for `translateEndo`, degenerate case.**  For affine points `P`, `Q` with
`P ⊕ Q = O`, `translateEndo hP ∘ translateEndo hQ = id`.  This is the statement the merged
`translateEndo_comp` cannot make, because its target `translateEndo hR` is indexed by an affine
point and `O` is not one. -/
theorem translateEndo_comp_zero {xP yP xQ yQ : F}
    (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ)
    (hsum : translatePoint hP + translatePoint hQ = 0) :
    (translateEndo hP).comp (translateEndo hQ) = RingHom.id W.FunctionField := by
  obtain ⟨hx, hy⟩ := translateEndo_comp_apply_gen_zero hP hQ hsum
  -- Reduce to agreement on the coordinate ring, then to the two generators.
  have hcr : (translateEndo hP).comp (translateCoordHom hQ)
      = algebraMap W.CoordinateRing W.FunctionField := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c => ?_) ?_) ?_
    · -- constants: both sides reduce to `algebraMap F F(W) c`
      have hofC : AdjoinRoot.of W.polynomial (C c) = algebraMap F W.CoordinateRing c := by
        rw [IsScalarTower.algebraMap_apply F F[X] W.CoordinateRing, AdjoinRoot.algebraMap_eq,
          ← Polynomial.C_eq_algebraMap]
      simp only [RingHom.comp_apply, hofC, translateCoordHom_algebraMap,
        translateEndo_algebraMap_base, ← IsScalarTower.algebraMap_apply]
    · -- the `X`-generator: this is `hx`, read through `genX = algebraMap _ _ (mk (C X))`
      have hxc : translateEndo hP (translateCoordHom hQ (mk W (C X)))
          = algebraMap W.CoordinateRing W.FunctionField (mk W (C X)) := by
        have h := hx
        rw [genX, genPsi] at h
        simpa only [translateEndo_algebraMap] using h
      simpa only [RingHom.comp_apply,
        show AdjoinRoot.of W.polynomial X = mk W (C X) from rfl] using hxc
    · -- the root generator: this is `hy`, read through `genY = algebraMap _ _ root`
      have hyc : translateEndo hP (translateCoordHom hQ (AdjoinRoot.root W.polynomial))
          = algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.root W.polynomial) := by
        have h := hy
        rw [genY, genPsi] at h
        simpa only [translateEndo_algebraMap] using h
      simpa only [RingHom.comp_apply] using hyc
  refine IsFractionRing.ringHom_ext (A := W.CoordinateRing) (fun a => ?_)
  rw [RingHom.comp_apply, translateEndo_algebraMap, ← RingHom.comp_apply, hcr, RingHom.id_apply]

/-- The degenerate composition law in applied form. -/
theorem translateEndo_translateEndo_apply_zero {xP yP xQ yQ : F}
    (hP : W.Equation xP yP) (hQ : W.Equation xQ yQ)
    (hsum : translatePoint hP + translatePoint hQ = 0) (g : W.FunctionField) :
    translateEndo hP (translateEndo hQ g) = g := by
  have := translateEndo_comp_zero hP hQ hsum
  exact congr($this g)

/-! ### `translateEndo` is bijective -/

/-- **Translation by `T` is surjective on `F(W)`**: `g = τ_T(τ_{-T}(g))`. -/
theorem translateEndo_surjective (h₂ : W.Equation x₂ y₂) :
    Function.Surjective (translateEndo h₂) := fun g =>
  ⟨translateEndo ((W.equation_neg x₂ y₂).mpr h₂) g,
    translateEndo_translateEndo_apply_zero h₂ _ (translatePoint_add_neg h₂) g⟩

/-- **Translation by `T` is bijective on `F(W)`.**  Injectivity is automatic (a ring hom out of a
field); surjectivity is `translateEndo_surjective`. -/
theorem translateEndo_bijective (h₂ : W.Equation x₂ y₂) :
    Function.Bijective (translateEndo h₂) :=
  ⟨(translateEndo h₂).injective, translateEndo_surjective h₂⟩

/-! ### `τ_T` as an `F`-algebra automorphism -/

/-- **Translation by an affine point `T`, as an `F`-algebra automorphism of `F(W)`.**  The inverse
is translation by `-T`.

This is the type at which `τ_T` can act on the places of `F(W)`: a `ValuationSubring` is transported
by a ring *automorphism*, and the merged `translateEndoAlgHom` is only an `F(W) →ₐ[F] F(W)`. -/
noncomputable def translateAlgEquiv (h₂ : W.Equation x₂ y₂) :
    W.FunctionField ≃ₐ[F] W.FunctionField :=
  AlgEquiv.ofAlgHom (translateEndoAlgHom h₂) (translateEndoAlgHom ((W.equation_neg x₂ y₂).mpr h₂))
    (AlgHom.ext fun g =>
      translateEndo_translateEndo_apply_zero h₂ _ (translatePoint_add_neg h₂) g)
    (AlgHom.ext fun g =>
      translateEndo_translateEndo_apply_zero _ h₂ (translatePoint_neg_add h₂) g)

@[simp] lemma translateAlgEquiv_apply (h₂ : W.Equation x₂ y₂) (g : W.FunctionField) :
    translateAlgEquiv h₂ g = translateEndo h₂ g := rfl

@[simp] lemma translateAlgEquiv_symm_apply (h₂ : W.Equation x₂ y₂) (g : W.FunctionField) :
    (translateAlgEquiv h₂).symm g = translateEndo ((W.equation_neg x₂ y₂).mpr h₂) g := rfl

/-! ### Non-vacuity: `Aut_F F(W)` is not trivial -/

/-- **Translation by an affine point is never the identity automorphism.**

If it were, then `τ_T` would fix both coordinate generators, so
`genericPoint_add_translatePoint` would read `𝒫 + 𝒯_T = 𝒫`, forcing `𝒯_T = 0` — impossible, since
`𝒯_T` is a `Point.some`.  Note there is no `T = O` to exclude: `translateAlgEquiv` is indexed by an
`Equation`, so `T` is affine by construction.

Together with `nontrivial_algEquiv_of_equation` this is the certificate that a statement about how
`Aut_F F(W)` acts on the places of `F(W)` is not a statement about a one-element group — **provided
`W` has an affine `F`-point at all**, which is a condition on `F` and is not claimed here.  It holds
whenever `F` is algebraically closed with `(2 : F) ≠ 0`
(`WeierstrassCurve.Affine.exists_equation`, `EllipticCurves/Torsion/ThreeTorsionStructure.lean`);
that file is deliberately not imported, to keep this one a leaf of the translation subtree. -/
theorem translateAlgEquiv_ne_one (h₂ : W.Equation x₂ y₂) : translateAlgEquiv h₂ ≠ 1 := by
  intro hone
  have hx : translateEndo h₂ (genX W) = genX W := by
    rw [← translateAlgEquiv_apply h₂, hone]; rfl
  have hy : translateEndo h₂ (genY W) = genY W := by
    rw [← translateAlgEquiv_apply h₂, hone]; rfl
  have hfix : genericPoint + translatePoint h₂ = (genericPoint : (W.map
      (algebraMap F W.FunctionField)).Point) := by
    rw [genericPoint_add_translatePoint h₂, genericPoint]
    simp only [Point.some.injEq]
    exact ⟨hx, hy⟩
  have hzero : translatePoint h₂ = 0 := by
    have h := congrArg (fun p => -genericPoint + p) hfix
    simpa [← add_assoc] using h
  rw [translatePoint_eq_some h₂] at hzero
  exact Point.some_ne_zero _ hzero

/-- **`Aut_F F(W)` is nontrivial** as soon as `W` has an affine `F`-point: translation by that point
is an automorphism different from the identity. -/
theorem nontrivial_algEquiv_of_equation (h₂ : W.Equation x₂ y₂) :
    Nontrivial (W.FunctionField ≃ₐ[F] W.FunctionField) :=
  ⟨⟨translateAlgEquiv h₂, 1, translateAlgEquiv_ne_one h₂⟩⟩

end CoordinateRing
end WeierstrassCurve.Affine
