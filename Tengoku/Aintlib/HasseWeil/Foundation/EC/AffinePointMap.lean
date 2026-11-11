import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Functorial action of ring homs on `Affine.Point` (T-III-4-020b-2, Phase 0a)

For an injective ring homomorphism `f : R →+* S` and a Weierstrass curve `W`
over `R`, we build the natural map
`Affine.Point.map f : W.toAffine.Point → (W.map f).toAffine.Point`
which sends `zero` to `zero` and `some x y h` to `some (f x) (f y) _`.

mathlib provides `map_nonsingular` (`Affine/Basic.lean:278`) which shows that
nonsingularity of `(x, y)` transfers to nonsingularity of `(f x, f y)` on
`W.map f` under an injective `f`. We package this into the functorial
`Point.map`.

## Main definition

* `HasseWeil.Affine.Point.map` — the map `W.Point → (W.map f).Point` for an
  injective ring homomorphism `f : R →+* S`.

This is Phase 0a of T-III-4-020b-2. Phases 0b (`map_add`) and 0c (`map_zsmul`)
build the group-hom properties on top.

## References

* mathlib: `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`
* Silverman, *The Arithmetic of Elliptic Curves*, III.4 (group law).
-/

open WeierstrassCurve

namespace HasseWeil.Affine.Point

variable {R S : Type*} [CommRing R] [CommRing S] {W : WeierstrassCurve R}
    (f : R →+* S) (hf : Function.Injective f)

/-- The natural map `W.toAffine.Point → (W.map f).toAffine.Point` induced by
    an injective ring homomorphism `f : R →+* S`. It sends `zero` to `zero`
    and `some x y h` to `some (f x) (f y) _`, using that nonsingularity
    transfers under an injective ring hom (mathlib's `map_nonsingular`).-/
noncomputable def map : W.toAffine.Point → (W.map f).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (f x) (f y) ((Affine.map_nonsingular W.toAffine hf x y).mpr h)

/--
@isnad1 id=eq.1h4v.s6.b2fe4c54481c from=translated src=- shape=56bf8c12 vocab=526f0e4b
-/
@[simp] theorem map_zero : map f hf (.zero : W.toAffine.Point) = .zero := rfl

/--
@isnad1 id=eq.2h6v.s7.2c827c798382 from=translated src=- shape=9983f42d vocab=3541eb48
-/
@[simp] theorem map_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    map f hf (.some x y h) =
      .some (f x) (f y) ((Affine.map_nonsingular W.toAffine hf x y).mpr h) :=
  rfl

end HasseWeil.Affine.Point

/-! ### Phase 0b: `Affine.Point.map` is additive

Here we restrict to ring homs between fields, since `Affine.Point` only has
`Add` over a field. Using mathlib's equivariance lemmas
(`Affine.map_negY`, `map_addX`, `map_addY`, `map_slope`) the case analysis
of `Point.add` goes through mechanically. -/

namespace HasseWeil.Affine.Point

variable {F F' : Type*} [Field F] [Field F'] [DecidableEq F] [DecidableEq F']
    {W : WeierstrassCurve F} (f : F →+* F')

/-- `Point.map f` is additive on points over a field: it commutes with the
    group law. Case analysis on mathlib's `Point.add`:
    * `(0, P)`, `(P, 0)` : trivial via `map_zero`.
    * `some + some` with Y-cancellation : both sides are `0` (preserved under `f`).
    * `some + some` without Y-cancellation : both sides are `some (addX ...) (addY ...)`,
      and `f` commutes with `addX`, `addY`, `slope`, `negY` (mathlib equivariance).
@isnad1 id=eq.0h6v.s7.40c0dc62a43b from=translated src=- shape=25d5384c vocab=cfe581b1
-/
theorem map_add (P Q : W.toAffine.Point) :
    map f f.injective (P + Q) = map f f.injective P + map f f.injective Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · obtain ⟨hx, hy⟩ := hxy
    have h_Y_eq_f : f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂) := by
      rw [hy, Affine.map_negY]
    rw [Affine.Point.add_of_Y_eq hx hy, map_some, map_some,
      Affine.Point.add_of_Y_eq (congr_arg f hx) h_Y_eq_f]
    exact map_zero f f.injective
  · have hxy_f : ¬(f x₁ = f x₂ ∧ f y₁ = (W.map f).toAffine.negY (f x₂) (f y₂)) := by
      rintro ⟨hfx, hfy⟩
      exact hxy ⟨f.injective hfx, f.injective (by rw [hfy, Affine.map_negY])⟩
    rw [Affine.Point.add_some hxy, map_some, map_some, map_some,
      Affine.Point.add_some hxy_f]
    congr 1
    · rw [Affine.map_slope, Affine.map_addX]
    · rw [Affine.map_slope, Affine.map_addY]

/-- `Point.map f` preserves negation: `-map f P = map f (-P)`.
@isnad1 id=eq.0h5v.s7.19e4f65c5194 from=translated src=- shape=b016db65 vocab=b68dfed2
-/
theorem map_neg (P : W.toAffine.Point) :
    -map f f.injective P = map f f.injective (-P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [map_some, Affine.Point.neg_some, Affine.Point.neg_some, map_some]
    congr 1
    exact Affine.map_negY f x y

/-- `Point.map f` packaged as an `AddMonoidHom`. Uses `map_add` and `map_zero`
    to witness the additive structure.-/
noncomputable def mapAddMonoidHom :
    W.toAffine.Point →+ (W.map f).toAffine.Point where
  toFun := map f f.injective
  map_zero' := map_zero f f.injective
  map_add' := map_add f

/-- `Point.map f` commutes with integer scalar multiplication. Direct from
    `AddMonoidHom.map_zsmul` since `mapAddMonoidHom` is an `AddMonoidHom`.
@isnad1 id=eq.0h6v.s8.217e320dc66b from=translated src=- shape=15d8daa5 vocab=47b29271
-/
theorem map_zsmul (n : ℤ) (P : W.toAffine.Point) :
    map f f.injective (n • P) = n • map f f.injective P :=
  (mapAddMonoidHom f).map_zsmul n P

end HasseWeil.Affine.Point
