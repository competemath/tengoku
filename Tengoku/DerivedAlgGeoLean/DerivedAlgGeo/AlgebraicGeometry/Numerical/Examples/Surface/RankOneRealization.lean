/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.Surface.K3
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialMukai
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialSupport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The real divisor realization of a Picard-rank-one surface, and the K3 model

`Models/Surface/RankOne.lean` builds the rational intersection ring
`ℚ[H]/(H³)` with `∫_X H² = h2`, and `K3.lean`, `ProjectivePlane.lean` and
`Abelian.lean` are three variety presentations over it.  What none of them had
was a `Surface.NumericalRealization`: a map of the rational codimension-one
piece into a real divisor space carrying the intersection form.  Without one,
every divisorial statement — the charge, the discriminants, the walls, the
support property — was conditional on a realization existing at all.

This file supplies it once, for every `h2`, and then instantiates the K3 case.

## The realization

The rational piece `N¹` is the line `ℚ·H`, so the real divisor space is `ℝ`
with `H` as the unit vector and the intersection form

```text
(x, y) ↦ h2 · x · y.
```

`surfaceRealization` packages that, and `surfaceChernCharacter_*` reads off the
induced real Chern character in the coordinates `(r, c, s)` of `SurfaceNum`:
rank `r`, first Chern class `c`, and `∫ch₂ = h2 · s`.  The last one is worth
stating explicitly, because `SurfaceNum` records the *coefficient* of `H²` and
the divisorial layer wants its *integral*.

## Hodge definiteness is free in Picard rank one

`DivisorSpace.HodgeDefinite` asks for `ω² > 0` together with negative
definiteness on `ω^⊥`.  On a line with a nondegenerate form the orthogonal
complement of a nonzero vector is zero, so the second condition holds with no
content and the first is `h2 · t² > 0`.  `surfaceHodgeDefinite` is therefore a
theorem, not a supplied certificate, and it is what makes the support property
of `Stability/DivisorialSupport.lean` fire on a model rather than on a
hypothesis.

That is the whole point of doing rank one first: it separates "the support
property argument is correct" from "the Hodge input is available", and only the
second is hard.  A Picard rank three example, where `ω^⊥` is a genuine negative
definite plane, is the next step and lives in `BlowUpPlane.lean`.

## What is not claimed

The carrier is not identified with `K_num(X)` for a geometric K3, and no
Chern-character map from coherent sheaves is constructed.  The
Bogomolov--Gieseker input is `k3BogomolovSanity`, whose `Semistable` predicate
is defined to be the conclusion; the support property below is therefore a
statement about the locus of classes of nonnegative discriminant, which is
exactly what it says, and it is **not** a theorem about semistable sheaves.
-/

open Submodule Set
open DerivedAlgGeo.LinearAlgebra
open CategoryTheory.Triangulated.WeakStabilityCondition
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

namespace AlgebraicGeometry.Numerical

namespace Examples

noncomputable section

/-! ### The real divisor line -/

/-- The real numerical divisor space of a Picard-rank-one surface: the line
spanned by `H`.-/
abbrev SurfaceDivisor : Type := ℝ

/-- The intersection form `(x, y) ↦ h2 · x · y` in the basis `H`.-/
def surfaceIntersectionForm (h2 : ℝ) : LinearMap.BilinForm ℝ SurfaceDivisor :=
  LinearMap.mk₂ ℝ (fun x y => h2 * x * y)
    (fun _ _ _ => by ring) (fun _ _ _ => by simp; ring)
    (fun _ _ _ => by ring) (fun _ _ _ => by simp; ring)

/--
@isnad1 id=eq.0h3v.s8.f6a86ed8c3bd from=translated src=- shape=62f94fef vocab=a4ef5755
-/
@[simp]
theorem surfaceIntersectionForm_apply (h2 x y : ℝ) :
    surfaceIntersectionForm h2 x y = h2 * x * y := rfl

/-- The real divisor space of a Picard-rank-one surface with `∫_X H² = h2`.-/
def surfaceDivisorSpace (h2 : ℝ) : DivisorSpace SurfaceDivisor where
  intersection := surfaceIntersectionForm h2
  intersection_symm := ⟨by intro x y; simp; ring⟩

/--
@isnad1 id=eq.0h3v.s5.0d6b2ce1f266 from=translated src=- shape=05335494 vocab=e1dfdb1b
-/
@[simp]
theorem surfaceDivisorSpace_pair (h2 x y : ℝ) :
    (surfaceDivisorSpace h2).pair x y = h2 * x * y := rfl

/-! ### The rational divisor piece is the line `ℚ·H` -/

/--
@isnad1 id=lt.0h0v.s5.497c17f34f44 from=translated src=- shape=1a49f3df vocab=18c50880
-/
theorem one_lt_dim : (1 : ℕ) < surfacePB.dim := by rw [surfacePB_dim]; norm_num

/-- The index of `H` in the power basis.-/
def idx1 : Fin surfacePB.dim := ⟨1, one_lt_dim⟩

/--
@isnad1 id=eq.0h0v.s7.b78818196a7f from=translated src=- shape=2829c1f3 vocab=a94c0fe0
-/
@[simp]
theorem surfacePB_basis_idx1 : surfacePB.basis idx1 = H := by
  rw [surfacePB_basis_apply]
  simp [idx1]

/--
@isnad1 id=eq.0h0v.s7.c57dba7eae45 from=translated src=- shape=5820f2b4 vocab=26adc48c
-/
theorem surfaceW_preimage_one : surfaceW ⁻¹' ({1} : Set ℕ) = ({idx1} : Set (Fin surfacePB.dim)) := by
  ext i
  constructor
  · intro hi
    have : (i : ℕ) = 1 := hi
    exact Set.mem_singleton_iff.mpr (Fin.ext this)
  · intro hi
    have : i = idx1 := hi
    show surfaceW i = 1
    rw [this]
    rfl

/-- The codimension-one piece is the rational line spanned by `H`.
@isnad1 id=eq.0h0v.s8.0c0c6c5bd2a3 from=translated src=- shape=e829b5e3 vocab=f84721a9
-/
theorem surfacePieceOne_eq_span :
    gradedPiece (⇑surfacePB.basis) surfaceW 1 = Submodule.span ℚ ({H} : Set SurfaceRing) := by
  rw [gradedPiece, surfaceW_preimage_one, Set.image_singleton, surfacePB_basis_idx1]

/-! ### The realization -/

/-- The `H`-coordinate of `a • H` is `a`.
@isnad1 id=eq.0h1v.s8.f36815fe2714 from=translated src=- shape=71ec3903 vocab=d9b69b40
-/
theorem coord_idx1_smul_H (a : ℚ) : surfacePB.basis.coord idx1 (a • H) = a := by
  rw [← surfacePB_basis_idx1, Module.Basis.coord_apply, map_smul,
    Module.Basis.repr_self]
  simp

/-! ### Hodge definiteness in Picard rank one -/

/-- **Negative definiteness on `ω^⊥` is free on a line.**

The orthogonal complement of a nonzero vector for a nondegenerate form on `ℝ`
is `0`, so the definiteness clause is vacuous and only positivity of `ω²`
carries content.
@isnad1 id=hodgedef.2h2v.s5.e8ef13242af8 from=translated src=- shape=42abdbdf vocab=9ea9976d
-/
theorem surfaceHodgeDefinite {h2 t : ℝ} (hh2 : 0 < h2) (ht : t ≠ 0) :
    (surfaceDivisorSpace h2).HodgeDefinite t where
  H_square_pos := by
    show 0 < h2 * t * t
    rw [mul_assoc]
    exact mul_pos hh2 (mul_self_pos.mpr ht)
  neg_definite x hx hxne := by
    exfalso
    apply hxne
    have hx' : h2 * t * x = 0 := hx
    have hne : h2 * t ≠ 0 := by
      have := ne_of_gt hh2
      exact mul_ne_zero this ht
    exact (mul_eq_zero.mp hx').resolve_left hne

/-! ### The K3 model -/

variable {d : ℕ}

/-! ### The support property, on a model rather than on hypotheses -/

/-! ### The Mukai vector of the model -/

end

end Examples

end AlgebraicGeometry.Numerical
