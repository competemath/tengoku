/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.RiemannRoch.General
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Core.GradedBasis
import Tengoku.Seed.RingTheory.AdjoinRoot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The intersection ring of a Picard-rank-one surface

Every smooth projective surface with `Pic X = ℤ·H` has the same numerical intersection ring
up to the one number `∫_X H²`: it is `ℚ[t]/(t³)` with `t = H`, graded by codimension, and
the degree map is pinned by where it sends `H²`.

So the ring, its grading, the Chern character in the basis `1, H, H²`, and the degree map on
the normal form are all shared. What distinguishes one surface from another is only the
**Todd class**, and that is what the individual model files supply:

* `Models/Surface/K3.lean` — `td = 1 + 0 + (1/d)H²` on a K3 of degree `H² = 2d`;
* `Models/Surface/ProjectivePlane.lean` — `td = 1 + (3/2)H + H²` on `ℙ²`, where `H² = 1`;
* `Models/Surface/Abelian.lean` — `td = 1 + 0 + 0` on an abelian surface.

The degree is parametrised by `h2 = ∫_X H²` rather than by a surface, so a new
Picard-rank-one model costs a Todd class and nothing else.

`Models/MonogenicRing.lean` performs this same construction in arbitrary dimension, and the
threefold and fourfold models are built on it. This file is not rebuilt on top of that one:
see the implementation notes there for why.
-/

open Polynomial Submodule Set
open DerivedAlgGeo.LinearAlgebra

namespace AlgebraicGeometry.Numerical

namespace Examples

/-! ### The ring `ℚ[t]/(t³)` -/

/-- The defining relation: nothing survives in codimension three on a surface.-/
noncomputable def surfaceRel : ℚ[X] := X ^ 3

/--
@isnad1 id=ne.0h0v.s4.a7a3a575a9a3 from=translated src=- shape=2d527563 vocab=c868f154
-/
theorem surfaceRel_ne_zero : surfaceRel ≠ 0 :=
  pow_ne_zero 3 Polynomial.X_ne_zero

/-- The numerical intersection ring `A^•(X)_ℚ = ℚ[t]/(t³)`.-/
abbrev SurfaceRing : Type := AdjoinRoot surfaceRel

/-- The power basis `1, H, H²`.-/
noncomputable def surfacePB : PowerBasis ℚ SurfaceRing := AdjoinRoot.powerBasis surfaceRel_ne_zero

/--
@isnad1 id=eq.0h0v.s4.593661286240 from=translated src=- shape=34bef2d9 vocab=eb40de43
-/
theorem surfacePB_dim : surfacePB.dim = 3 := by
  rw [surfacePB, AdjoinRoot.powerBasis_dim, surfaceRel, Polynomial.natDegree_X_pow]

/-- The ample generator of the Picard group.-/
noncomputable def H : SurfaceRing := AdjoinRoot.root surfaceRel

/--
@isnad1 id=eq.0h0v.s4.b95b04a7c591 from=translated src=- shape=72f55bc8 vocab=85382b8c
-/
theorem surfacePB_gen : surfacePB.gen = H := AdjoinRoot.powerBasis_gen _

/--
@isnad1 id=eq.0h1v.s8.94cd574faaba from=translated src=- shape=b4782f86 vocab=5666ab1d
-/
theorem surfacePB_basis_apply (i : Fin surfacePB.dim) : surfacePB.basis i = H ^ (i : ℕ) := by
  rw [surfacePB.basis_eq_pow, surfacePB_gen]

/-- The codimension of `Hⁱ` is `i`.-/
def surfaceW : Fin surfacePB.dim → ℕ := fun i => (i : ℕ)

-- `surfacePB.dim` cannot be rewritten inside a hypothesis mentioning `i : Fin surfacePB.dim`
-- — the motive does not typecheck. Feed the equation to `omega` as a fact about naturals.
/--
@isnad1 id=le.0h1v.s5.d349610af5b0 from=translated src=- shape=093ec9e5 vocab=38e38241
-/
theorem surfaceW_le (i : Fin surfacePB.dim) : surfaceW i ≤ 2 := by
  have h := i.isLt
  have hd := surfacePB_dim
  show (i : ℕ) ≤ 2
  omega

/--
@isnad1 id=lt.0h0v.s5.977676deeb05 from=translated src=- shape=1a49f3df vocab=18c50880
-/
theorem two_lt_dim : (2 : ℕ) < surfacePB.dim := by rw [surfacePB_dim]; norm_num

/-- The index of `H²`, the top graded piece.-/
def idx2 : Fin surfacePB.dim := ⟨2, two_lt_dim⟩

/--
@isnad1 id=mem.0h0v.s8.4cf12d01a302 from=translated src=- shape=94be6a0b vocab=dc3a7e90
-/
theorem surface_one_mem : (1 : SurfaceRing) ∈ gradedPiece (⇑surfacePB.basis) surfaceW 0 := by
  have h0 : (0 : ℕ) < surfacePB.dim := by rw [surfacePB_dim]; norm_num
  have hb : surfacePB.basis ⟨0, h0⟩ = 1 := by rw [surfacePB_basis_apply]; simp
  have hmem := mem_gradedPiece (b := ⇑surfacePB.basis) (w := surfaceW) ⟨0, h0⟩
  rwa [hb] at hmem

/--
@isnad1 id=mem.0h0v.s8.4ab75f7459e5 from=translated src=- shape=000e8283 vocab=a27d1631
-/
theorem H_mem_piece_one : H ∈ gradedPiece (⇑surfacePB.basis) surfaceW 1 := by
  have h1 : (1 : ℕ) < surfacePB.dim := by rw [surfacePB_dim]; norm_num
  have hb : surfacePB.basis ⟨1, h1⟩ = H := by rw [surfacePB_basis_apply]; simp
  have hmem := mem_gradedPiece (b := ⇑surfacePB.basis) (w := surfaceW) ⟨1, h1⟩
  rwa [hb] at hmem

/--
@isnad1 id=mem.0h0v.s8.3c333faf9db5 from=translated src=- shape=fc8ef6b5 vocab=66f13a6d
-/
theorem Hsq_mem_piece_two : H ^ 2 ∈ gradedPiece (⇑surfacePB.basis) surfaceW 2 := by
  have hb : surfacePB.basis idx2 = H ^ 2 := by rw [surfacePB_basis_apply]; rfl
  have hmem := mem_gradedPiece (b := ⇑surfacePB.basis) (w := surfaceW) idx2
  rwa [hb] at hmem

/--
@isnad1 id=mem.1h3v.s9.f082d7fea560 from=translated src=- shape=96d1bad4 vocab=9e608269
-/
theorem algebraMap_mul_mem {i : ℕ} {x : SurfaceRing} (q : ℚ)
    (hx : x ∈ gradedPiece (⇑surfacePB.basis) surfaceW i) :
    algebraMap ℚ SurfaceRing q * x ∈ gradedPiece (⇑surfacePB.basis) surfaceW i := by
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hx

/-! ### The degree map, pinned by `∫_X H² = h2` -/

/-- `∫_X`, normalised so that `∫_X H² = h2`.-/
noncomputable def surfaceDegree (h2 : ℚ) : SurfaceRing →ₗ[ℚ] ℚ := h2 • surfacePB.basis.coord idx2

-- `simp` is the wrong tool here: `PowerBasis.coe_basis` fires first and turns `basis i` into
-- `gen ^ i`, after which `Basis.repr_self` no longer matches. Rewrite by hand.
/--
@isnad1 id=eq.1h2v.s8.35d2b514ef49 from=translated src=- shape=a0b0e63d vocab=db931241
-/
theorem surfaceDegree_basis_of_ne (h2 : ℚ) (i : Fin surfacePB.dim) (hi : surfaceW i ≠ 2) :
    surfaceDegree h2 (surfacePB.basis i) = 0 := by
  have hne : i ≠ idx2 := fun h => hi (by rw [h]; rfl)
  show (h2 • surfacePB.basis.coord idx2) (surfacePB.basis i) = 0
  rw [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
  simp [hne]

/--
@isnad1 id=eq.0h1v.s8.f2a9ed6ef7c5 from=translated src=- shape=71db0efa vocab=cd470b18
-/
theorem surfaceDegree_basis_two (h2 : ℚ) : surfaceDegree h2 (surfacePB.basis idx2) = h2 := by
  show (h2 • surfacePB.basis.coord idx2) (surfacePB.basis idx2) = h2
  rw [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
  simp

/--
@isnad1 id=eq.0h1v.s6.e22819c28120 from=translated src=- shape=a4442736 vocab=d07bcfd1
-/
theorem surfaceDegree_one (h2 : ℚ) : surfaceDegree h2 1 = 0 := by
  have h0 : (0 : ℕ) < surfacePB.dim := by rw [surfacePB_dim]; norm_num
  have hb : surfacePB.basis ⟨0, h0⟩ = 1 := by rw [surfacePB_basis_apply]; simp
  rw [← hb]
  exact surfaceDegree_basis_of_ne h2 _ (by show (0 : ℕ) ≠ 2; decide)

/--
@isnad1 id=eq.0h1v.s6.0fade46fa637 from=translated src=- shape=bc4912a8 vocab=24e2afc7
-/
theorem surfaceDegree_H (h2 : ℚ) : surfaceDegree h2 H = 0 := by
  have h1 : (1 : ℕ) < surfacePB.dim := by rw [surfacePB_dim]; norm_num
  have hb : surfacePB.basis ⟨1, h1⟩ = H := by rw [surfacePB_basis_apply]; simp
  rw [← hb]
  exact surfaceDegree_basis_of_ne h2 _ (by show (1 : ℕ) ≠ 2; decide)

/-- `∫_X H² = h2`: the degree of the surface.
@isnad1 id=eq.0h1v.s7.3cf2d77f76ad from=translated src=- shape=50cca3e0 vocab=aa581a90
-/
theorem surfaceDegree_Hsq (h2 : ℚ) : surfaceDegree h2 (H ^ 2) = h2 := by
  have hb : surfacePB.basis idx2 = H ^ 2 := by rw [surfacePB_basis_apply]; rfl
  rw [← hb]
  exact surfaceDegree_basis_two h2

/--
@isnad1 id=eq.0h3v.s8.560569cd17ef from=translated src=- shape=6442cfbd vocab=5f0c19ad
-/
theorem surfaceDegree_algebraMap_mul (h2 q : ℚ) (x : SurfaceRing) :
    surfaceDegree h2 (algebraMap ℚ SurfaceRing q * x) = q * surfaceDegree h2 x := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- `∫_X` on the normal form `a + b·H + c·H²`. Only the top coefficient survives.
@isnad1 id=eq.0h4v.s8.7705b55bf14f from=translated src=- shape=0cd54388 vocab=98288741
-/
theorem surfaceDegree_normalForm (h2 a b c : ℚ) :
    surfaceDegree h2 (algebraMap ℚ SurfaceRing a + algebraMap ℚ SurfaceRing b * H
      + algebraMap ℚ SurfaceRing c * H ^ 2) = h2 * c := by
  rw [map_add, map_add, surfaceDegree_algebraMap_mul, surfaceDegree_algebraMap_mul,
    surfaceDegree_H, surfaceDegree_Hsq, mul_zero, add_zero]
  rw [show algebraMap ℚ SurfaceRing a = algebraMap ℚ SurfaceRing a * 1 by rw [mul_one],
    surfaceDegree_algebraMap_mul, surfaceDegree_one, mul_zero, zero_add]
  ring

/-! ### The Chern character

All three models use the same `N`. `K3.lean` and `Abelian.lean` share `k3ChCoeff`;
`ProjectivePlane.lean` reparametrises with its own `p2ChCoeff`, because `ch₂` is a
half-integer on `ℙ²` — see `Models/Surface/ProjectivePlane.lean`. Coefficients are
therefore rational rather than integral. -/

/-- A class is recorded by the three rational coefficients of `ch = a + b·H + c·H²`.-/
abbrev SurfaceNum : Type := Fin 3 → ℤ

/-- Shared Chern-character coordinates for the rank-one surface models: the
class `(r, c, s)` has `ch = r + c·H + s·H²`.

The historical name is retained even though the construction is not K3-specific.-/
noncomputable def k3ChCoeff (E : SurfaceNum) : ℕ → ℚ
  | 0 => (E 0 : ℚ)
  | 1 => (E 1 : ℚ)
  | 2 => (E 2 : ℚ)
  | _ + 3 => 0

/--
@isnad1 id=eq.0h3v.s5.d53b91564e64 from=translated src=- shape=897af36f vocab=9dc42bcc
-/
theorem k3ChCoeff_add (E F : SurfaceNum) (i : ℕ) :
    k3ChCoeff (E + F) i = k3ChCoeff E i + k3ChCoeff F i := by
  match i with
  | 0 | 1 => simp only [k3ChCoeff, Pi.add_apply, Int.cast_add]
  | 2 => simp only [k3ChCoeff, Pi.add_apply, Int.cast_add]
  | _ + 3 => simp only [k3ChCoeff, add_zero]

/-- The Chern character of `E`, given its coefficient functions. `chCoeff E i` is the
coefficient of `Hⁱ`; keeping it abstract lets `ℙ²` use half-integers.-/
noncomputable def surfaceCh (chCoeff : SurfaceNum → ℕ → ℚ) (E : SurfaceNum) : ℕ → SurfaceRing
  | 0 => algebraMap ℚ SurfaceRing (chCoeff E 0)
  | 1 => algebraMap ℚ SurfaceRing (chCoeff E 1) * H
  | 2 => algebraMap ℚ SurfaceRing (chCoeff E 2) * H ^ 2
  | _ + 3 => 0

/--
@isnad1 id=mem.0h3v.s8.f0babfa6f988 from=translated src=- shape=d6450398 vocab=4cc15b84
-/
theorem surfaceCh_mem (chCoeff : SurfaceNum → ℕ → ℚ) (E : SurfaceNum) (i : ℕ) :
    surfaceCh chCoeff E i ∈ gradedPiece (⇑surfacePB.basis) surfaceW i := by
  match i with
  | 0 =>
    show algebraMap ℚ SurfaceRing (chCoeff E 0) ∈ _
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ surface_one_mem
  | 1 => exact algebraMap_mul_mem _ H_mem_piece_one
  | 2 => exact algebraMap_mul_mem _ Hsq_mem_piece_two
  | _ + 3 => exact Submodule.zero_mem _

/--
@isnad1 id=eq.1h4v.s7.8528b06aaba9 from=translated src=- shape=b7137fa3 vocab=e1c904cb
-/
theorem surfaceCh_add (chCoeff : SurfaceNum → ℕ → ℚ)
    (hadd : ∀ E F i, chCoeff (E + F) i = chCoeff E i + chCoeff F i)
    (E F : SurfaceNum) (i : ℕ) :
    surfaceCh chCoeff (E + F) i = surfaceCh chCoeff E i + surfaceCh chCoeff F i := by
  match i with
  | 0 =>
    show algebraMap ℚ SurfaceRing (chCoeff (E + F) 0) = _
    rw [hadd, map_add]
    rfl
  | 1 =>
    show algebraMap ℚ SurfaceRing (chCoeff (E + F) 1) * H = _
    rw [hadd, map_add, add_mul]
    rfl
  | 2 =>
    show algebraMap ℚ SurfaceRing (chCoeff (E + F) 2) * H ^ 2 = _
    rw [hadd, map_add, add_mul]
    rfl
  | _ + 3 => show (0 : SurfaceRing) = 0 + 0; rw [add_zero]

/--
@isnad1 id=eq.0h2v.s8.13bed1706773 from=translated src=- shape=cbc41ad6 vocab=fea68605
-/
theorem surfaceCh_sum (chCoeff : SurfaceNum → ℕ → ℚ) (E : SurfaceNum) :
    (∑ i ∈ Finset.range (2 + 1), surfaceCh chCoeff E i)
      = algebraMap ℚ SurfaceRing (chCoeff E 0) + algebraMap ℚ SurfaceRing (chCoeff E 1) * H
        + algebraMap ℚ SurfaceRing (chCoeff E 2) * H ^ 2 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  rfl

end Examples

end AlgebraicGeometry.Numerical
