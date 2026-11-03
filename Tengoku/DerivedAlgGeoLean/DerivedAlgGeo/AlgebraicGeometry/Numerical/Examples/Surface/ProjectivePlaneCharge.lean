/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Models.Surface.ProjectivePlane
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.CentralCharge.Divisorial.Charge
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.DivisorialChargeNumerical
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.StabilityCondition.Walls.Divisorial.Slice
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.AlgebraicGeometry.Numerical.Stability.SurfaceChargeNumerical
import Tengoku.Seed.Data.Fin.VecNotation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The projective-plane child of the divisorial surface charge

This file instantiates the intrinsic divisorial surface construction for
`ℙ²`.  Its divisor space is one-dimensional, with the hyperplane class `H`
normalized by `H² = 1`.  Two class carriers carry a full
`ChernCharacter`: a placeholder integral triple `(r, c, v)` and the
existing `SurfaceNum` presentation.  Their comparison is made before choosing
`B` and `omega`.

## What is, and is not, compared here

The two carriers have identical coordinates: on both, `ch₂ = c/2 + v`, and
the comparison map `p2ProjectiveToSurface` is the identity on coordinates.
The theorem `p2ProjectiveCharge_eq_surfaceCharge` is therefore an instance of
`ChernCharacter.Pullback.centralCharge_eq` applied to an identity witness; it
is **not** a comparison between Li's image lattice `Λ_ι` and the surface
lattice, because nothing in this file is `Λ_ι` or `v_ι`.  The mathematical
content is the identity `-∫ exp(-(b + i a) H) ch = Z_{aH, bH}`, which is
`ChargeCoordinates.centralCharge_twistByScalar_apply` and holds on
every polarised surface; `p2ProjectiveCharge_apply` records it in the
`(r, c, v)` coordinates.  The only `ℙ²`-specific input is `H² = 1`, which makes
the compressed degree `H · ch₁` equal to the full first Chern class.

The exponential presentation is the projective-space charge of the
projective-family construction for the identity embedding `ℙ² ⊂ ℙ²`, the one
case in which no Todd correction appears (arXiv:2607.28411v1, (5.5) and
Remark 6.3).  For any other embedding the pulled-back charge is not of this
form until the GRR/Todd term has been computed.

The older scalar `ChargeCoordinates` objects are derived compatibility
views.  Thus the projective-plane charge is a child of the same parent as the
smooth-quadric charge, rather than a parent or a separate charge polynomial.

The adapter is only arithmetic.  It does not claim that either carrier is
`K₀(ℙ²)` or `Λ_ι`, does not compare stability conditions, hearts, or slicings,
and does not provide the geometric family map or the C1/C2 properties needed
by the eventual stability comparison.
-/

open Complex
open CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.Divisorial

namespace AlgebraicGeometry.Numerical

namespace Examples

noncomputable section

/-! ### The projective-plane divisor space -/

/-- Real numerical divisor classes on `ℙ²`, represented in the hyperplane
basis.-/
abbrev P2Divisor : Type := ℝ

/-- The intersection form in the normalized hyperplane basis.-/
def p2IntersectionForm : LinearMap.BilinForm ℝ P2Divisor :=
  LinearMap.mk₂ ℝ (fun x y => x * y)
    (fun _ _ _ => by ring)
    (fun _ _ _ => by ring)
    (fun _ _ _ => by ring)
    (fun _ _ _ => by ring)

/-- The rank-one numerical divisor space of `ℙ²`.-/
def p2DivisorSpace : DivisorSpace P2Divisor where
  intersection := p2IntersectionForm
  intersection_symm := ⟨by intro x y; simp [p2IntersectionForm]; ring⟩

/-- The hyperplane generator in the one-dimensional divisor space.-/
def p2Hyperplane : P2Divisor := 1

/--
@isnad1 id=eq.0h0v.s4.48d0020bfabe from=translated src=- shape=5114bbf8 vocab=ad43b4df
-/
@[simp]
theorem p2Hyperplane_square :
    p2DivisorSpace.pair p2Hyperplane p2Hyperplane = 1 := by
  norm_num [DivisorSpace.pair, p2DivisorSpace, p2IntersectionForm,
    p2Hyperplane]

/-! ### The two full Chern-character presentations -/

/-- A placeholder integral `(r, c, v)` carrier for the exponential
presentation of the charge.

It has the same coordinates as `SurfaceNum` (`ch₂ = c/2 + v` on both) and is
a separate Lean type only so that the adapter below carries an explicit
source-to-target map, where a geometric class map can later be substituted.
It is not Li's image lattice `Λ_ι` and carries no information about `K₀(ℙ²)`.-/
abbrev P2ProjectiveCoordinates : Type := ℤ × ℤ × ℤ

/-- The full Chern character on the explicit projective-family coordinates.-/
noncomputable def p2ProjectiveChernCharacter :
    ChernCharacter P2ProjectiveCoordinates P2Divisor where
  rank := AddMonoidHom.mk' (fun E => (E.1 : ℝ)) (by
    intro E F
    change ((E.1 + F.1 : ℤ) : ℝ) = (E.1 : ℝ) + (F.1 : ℝ)
    push_cast
    rfl)
  chOne := AddMonoidHom.mk' (fun E => (E.2.1 : ℝ)) (by
    intro E F
    change ((E.2.1 + F.2.1 : ℤ) : ℝ) = (E.2.1 : ℝ) + (F.2.1 : ℝ)
    push_cast
    rfl)
  chTwo := AddMonoidHom.mk' (fun E => (E.2.1 : ℝ) / 2 + (E.2.2 : ℝ)) (by
    intro E F
    change ((E.2.1 + F.2.1 : ℤ) : ℝ) / 2 + ((E.2.2 + F.2.2 : ℤ) : ℝ) =
      ((E.2.1 : ℝ) / 2 + (E.2.2 : ℝ)) +
        ((F.2.1 : ℝ) / 2 + (F.2.2 : ℝ))
    push_cast
    ring)

/-- The old scalar-coordinate view, derived from the full character at `H`.-/
noncomputable def p2ProjectiveChargeCoordinates :
    ChargeCoordinates P2ProjectiveCoordinates :=
  p2ProjectiveChernCharacter.coordinatesAt p2DivisorSpace p2Hyperplane

/-- The source rank coordinate is the first projective triple entry.
@isnad1 id=eq.0h1v.s6.5380f2c86835 from=translated src=- shape=fb3efedd vocab=f56b03fb
-/
@[simp]
theorem p2ProjectiveChargeCoordinates_rank (E : P2ProjectiveCoordinates) :
    p2ProjectiveChargeCoordinates.rank E = (E.1 : ℝ) := by
  rfl

/-- The source degree coordinate is the second projective triple entry.
@isnad1 id=eq.0h1v.s6.fdf2b595599f from=translated src=- shape=05fc77f1 vocab=5ed4f583
-/
@[simp]
theorem p2ProjectiveChargeCoordinates_degree (E : P2ProjectiveCoordinates) :
    p2ProjectiveChargeCoordinates.degree E = (E.2.1 : ℝ) := by
  simp [p2ProjectiveChargeCoordinates, p2ProjectiveChernCharacter,
    p2DivisorSpace, p2IntersectionForm, p2Hyperplane, DivisorSpace.pair]

/-- The source `ch₂` coordinate is `c/2 + v`.
@isnad1 id=eq.0h1v.s7.fce078ded8dd from=translated src=- shape=50089030 vocab=bd241a0c
-/
@[simp]
theorem p2ProjectiveChargeCoordinates_chTwo (E : P2ProjectiveCoordinates) :
    p2ProjectiveChargeCoordinates.chTwo E = (E.2.1 : ℝ) / 2 + (E.2.2 : ℝ) := by
  rfl

/-- The projective-plane source uses the normalization `H² = 1`.
@isnad1 id=eq.0h0v.s4.5a3db338c501 from=translated src=- shape=b3c4969c vocab=984a1945
-/
@[simp]
theorem p2ProjectiveChargeCoordinates_hyperplaneSquare :
    p2ProjectiveChargeCoordinates.hyperplaneSquare = 1 := by
  exact p2Hyperplane_square

/-! ### Real realization of the rational divisor piece -/

/-- The unique basis index of codimension one in the rank-one surface ring.-/
def p2DivisorIndex : Fin surfacePB.dim :=
  ⟨1, by rw [surfacePB_dim]; norm_num⟩

/-- The weight-one basis vectors are exactly the singleton `H`.
@isnad1 id=eq.0h0v.s8.0c3c5ebdb30c from=translated src=- shape=16ad7de9 vocab=1236c7ad
-/
theorem surfaceWeightOneBasis :
    surfacePB.basis '' (surfaceW ⁻¹' ({1} : Set ℕ)) = ({H} : Set SurfaceRing) := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hi
    have hindex : i = p2DivisorIndex := Fin.ext hi
    rw [hindex, surfacePB_basis_apply]
    simp [p2DivisorIndex]
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    refine ⟨p2DivisorIndex, ?_, ?_⟩
    · simp [surfaceW, p2DivisorIndex]
    · rw [surfacePB_basis_apply]
      simp [p2DivisorIndex]

/-! ### The explicit numerical comparison map -/

/-- The source-to-target additive map sending `(r, c, v)` to `![r, c, v]`.-/
def p2ProjectiveToSurface : P2ProjectiveCoordinates →+ SurfaceNum :=
  AddMonoidHom.mk'
    (fun E => ![E.1, E.2.1, E.2.2])
    (by
      intro E F
      funext i
      fin_cases i <;> rfl)

/-! ### The two presentations of the same charge -/

/-- The projective-plane rank-one family `B = bH`, `omega = aH`, obtained as
a specialization of the parent parameter space.-/
def p2Parameters (a b : ℝ) : StabilityParameters P2Divisor :=
  StabilityParameters.rankOne p2Hyperplane a b

/-- The divisorial parent charge on the placeholder `(r, c, v)` carrier at
`B = bH`, `omega = aH`.  Its expansion `p2ProjectiveCharge_apply` is the
projective-space exponential `-∫ exp(-(b + i a) H) ch`; the carrier is not
Li's image lattice.-/
noncomputable def p2ProjectiveCharge (a b : ℝ) :
    P2ProjectiveCoordinates →+ ℂ :=
  p2ProjectiveChernCharacter.centralCharge p2DivisorSpace (p2Parameters a b)

/-! ### The inherited rank-one wall slice -/

/-- The projective-plane wall slice has no transverse directions.-/
def p2WallSlice :
    OrthogonalSlice p2DivisorSpace (Fin 0 → ℝ) :=
  OrthogonalSlice.rankOne p2DivisorSpace p2Hyperplane

/-- The projective-coordinate charge as a child of the generic wall-family
and orthogonal-slice layers.-/
def p2ProjectiveWallFamily :
    CategoryTheory.Triangulated.WeakStabilityCondition.StabilityCondition.Wall.ChargeFamily
      (OrthogonalSlice.Point (Fin 0 → ℝ)) P2ProjectiveCoordinates :=
  p2WallSlice.chargeFamily p2ProjectiveChernCharacter

/-- Evaluating the inherited rank-one family recovers the existing
projective-plane charge.
@isnad1 id=eq.0h3v.s7.216c0bc59a85 from=translated src=- shape=4ccaf5e6 vocab=6748090e
-/
@[simp]
theorem p2ProjectiveWallFamily_charge (a b : ℝ)
    (E : P2ProjectiveCoordinates) :
    p2ProjectiveWallFamily.charge
        (OrthogonalSlice.Point.rankOne b a) E =
      p2ProjectiveCharge a b E := by
  rw [p2ProjectiveCharge]
  have hparameters :
      p2WallSlice.parameters (OrthogonalSlice.Point.rankOne b a) =
        p2Parameters a b := by
    apply congrArg₂ StabilityParameters.mk
    · change b • p2Hyperplane + 0 = b • p2Hyperplane
      simp
    · rfl
  change p2ProjectiveChernCharacter.centralCharge p2DivisorSpace
      (p2WallSlice.parameters (OrthogonalSlice.Point.rankOne b a)) E = _
  rw [hparameters]

/-- The projective charge respects the additive zero class.
@isnad1 id=eq.0h2v.s6.9fca053be4d1 from=translated src=- shape=93543ccd vocab=c736927d
-/
theorem p2ProjectiveCharge_zero (a b : ℝ) :
    p2ProjectiveCharge a b 0 = 0 :=
  (p2ProjectiveCharge a b).map_zero

/-- The projective-space exponential `-∫ exp(-(b + i a) H) ch` in the
`(r, c, v)` coordinates: the surface charge at `B = bH`, `omega = aH` equals the
exponential presentation with `H² = 1`.
@isnad1 id=eq.0h3v.s8.092216abe431 from=translated src=- shape=3d656c31 vocab=5810e654
-/
@[simp]
theorem p2ProjectiveCharge_apply (a b : ℝ) (E : P2ProjectiveCoordinates) :
    p2ProjectiveCharge a b E =
      -Complex.ofReal ((E.2.1 : ℝ) / 2 + (E.2.2 : ℝ))
        + (b + a * Complex.I) * Complex.ofReal (E.2.1 : ℝ)
        - (b + a * Complex.I) ^ 2 * Complex.ofReal ((E.1 : ℝ) / 2) := by
  calc
    p2ProjectiveCharge a b E =
        (p2ProjectiveChargeCoordinates.twistByScalar b).centralCharge a E := by
      simpa [p2ProjectiveCharge, p2Parameters, p2ProjectiveChargeCoordinates] using
        (ChernCharacter.centralCharge_rankOne_eq p2ProjectiveChernCharacter
          p2DivisorSpace p2Hyperplane a b E)
    _ = _ := by
      rw [ChargeCoordinates.centralCharge_twistByScalar_apply]
      simp

/-! ### Coordinate formulas -/

/-- The real part of the projective-plane charge in `(r, c, v)` coordinates.
@isnad1 id=eq.0h3v.s7.6039580ec072 from=translated src=- shape=f7d64b6d vocab=ed9d608f
-/
theorem p2ProjectiveCharge_re (a b : ℝ) (E : P2ProjectiveCoordinates) :
    (p2ProjectiveCharge a b E).re =
      -((E.2.1 : ℝ) / 2 + (E.2.2 : ℝ))
        + b * (E.2.1 : ℝ)
        + (a ^ 2 - b ^ 2) * ((E.1 : ℝ) / 2) := by
  rw [p2ProjectiveCharge_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, pow_two]
  ring

/-- The imaginary part of the projective-plane charge in `(r, c, v)` coordinates.
@isnad1 id=eq.0h3v.s7.9c3804c2baaa from=translated src=- shape=ac863e39 vocab=a9d9de61
-/
theorem p2ProjectiveCharge_im (a b : ℝ) (E : P2ProjectiveCoordinates) :
    (p2ProjectiveCharge a b E).im =
      a * (E.2.1 : ℝ) - (2 * a * b) * ((E.1 : ℝ) / 2) := by
  rw [p2ProjectiveCharge_apply]
  simp only [Complex.sub_im, Complex.add_im, Complex.neg_im,
    Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, pow_two]
  ring

end

end Examples

end AlgebraicGeometry.Numerical
