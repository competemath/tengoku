/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Algebra.Polynomial.Laurent.Basic
import Tengoku.Tauceti.TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm
public import Tengoku.Tauceti.TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Basic

/-!
# Reflection matrices for the standard symmetric form

The reflection of `Rⁿ` in the hyperplane orthogonal to a vector `v` has the matrix
`1 - c • vecMulVec v v`, where the scalar `c` satisfies `c * (v ⬝ᵥ v) = 2`. Carrying the scalar
as data rather than as `2 * ⅟(v ⬝ᵥ v)` makes the construction available over any commutative
ring in which the norm of `v` happens to be invertible, makes it visibly natural in the
coefficient ring, and makes the invariance of a reflection under rescaling its vector a
one-line computation: putting `μ²c` on the unscaled-vector side gives the same matrix as
putting `c` on the side whose vector is scaled by `μ`.

Products of two such matrices are exactly the generators of the special orthogonal group
supplied by `TauCeti.closure_reflection_mul_eq_matrixSpecialOrthogonalGroup`, once
`toMatrix'_reflection` identifies the coordinate matrix of the reflection of the standard
quadratic form with `reflectionMatrix`. They are packaged here as `TauCeti.reflectionPair`.

The last and largest section of the file builds one-parameter families joining such a product to
the identity. Over an algebraically closed
field of characteristic different from two, `exists_laurentPath_reflectionMatrix_mul` produces
for every product of two reflections a single special orthogonal matrix over the Laurent
polynomials `K[T;T⁻¹]` together with two units `a` and `b` of `K`, such that specializing the
parameter `T` to `a` gives the identity and specializing it to `b` gives the given product; a
specialization is any `K`-algebra map `K[T;T⁻¹] →ₐ[K] K`, so the units are exactly the
admissible parameter values. The family reflects first in `v` and then in a vector moving
through the plane spanned by `v` and `w`, chosen so that the moving vector has invertible norm
throughout, and the two parameters are those at which the moving vector becomes proportional to
`v`, respectively to `w`. Consuming these families is what proves the special orthogonal group
geometrically connected: an idempotent regular function on the group is constant once right
translation by every rational point fixes it, a point joined to the identity by such a family
fixes every idempotent, and the generation theorem reduces the rational points to be handled to
the products of two reflections.

## Main declarations

* `TauCeti.reflectionMatrix`: the matrix of a reflection, with its normalizing scalar as data.
* `TauCeti.reflectionPair`: the product of two reflections, as a special orthogonal matrix.
* `TauCeti.toMatrix'_reflection`: `reflectionMatrix` is the coordinate matrix of the reflection
  of the standard quadratic form.
* `TauCeti.exists_laurentPath_reflectionMatrix_mul`: over an algebraically closed field of
  characteristic different from two, every product of two reflections is joined to the identity
  by a one-parameter family of special orthogonal matrices over the Laurent polynomials.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §2.
* J. S. Milne, *Algebraic Groups* (2017), §2.3.
-/

public section

namespace TauCeti

open Matrix

universe u v w

variable {n : Type v} [DecidableEq n]
variable {R : Type u} [CommRing R] {S : Type w} [CommRing S]

attribute [local instance] starRingOfComm

/-- The matrix of the reflection of `Rⁿ` in the hyperplane orthogonal to `v`, for a scalar `c`
playing the role of `2 / (v ⬝ᵥ v)`. It is a reflection precisely when `c * (v ⬝ᵥ v) = 2`, which
is not part of the definition. -/
def reflectionMatrix (v : n → R) (c : R) : Matrix n n R := 1 - c • vecMulVec v v

@[simp]
theorem reflectionMatrix_apply (v : n → R) (c : R) (i j : n) :
    reflectionMatrix v c i j = (if i = j then 1 else 0) - c * (v i * v j) := by
  simp [reflectionMatrix, Matrix.one_apply, vecMulVec_apply]

@[simp]
theorem transpose_reflectionMatrix (v : n → R) (c : R) :
    (reflectionMatrix v c)ᵀ = reflectionMatrix v c := by
  simp [reflectionMatrix, Matrix.transpose_sub, Matrix.transpose_smul, transpose_vecMulVec]

/-- Reflection matrices are natural in the coefficient ring. -/
@[simp]
theorem map_reflectionMatrix (f : R →+* S) (v : n → R) (c : R) :
    (reflectionMatrix v c).map f = reflectionMatrix (f ∘ v) (f c) := by
  ext i j
  simp [reflectionMatrix_apply, apply_ite f]

/-- Scaling the vector by `μ` with scalar `c` gives the same matrix as keeping the vector
unchanged and using scalar `μ²c`. -/
theorem reflectionMatrix_smul (v : n → R) (c μ : R) :
    reflectionMatrix (fun i => μ * v i) c = reflectionMatrix v (μ * μ * c) := by
  ext i j
  simp only [reflectionMatrix_apply]
  ring_nf

/-- A reflection matrix is a rank-one perturbation of the identity, so the calculus of
`TauCeti.LinearAlgebra.Matrix.OneSubVecMulVec` applies to it. -/
theorem reflectionMatrix_eq_one_sub_vecMulVec (v : n → R) (c : R) :
    reflectionMatrix v c = 1 - vecMulVec (c • v) v := by
  rw [reflectionMatrix, smul_vecMulVec]

/-- A reflection matrix is an involution. -/
@[simp]
theorem reflectionMatrix_mul_self [Fintype n] {v : n → R} {c : R} (hc : c * (v ⬝ᵥ v) = 2) :
    reflectionMatrix v c * reflectionMatrix v c = 1 := by
  rw [reflectionMatrix_eq_one_sub_vecMulVec,
    one_sub_vecMulVec_mul_self 1 (by rw [dotProduct_smul, smul_eq_mul, hc]; norm_num)]
  module

/-- A reflection matrix is orthogonal. -/
theorem reflectionMatrix_mem_orthogonalGroup [Fintype n] {v : n → R} {c : R}
    (hc : c * (v ⬝ᵥ v) = 2) :
    reflectionMatrix v c ∈ Matrix.orthogonalGroup n R := by
  rw [Matrix.mem_orthogonalGroup_iff, transpose_reflectionMatrix]
  exact reflectionMatrix_mul_self hc

/-- **A reflection matrix has determinant `-1`.** -/
@[simp]
theorem det_reflectionMatrix [Fintype n] {v : n → R} {c : R} (hc : c * (v ⬝ᵥ v) = 2) :
    (reflectionMatrix v c).det = -1 := by
  rw [reflectionMatrix_eq_one_sub_vecMulVec, det_one_sub_vecMulVec, dotProduct_smul,
    smul_eq_mul, hc]
  norm_num

/-! ### Comparison with the reflection of the standard quadratic form -/

section QuadraticForm

variable [Fintype n]

/-- The reflection of the standard quadratic form in a vector of invertible norm has
`reflectionMatrix` as its coordinate matrix. -/
theorem toMatrix'_reflection (v : n → R)
    [Invertible (Matrix.toQuadraticForm' (1 : Matrix n n R) v)] :
    LinearMap.toMatrix'
        (QuadraticMap.reflection (Matrix.toQuadraticForm' (1 : Matrix n n R)) v).toLinearMap =
      reflectionMatrix v (2 * ⅟(Matrix.toQuadraticForm' (1 : Matrix n n R) v)) := by
  ext i j
  rw [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe, QuadraticMap.reflection_apply,
    reflectionMatrix_apply]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, polar_toQuadraticForm'_one,
    Pi.single_apply, dotProduct_single, mul_one]
  ring_nf

end QuadraticForm

/-! ### Products of two reflections -/

section Pair

variable [Fintype n]

/-- The product of two reflection matrices is special orthogonal. -/
theorem reflectionMatrix_mul_mem_specialOrthogonalGroup {v w : n → R} {c d : R}
    (hc : c * (v ⬝ᵥ v) = 2) (hd : d * (w ⬝ᵥ w) = 2) :
    reflectionMatrix v c * reflectionMatrix w d ∈ Matrix.specialOrthogonalGroup n R :=
  Matrix.mem_specialOrthogonalGroup_iff.mpr
    ⟨Submonoid.mul_mem _ (reflectionMatrix_mem_orthogonalGroup hc)
        (reflectionMatrix_mem_orthogonalGroup hd),
      by rw [Matrix.det_mul, det_reflectionMatrix hc, det_reflectionMatrix hd]; ring⟩

/-- **The product of the reflections in two vectors with supplied normalizing scalars**, as an
element of the matrix special orthogonal group of the standard symmetric form. The scalars satisfy
the displayed equations with the respective norms. -/
def reflectionPair (v w : n → R) (c d : R) (hc : c * (v ⬝ᵥ v) = 2) (hd : d * (w ⬝ᵥ w) = 2) :
    Matrix.specialOrthogonalGroup n R :=
  ⟨reflectionMatrix v c * reflectionMatrix w d,
    reflectionMatrix_mul_mem_specialOrthogonalGroup hc hd⟩

@[simp]
theorem coe_reflectionPair {v w : n → R} {c d : R} (hc : c * (v ⬝ᵥ v) = 2)
    (hd : d * (w ⬝ᵥ w) = 2) :
    (reflectionPair v w c d hc hd : Matrix n n R) =
      reflectionMatrix v c * reflectionMatrix w d :=
  (rfl)

/-- Products of two reflections are natural in the coefficient ring. -/
@[simp]
theorem map_reflectionPair (f : R →+* S) {v w : n → R} {c d : R} (hc : c * (v ⬝ᵥ v) = 2)
    (hd : d * (w ⬝ᵥ w) = 2) :
    Matrix.SpecialOrthogonalGroup.map f (reflectionPair v w c d hc hd) =
      reflectionPair (f ∘ v) (f ∘ w) (f c) (f d)
        (by rw [← RingHom.map_dotProduct, ← map_mul, hc, map_ofNat])
        (by rw [← RingHom.map_dotProduct, ← map_mul, hd, map_ofNat]) :=
  Subtype.ext <| by
    rw [Matrix.SpecialOrthogonalGroup.coe_map, coe_reflectionPair, coe_reflectionPair,
      Matrix.map_mul, map_reflectionMatrix, map_reflectionMatrix]

end Pair

/-! ### One-parameter families through a product of two reflections -/

section Path

open scoped LaurentPolynomial

open LaurentPolynomial

variable {K : Type u} [Field K]

/-- The constant Laurent-polynomial vector attached to a vector over the coefficient field. -/
private noncomputable def constVector (v : n → K) : n → K[T;T⁻¹] := fun i => C (v i)

/-- The Laurent-polynomial vector `X • v + Y • w`. Its two coefficients travel along the
family, and each endpoint of the family is a parameter at which one of them vanishes. -/
private noncomputable def pathVector (v w : n → K) (X Y : K[T;T⁻¹]) : n → K[T;T⁻¹] :=
  fun i => X * C (v i) + Y * C (w i)

end Path

end TauCeti
