import Tengoku.EgzFormalProof.EGZ.Convex.Coordinate
import Tengoku.Seed.LinearAlgebra.Pi
import Tengoku.Seed.LinearAlgebra.LinearIndependent.BaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar extension of integer affine maps

An affine map of integer coordinate lattices is determined by its value at
zero and the images of the standard basis under its linear part. Casting
these integer coefficients constructs compatible affine maps over the real
numbers and modulo every natural number.
-/

open scoped BigOperators

namespace EGZ

namespace IntCoord

/--
@isnad1 id=injectiv.0h1v.s3.6cd4da71504d from=translated src=- shape=ca92e646 vocab=17e18337
-/
theorem real_injective {n : ℕ} : Function.Injective (@real n) :=
  isClosedEmbedding_real.injective

/--
@isnad1 id=eq.0h1v.s5.3fbb73242f22 from=translated src=- shape=771c46e9 vocab=3b8dec7a
-/
@[simp]
theorem real_zero {n : ℕ} : (0 : IntCoord n).real = 0 := by ext i; simp [real]

/--
@isnad1 id=eq.0h3v.s5.d72040ca8037 from=translated src=- shape=f0f972c8 vocab=afd269f4
-/
@[simp]
theorem real_add {n : ℕ} (x y : IntCoord n) : (x + y).real = x.real + y.real := by
  ext i
  simp [real]

/--
@isnad1 id=eq.0h3v.s5.e2bc62826486 from=translated src=- shape=f0f972c8 vocab=65bc41c8
-/
@[simp]
theorem real_sub {n : ℕ} (x y : IntCoord n) : (x - y).real = x.real - y.real := by
  ext i
  simp [real]

/--
@isnad1 id=eq.0h3v.s6.aa93e83ae00e from=translated src=- shape=fb01deb4 vocab=9bbde0f8
-/
@[simp]
theorem real_zsmul {n : ℕ} (c : ℤ) (x : IntCoord n) : (c • x).real = c • x.real := by
  ext i
  simp [real]

end IntCoord

namespace IntegralAffineMap

variable {l m n : ℕ}

/-- Extend the integer matrix of a linear map to a commutative ring.-/
noncomputable def linearScalarExtension (R : Type*) [CommRing R]
    (A : IntCoord m →ₗ[ℤ] IntCoord n) : (Fin m → R) →ₗ[R] (Fin n → R) where
  toFun x i := ∑ j, x j * (A (Pi.single j 1) i : R)
  map_add' x y := by
    ext i
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    simp [Finset.mul_sum, mul_assoc]

/-- Extend the integer coefficients and offset of an affine lattice map.-/
noncomputable def scalarExtension (R : Type*) [CommRing R]
    (A : IntCoord m →ᵃ[ℤ] IntCoord n) : (Fin m → R) →ᵃ[R] (Fin n → R) :=
  (linearScalarExtension R A.linear).toAffineMap +
    AffineMap.const R _ (fun i ↦ (A 0 i : R))

/--
@isnad1 id=eq.0h6v.s9.e15e0c25a063 from=translated src=- shape=63200647 vocab=79d5cb4a
-/
@[simp]
theorem scalarExtension_apply (R : Type*) [CommRing R]
    (A : IntCoord m →ᵃ[ℤ] IntCoord n) (x : Fin m → R) (i : Fin n) :
    scalarExtension R A x i = (∑ j, x j * (A.linear (Pi.single j 1) i : R)) +
      (A 0 i : R) := rfl

/-- Standard-basis expansion of an integer affine map, coordinate by coordinate.
@isnad1 id=eq.0h5v.s9.2235a826babb from=translated src=- shape=d32c1dae vocab=8851e700
-/
theorem integer_expansion (A : IntCoord m →ᵃ[ℤ] IntCoord n)
    (z : IntCoord m) (i : Fin n) :
    A z i = (∑ j, z j * A.linear (Pi.single j 1) i) + A 0 i := by
  have hl := congrArg (fun x ↦ A.linear x i) (pi_eq_sum_univ' z)
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hl
  have ha := congrFun (congrFun A.decomp z) i
  change A z i = A.linear z i + A 0 i at ha
  exact ha.trans (congrArg (fun t ↦ t + A 0 i) hl)

/-- Scalar extension agrees with the integer map on every integer vector.
@isnad1 id=eq.0h5v.s9.6b02430dfec0 from=translated src=- shape=56ca904a vocab=0801036e
-/
theorem scalarExtension_intCast (R : Type*) [CommRing R]
    (A : IntCoord m →ᵃ[ℤ] IntCoord n) (z : IntCoord m) :
    scalarExtension R A (fun i ↦ (z i : R)) = fun i ↦ (A z i : R) := by
  ext i
  rw [scalarExtension_apply, integer_expansion A z i]
  simp only [Int.cast_add, Int.cast_sum, Int.cast_mul]

/-- Affine maps on a coordinate module are determined by their values on
integer coordinate vectors, over any commutative ring.
@isnad1 id=eq.1h5v.s9.41e48ac4d3bc from=translated src=- shape=b0bfaab2 vocab=f614c71b
-/
theorem affine_ext_intCast (R : Type*) [CommRing R]
    {A B : (Fin m → R) →ᵃ[R] (Fin n → R)}
    (h : ∀ z : IntCoord m, A (fun i ↦ (z i : R)) = B (fun i ↦ (z i : R))) :
    A = B := by
  have hz : (fun i ↦ ((0 : IntCoord m) i : R)) = (0 : Fin m → R) := by
    ext i
    simp
  have hzero : A 0 = B 0 := by simpa only [hz] using h 0
  apply AffineMap.ext_linear ?_ hzero
  apply LinearMap.pi_ext
  intro i x
  have hcast : (fun j ↦ ((Pi.single i (1 : ℤ) : IntCoord m) j : R)) =
      Pi.single i (1 : R) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  have hsingle : A (Pi.single i 1) = B (Pi.single i 1) := by
    simpa only [hcast] using h (Pi.single i 1)
  have hlinear : A.linear (Pi.single i 1) = B.linear (Pi.single i 1) := by
    apply add_right_cancel (b := A 0)
    calc
      A.linear (Pi.single i 1) + A 0 = A (Pi.single i 1) := by
        simpa using (A.map_vadd 0 (Pi.single i 1)).symm
      _ = B (Pi.single i 1) := hsingle
      _ = B.linear (Pi.single i 1) + A 0 := by
        simpa [hzero] using B.map_vadd 0 (Pi.single i 1)
  have hx : Pi.single i x = x • Pi.single i (1 : R) := by
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [hx, map_smul, map_smul, hlinear]

/--
@isnad1 id=eq.0h2v.s7.2f51c62af3ec from=translated src=- shape=77d65a51 vocab=471c907c
-/
@[simp]
theorem scalarExtension_id (R : Type*) [CommRing R] :
    scalarExtension R (AffineMap.id ℤ (IntCoord n)) = AffineMap.id R (Fin n → R) := by
  apply affine_ext_intCast R
  intro z
  rw [scalarExtension_intCast]
  rfl

/--
@isnad1 id=eq.0h6v.s9.a165e68b3407 from=translated src=- shape=e6ccf256 vocab=38809fcd
-/
@[simp]
theorem scalarExtension_comp (R : Type*) [CommRing R]
    (A : IntCoord m →ᵃ[ℤ] IntCoord n) (B : IntCoord l →ᵃ[ℤ] IntCoord m) :
    scalarExtension R (A.comp B) = (scalarExtension R A).comp (scalarExtension R B) := by
  apply affine_ext_intCast R
  intro z
  simp only [scalarExtension_intCast, AffineMap.comp_apply]

/-- Package any integer affine map with its real and modular scalar extensions.-/
noncomputable def ofIntAffineMap (A : IntCoord m →ᵃ[ℤ] IntCoord n) :
    IntegralAffineMap m n where
  real := scalarExtension ℝ A
  integer := A
  modp p := scalarExtension (ZMod p) A
  real_integer z := scalarExtension_intCast ℝ A z
  mod_integer p z := scalarExtension_intCast (ZMod p) A z

/--
@isnad1 id=eq.0h3v.s8.21294603de8c from=translated src=- shape=0760cdb1 vocab=c27b7e3f
-/
@[simp]
theorem ofIntAffineMap_integer (A : IntCoord m →ᵃ[ℤ] IntCoord n) :
    (ofIntAffineMap A).integer = A := rfl

/--
@isnad1 id=eq.0h3v.s7.d6cb18a0ed7e from=translated src=- shape=ed4fb075 vocab=8152ca0e
-/
@[simp]
theorem ofIntAffineMap_real (A : IntCoord m →ᵃ[ℤ] IntCoord n) :
    (ofIntAffineMap A).real = scalarExtension ℝ A := rfl

/--
@isnad1 id=eq.0h4v.s8.ab7f2538245f from=translated src=- shape=49628a77 vocab=38f4f952
-/
@[simp]
theorem ofIntAffineMap_modp (A : IntCoord m →ᵃ[ℤ] IntCoord n) (p : ℕ) :
    (ofIntAffineMap A).modp p = scalarExtension (ZMod p) A := rfl

/-- An integral-affine map is determined by its integer realization.
@isnad1 id=eq.1h4v.s5.90fc4e6b89e2 from=translated src=- shape=9a79c626 vocab=31aa294e
-/
@[ext]
theorem ext_integer {A B : IntegralAffineMap m n} (h : A.integer = B.integer) : A = B := by
  have hr : A.real = B.real := by
    apply affine_ext_intCast ℝ
    intro z
    change A.real z.real = B.real z.real
    rw [A.real_integer, B.real_integer, h]
  have hm : A.modp = B.modp := by
    funext p
    apply affine_ext_intCast (ZMod p)
    intro z
    change A.modp p (z.mod p) = B.modp p (z.mod p)
    rw [A.mod_integer, B.mod_integer, h]
  cases A
  cases B
  simp_all

/--
@isnad1 id=eq.0h1v.s5.752d0d4be5fe from=translated src=- shape=85dd2600 vocab=cdaf5eb0
-/
@[simp]
theorem ofIntAffineMap_id : ofIntAffineMap (AffineMap.id ℤ (IntCoord n)) = id n :=
  ext_integer rfl

/--
@isnad1 id=eq.0h5v.s8.a7220acc1c5e from=translated src=- shape=3f2d5eff vocab=63d2183b
-/
@[simp]
theorem ofIntAffineMap_comp (A : IntCoord m →ᵃ[ℤ] IntCoord n)
    (B : IntCoord l →ᵃ[ℤ] IntCoord m) :
    ofIntAffineMap (A.comp B) = (ofIntAffineMap A).comp (ofIntAffineMap B) :=
  ext_integer rfl

/-- Injectivity of an integer linear map survives extension to real scalars.
@isnad1 id=injectiv.1h3v.s8.b200f9b7328a from=translated src=- shape=dcfae4f2 vocab=e3d9aba2
-/
theorem linearScalarExtension_real_injective (A : IntCoord m →ₗ[ℤ] IntCoord n)
    (hA : Function.Injective A) : Function.Injective (linearScalarExtension ℝ A) := by
  have hli : LinearIndependent ℤ (fun i : Fin m ↦ A (Pi.single i 1)) := by
    simpa only [Function.comp_def, Pi.basisFun_apply] using
      (Pi.basisFun ℤ (Fin m)).linearIndependent.map' A (LinearMap.ker_eq_bot.mpr hA)
  have hreal : LinearIndependent ℝ (fun i : Fin m ↦ (A (Pi.single i 1)).real) := by
    change LinearIndependent ℝ (fun i : Fin m ↦ fun j ↦ (A (Pi.single i 1) j : ℝ))
    simpa only [Function.comp_def, algebraMap_int_eq, Int.coe_castRingHom] using
      (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ)).mpr hli
  have heq : linearScalarExtension ℝ A =
      Fintype.linearCombination ℝ (fun i : Fin m ↦ (A (Pi.single i 1)).real) := by
    ext x i
    simp [linearScalarExtension, Fintype.linearCombination_apply, IntCoord.real]
  rw [heq]
  exact hreal.fintypeLinearCombination_injective

/-- An injective affine lattice chart has an injective real realization.
@isnad1 id=injectiv.1h3v.s8.ac9dfc96a24a from=translated src=- shape=a64cfe80 vocab=7b0365d0
-/
theorem ofIntAffineMap_real_injective (A : IntCoord m →ᵃ[ℤ] IntCoord n)
    (hA : Function.Injective A) : Function.Injective (ofIntAffineMap A).real := by
  apply ((ofIntAffineMap A).real.linear_injective_iff).mp
  simpa [ofIntAffineMap, scalarExtension] using
    linearScalarExtension_real_injective A.linear (A.linear_injective_iff.mpr hA)

/-- The difference from the integer offset realizes the real linear part.
@isnad1 id=eq.0h4v.s8.bd1ff07d2109 from=translated src=- shape=36cde312 vocab=7e917f2d
-/
theorem integer_sub_zero_real (A : IntegralAffineMap m n) (z : IntCoord m) :
    (A.integer z - A.integer 0).real = A.real.linear z.real := by
  have h := A.real.linearMap_vsub z.real (0 : RealCoord m)
  rw [vsub_eq_sub, vsub_eq_sub, sub_zero, ← IntCoord.real_zero,
    A.real_integer, A.real_integer] at h
  simpa only [IntCoord.real_sub] using h.symm

/-- Recover the integer linear part of an integral-affine map. Its additivity
and integer homogeneity follow from compatibility with its real realization.-/
def integerLinear (A : IntegralAffineMap m n) : IntCoord m →ₗ[ℤ] IntCoord n where
  toFun z := A.integer z - A.integer 0
  map_add' x y := by
    apply IntCoord.real_injective
    simp only [IntCoord.real_add, integer_sub_zero_real, map_add]
  map_smul' c x := by
    apply IntCoord.real_injective
    simp only [IntCoord.real_zsmul, integer_sub_zero_real, map_zsmul,
      RingHom.id_apply]

/-- The stored integer realization is itself an affine map over the integers.-/
def toIntAffineMap (A : IntegralAffineMap m n) : IntCoord m →ᵃ[ℤ] IntCoord n where
  toFun := A.integer
  linear := A.integerLinear
  map_vadd' p v := by
    apply IntCoord.real_injective
    change (A.integer (v + p)).real =
      (A.integer v - A.integer 0 + A.integer p).real
    rw [IntCoord.real_add, integer_sub_zero_real, ← A.real_integer, ← A.real_integer,
      IntCoord.real_add]
    exact A.real.map_vadd (IntCoord.real p) (IntCoord.real v)

/--
@isnad1 id=eq.0h4v.s7.b364f4a6b1fa from=translated src=- shape=a832ddad vocab=d374fb3c
-/
@[simp]
theorem toIntAffineMap_apply (A : IntegralAffineMap m n) (z : IntCoord m) :
    A.toIntAffineMap z = A.integer z := rfl

/--
@isnad1 id=eq.0h3v.s4.4199747fc54a from=translated src=- shape=db68ba20 vocab=aba3bfa4
-/
@[simp]
theorem ofIntAffineMap_toIntAffineMap (A : IntegralAffineMap m n) :
    ofIntAffineMap A.toIntAffineMap = A := ext_integer rfl

/--
@isnad1 id=eq.0h3v.s7.6aaf1678d693 from=translated src=- shape=91dc9a07 vocab=e3605249
-/
@[simp]
theorem toIntAffineMap_ofIntAffineMap (A : IntCoord m →ᵃ[ℤ] IntCoord n) :
    (ofIntAffineMap A).toIntAffineMap = A := AffineMap.ext fun _ ↦ rfl

/--
@isnad1 id=eq.0h1v.s7.4ad0ea181a9d from=translated src=- shape=b75053f7 vocab=b12c24ad
-/
@[simp]
theorem toIntAffineMap_id : (id n).toIntAffineMap = AffineMap.id ℤ (IntCoord n) :=
  AffineMap.ext fun _ ↦ rfl

/--
@isnad1 id=eq.0h5v.s7.6ba6fe0874f3 from=translated src=- shape=21f109ed vocab=a74e90df
-/
@[simp]
theorem toIntAffineMap_comp (A : IntegralAffineMap m n) (B : IntegralAffineMap l m) :
    (A.comp B).toIntAffineMap = A.toIntAffineMap.comp B.toIntAffineMap :=
  AffineMap.ext fun _ ↦ rfl

end IntegralAffineMap
end EGZ
