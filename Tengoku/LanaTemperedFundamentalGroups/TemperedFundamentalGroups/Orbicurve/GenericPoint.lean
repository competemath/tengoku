/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The generic point of an elliptic curve and its affine automorphisms

Let `W` be an elliptic curve over a field `k` with function field `F = k(W)`. This file
constructs the generic point `genericPoint W ∈ W(F)` (with coordinates the classes of `X` and
`Y`) and the group `AffAut W` of affine automorphisms `P ↦ ε • P + m` (`ε = ±1`, `m ∈ W(k)`) of
`W`, acting on `F` by pullback of functions.

For `g : AffAut W` the `k`-algebra endomorphism `pullback W g : F →ₐ[k] F` ("`f ↦ f ∘ g`") is
the unique one sending the generic point to `g(genericPoint W)`; it exists because the
`x`-coordinate of `g(genericPoint W)` is transcendental over `k`. We have
`pullback W (g * h) = (pullback W h).comp (pullback W g)`, so that `g • f := pullback W g⁻¹ f`
is a left action by `k`-algebra automorphisms.

## Main definitions

* `xOf`, `yOf`: the coordinates of a point (`0` for the point at infinity).
* `bc W L`: the base change `W(k) →+ W(L)`.
* `genericPoint W`: the generic point of `W` in `W(k(W))`.
* `liftFF`: the `k`-algebra map `k(W) → L` sending the generic point to an `L`-point with
  transcendental `x`-coordinate.
* `AffAut W`: the group of affine automorphisms `P ↦ ε • P + m`, acting on points over any
  extension by `AffAut.act`.
* `pullback W g`: the pullback of functions along `g`; the instance
  `MulSemiringAction (AffAut W) (funField W)`.
-/

universe u

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

namespace TemperedFundamentalGroups.Orbicurve

noncomputable section

variable {k : Type u} [Field k] (W : WeierstrassCurve k)

/-! ### Coordinates of points -/

section Coordinates

variable {L : Type*} [Field L] {V : Affine L}

/-- The `x`-coordinate of a point (`0` for the point at infinity). -/
def xOf : V.Point → L
  | .zero => 0
  | .some x _ _ => x

/-- The `y`-coordinate of a point (`0` for the point at infinity). -/
def yOf : V.Point → L
  | .zero => 0
  | .some _ y _ => y

/--
@isnad1 id=eq.1h4v.s5.1525e0875428 from=translated src=- shape=81bddcde vocab=b2014692
-/
@[simp] lemma xOf_some {x y : L} (h : V.Nonsingular x y) : xOf (.some x y h) = x := rfl

/--
@isnad1 id=eq.1h4v.s5.b0c2f147de10 from=translated src=- shape=de9bbb93 vocab=66b184db
-/
@[simp] lemma yOf_some {x y : L} (h : V.Nonsingular x y) : yOf (.some x y h) = y := rfl

/--
@isnad1 id=nonsingu.1h3v.s5.c03ce9692afe from=translated src=- shape=b356ad54 vocab=3d96a57a
-/
lemma nonsingular_xOf_yOf {P : V.Point} (hP : P ≠ 0) : V.Nonsingular (xOf P) (yOf P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact h

/--
@isnad1 id=equation.1h3v.s5.99694b01ec3d from=translated src=- shape=b356ad54 vocab=4fffc236
-/
lemma equation_xOf_yOf {P : V.Point} (hP : P ≠ 0) : V.Equation (xOf P) (yOf P) :=
  (nonsingular_xOf_yOf hP).1

lemma eq_some_xOf_yOf {P : V.Point} (hP : P ≠ 0) : P = .some _ _ (nonsingular_xOf_yOf hP) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => rfl

/--
@isnad1 id=eq.4h4v.s6.ece0786617b9 from=translated src=- shape=8a86a151 vocab=ec587615
-/
lemma Point.ext_xOf_yOf {P Q : V.Point} (hP : P ≠ 0) (hQ : Q ≠ 0) (hx : xOf P = xOf Q)
    (hy : yOf P = yOf Q) : P = Q := by
  rw [eq_some_xOf_yOf hP, eq_some_xOf_yOf hQ]
  simp [hx, hy]

variable {K : Type*} [Field K] [DecidableEq L] [DecidableEq K] [Algebra k L] [Algebra k K]
  (φ : L →ₐ[k] K)
  {V : WeierstrassCurve k}

/--
@isnad1 id=eq.0h6v.s8.078f789b324c from=translated src=- shape=5ce53778 vocab=d3b75ae1
-/
lemma xOf_map (P : (V.toAffine⁄L).Point) : xOf (Point.map φ P) = φ (xOf P) := by
  cases P with
  | zero => exact (map_zero φ).symm
  | some x y h => rfl

/--
@isnad1 id=eq.0h6v.s8.ae40c7c81fe4 from=translated src=- shape=5ce53778 vocab=9cfb9144
-/
lemma yOf_map (P : (V.toAffine⁄L).Point) : yOf (Point.map φ P) = φ (yOf P) := by
  cases P with
  | zero => exact (map_zero φ).symm
  | some x y h => rfl

/--
@isnad1 id=iff.0h6v.s9.f0c8d08cb688 from=translated src=- shape=1fa2e19f vocab=a41500be
-/
lemma map_eq_zero_iff {P : (V.toAffine⁄L).Point} : Point.map φ P = 0 ↔ P = 0 := by
  rw [← (Point.map φ).map_zero]
  exact (Point.map_injective φ).eq_iff

end Coordinates

/-! ### Base change of rational points -/

section BaseChange

variable [DecidableEq k] (L : Type*) [Field L] [DecidableEq L] [Algebra k L]

/-- The base change `W(k) →+ W(L)` of rational points. -/
def bc : W.toAffine.Point →+ (W.toAffine⁄L).Point :=
  Point.map (W' := W.toAffine) (Algebra.ofId k L)

variable {W L}

/--
@isnad1 id=eq.0h4v.s8.be0d485c191a from=translated src=- shape=c5d1eba8 vocab=2b00e05a
-/
@[simp] lemma xOf_bc (P : W.toAffine.Point) : xOf (bc W L P) = algebraMap k L (xOf P) :=
  xOf_map (V := W) (Algebra.ofId k L) P

/--
@isnad1 id=eq.0h4v.s8.47a0163261c3 from=translated src=- shape=c5d1eba8 vocab=72d328f8
-/
@[simp] lemma yOf_bc (P : W.toAffine.Point) : yOf (bc W L P) = algebraMap k L (yOf P) :=
  yOf_map (V := W) (Algebra.ofId k L) P

/--
@isnad1 id=iff.0h4v.s8.cff78a483d70 from=translated src=- shape=32565011 vocab=34d1b748
-/
@[simp] lemma bc_eq_zero_iff {P : W.toAffine.Point} : bc W L P = 0 ↔ P = 0 :=
  map_eq_zero_iff (V := W) (Algebra.ofId k L)

/--
@isnad1 id=eq.0h6v.s9.cfec4918f984 from=translated src=- shape=5820e189 vocab=e92ad650
-/
lemma map_bc {K : Type*} [Field K] [DecidableEq K] [Algebra k K] (φ : L →ₐ[k] K)
    (P : W.toAffine.Point) :
    Point.map φ (bc W L P) = bc W K P := by
  have := Point.map_map (W' := W.toAffine) (Algebra.ofId k L) φ P
  rw [Subsingleton.elim (φ.comp (Algebra.ofId k L)) (Algebra.ofId k K)] at this
  exact this

omit [DecidableEq k] in
/--
@isnad1 id=eq.0h7v.s10.69438a21fa75 from=translated src=- shape=48437fd3 vocab=94ab56a2
-/
lemma map_units_smul {K : Type*} [Field K] [DecidableEq K] [Algebra k K] (φ : L →ₐ[k] K) (ε : ℤˣ)
    (P : (W.toAffine⁄L).Point) : Point.map φ (ε • P) = ε • Point.map φ P := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

/--
@isnad1 id=eq.0h5v.s9.8484152431a5 from=translated src=- shape=251e7211 vocab=ef0673d2
-/
lemma bc_units_smul (ε : ℤˣ) (P : W.toAffine.Point) : bc W L (ε • P) = ε • bc W L P := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]

end BaseChange

/-! ### The generic point -/

/-- The function field `k(W)` of `W`. -/
abbrev funField : Type u := W.toAffine.FunctionField

/-- The `x`-coordinate of the generic point: the class of `X` in `k(W)`. -/
def xGen : funField W :=
  algebraMap W.toAffine.CoordinateRing _ (AdjoinRoot.mk W.toAffine.polynomial (C X))

/-- The `y`-coordinate of the generic point: the class of `Y` in `k(W)`. -/
def yGen : funField W :=
  algebraMap W.toAffine.CoordinateRing _ (AdjoinRoot.mk W.toAffine.polynomial X)

/--
@isnad1 id=eq.0h3v.s11.24a11a01781f from=translated src=- shape=140bcad5 vocab=902c4c04
-/
lemma algebraMap_funField (a : k) : algebraMap k (funField W) a =
    algebraMap W.toAffine.CoordinateRing _ (AdjoinRoot.mk W.toAffine.polynomial (C (C a))) := by
  rw [IsScalarTower.algebraMap_apply k W.toAffine.CoordinateRing]
  rfl

/--
@isnad1 id=equation.0h2v.s9.bf0c3db35bf2 from=translated src=- shape=fd4d3e3e vocab=7231590e
-/
lemma equation_gen : (W.toAffine⁄(funField W)).Equation (xGen W) (yGen W) := by
  have h0 : AdjoinRoot.mk W.toAffine.polynomial (Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y -
      C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) = 0 := AdjoinRoot.mk_self
  have h := congrArg (algebraMap W.toAffine.CoordinateRing (funField W)) h0
  rw [equation_iff]
  simp only [map_add, map_sub, map_mul, map_pow, map_zero] at h
  simp only [xGen, yGen, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, algebraMap_funField]
  linear_combination h

variable {W} in
/--
@isnad1 id=nonsingu.1h5v.s6.4ac7ff550d4a from=translated src=- shape=6713050f vocab=40ee67ce
-/
lemma nonsingular_of_equation [W.IsElliptic] {L : Type*} [Field L] [Algebra k L] {x y : L}
    (h : (W.toAffine⁄L).Equation x y) : (W.toAffine⁄L).Nonsingular x y := by
  haveI : (W.toAffine⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap k L)).IsElliptic
  exact equation_iff_nonsingular.mp h

/-- The generic point of `W`, a point of `W` over its function field. -/
def genericPoint [W.IsElliptic] : (W.toAffine⁄(funField W)).Point :=
  .some (xGen W) (yGen W) (nonsingular_of_equation (equation_gen W))

/--
@isnad1 id=ne.0h2v.s11.b75bcb970e65 from=translated src=- shape=4fbed248 vocab=7b7ec310
-/
@[simp] lemma genericPoint_ne_zero [W.IsElliptic] : genericPoint W ≠ 0 :=
  Point.some_ne_zero _

/--
@isnad1 id=eq.0h2v.s8.4f9a11196313 from=translated src=- shape=7be89baa vocab=35875d9e
-/
@[simp] lemma xOf_genericPoint [W.IsElliptic] : xOf (genericPoint W) = xGen W := rfl

/--
@isnad1 id=eq.0h2v.s8.6ba02886c4a7 from=translated src=- shape=7be89baa vocab=6af97f11
-/
@[simp] lemma yOf_genericPoint [W.IsElliptic] : yOf (genericPoint W) = yGen W := rfl

/--
@isnad1 id=eq.0h3v.s11.a3c95bdaa710 from=translated src=- shape=87eba4ac vocab=579e36ad
-/
lemma aeval_xGen (p : k[X]) : aeval (xGen W) p =
    algebraMap W.toAffine.CoordinateRing (funField W)
      (AdjoinRoot.mk W.toAffine.polynomial (C p)) := by
  rw [xGen, ← IsScalarTower.coe_toAlgHom' k, Polynomial.aeval_algHom_apply]
  congr 1
  rw [AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, aeval_algebraMap_apply, aeval_X_left_apply,
    AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C]

/--
@isnad1 id=transcen.0h2v.s8.ddb7592c6c21 from=translated src=- shape=40e80979 vocab=2ceea5cc
-/
lemma transcendental_xGen : Transcendental k (xGen W) := by
  rw [transcendental_iff_injective]
  intro p q h
  simp only [aeval_xGen] at h
  have := IsFractionRing.injective W.toAffine.CoordinateRing (funField W) h
  rw [AdjoinRoot.mk_C, AdjoinRoot.mk_C] at this
  exact AdjoinRoot.of.injective_of_degree_ne_zero
    (by rw [W.toAffine.degree_polynomial]; decide) this

/-! ### Maps out of the function field -/

section Eval

variable {L : Type*} [CommRing L] [Algebra k L]

/-- The evaluation `k[W] →ₐ[k] L` at a solution `(x, y)` of the Weierstrass equation. -/
def evalHom (x y : L) (h : (W.toAffine⁄L).Equation x y) :
    W.toAffine.CoordinateRing →ₐ[k] L :=
  AdjoinRoot.liftAlgHom _ (Polynomial.aeval x) y (by
    rw [equation_iff] at h
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
    simp [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_pow]
    linear_combination h)

variable {W}

/--
@isnad1 id=eq.1h6v.s9.59d74a101c3c from=translated src=- shape=6a110da4 vocab=7e1a66d6
-/
lemma evalHom_of (x y : L) (h : (W.toAffine⁄L).Equation x y) (p : k[X]) :
    evalHom W x y h (AdjoinRoot.of _ p) = aeval x p := by
  simp [evalHom]

/--
@isnad1 id=eq.1h5v.s10.3aac4563acec from=translated src=- shape=d4854b29 vocab=1c8fafd9
-/
lemma evalHom_x (x y : L) (h : (W.toAffine⁄L).Equation x y) :
    evalHom W x y h (AdjoinRoot.mk W.toAffine.polynomial (C X)) = x := by
  rw [AdjoinRoot.mk_C, evalHom_of, aeval_X]

/--
@isnad1 id=eq.1h5v.s9.c3cb5289e36e from=translated src=- shape=8b7cd1e9 vocab=e8d35872
-/
lemma evalHom_y (x y : L) (h : (W.toAffine⁄L).Equation x y) :
    evalHom W x y h (AdjoinRoot.mk W.toAffine.polynomial X) = y := by
  simp [evalHom]

end Eval

section Lift

variable {L : Type*} [Field L] [Algebra k L] {W}

instance : Module.Finite k[X] W.toAffine.CoordinateRing :=
  Module.Finite.of_basis (CoordinateRing.basis W.toAffine)

/--
@isnad1 id=injectiv.2h5v.s7.a97ca7198e03 from=translated src=- shape=45af54ea vocab=7bce15d7
-/
lemma injective_evalHom (x y : L) (h : (W.toAffine⁄L).Equation x y) (hx : Transcendental k x) :
    Function.Injective (evalHom W x y h) := by
  have hker : RingHom.ker (evalHom W x y h) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := k[X])
    refine eq_bot_iff.mpr fun p hp => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, AdjoinRoot.algebraMap_eq, evalHom_of] at hp
    by_contra hp0
    exact hx ⟨p, hp0, hp⟩
  exact (RingHom.injective_iff_ker_eq_bot _).mpr hker

/-- The `k`-algebra map `k(W) → L` sending the generic point to the `L`-point `(x, y)`, for `x`
transcendental over `k`. -/
def liftFF (x y : L) (h : (W.toAffine⁄L).Equation x y) (hx : Transcendental k x) :
    funField W →ₐ[k] L :=
  IsFractionRing.liftAlgHom (injective_evalHom x y h hx)

/--
@isnad1 id=eq.2h5v.s9.a7a73f6bc5c0 from=translated src=- shape=5ab691d6 vocab=711381c7
-/
@[simp] lemma liftFF_xGen (x y : L) (h : (W.toAffine⁄L).Equation x y) (hx : Transcendental k x) :
    liftFF x y h hx (xGen W) = x := by
  rw [liftFF, IsFractionRing.liftAlgHom_apply, xGen, IsFractionRing.lift_algebraMap]
  exact evalHom_x x y h

/--
@isnad1 id=eq.2h5v.s9.47befd513f6c from=translated src=- shape=d29be579 vocab=c1296b61
-/
@[simp] lemma liftFF_yGen (x y : L) (h : (W.toAffine⁄L).Equation x y) (hx : Transcendental k x) :
    liftFF x y h hx (yGen W) = y := by
  rw [liftFF, IsFractionRing.liftAlgHom_apply, yGen, IsFractionRing.lift_algebraMap]
  exact evalHom_y x y h

/-- A `k`-algebra map out of `k(W)` is determined by the images of the coordinates of the generic
point.
@isnad1 id=eq.2h5v.s12.5571d008131c from=translated src=- shape=6ab27e3c vocab=4bd81525
-/
lemma algHom_ext_funField {φ ψ : funField W →ₐ[k] L} (hx : φ (xGen W) = ψ (xGen W))
    (hy : φ (yGen W) = ψ (yGen W)) : φ = ψ := by
  have hc : φ.comp (IsScalarTower.toAlgHom k W.toAffine.CoordinateRing (funField W)) =
      ψ.comp (IsScalarTower.toAlgHom k W.toAffine.CoordinateRing (funField W)) := by
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      change φ (algebraMap _ _ (AdjoinRoot.of _ X)) = ψ (algebraMap _ _ (AdjoinRoot.of _ X))
      rw [← AdjoinRoot.mk_C]
      exact hx
    · exact hy
  apply AlgHom.coe_ringHom_injective
  exact IsFractionRing.ringHom_ext (A := W.toAffine.CoordinateRing)
    fun c => DFunLike.congr_fun hc c

variable [DecidableEq L] [W.IsElliptic]

/--
@isnad1 id=eq.0h4v.s12.9b129668c7c8 from=translated src=- shape=caabf75a vocab=70308c2d
-/
lemma xOf_map_genericPoint (φ : funField W →ₐ[k] L) :
    xOf (Point.map φ (genericPoint W)) = φ (xGen W) := xOf_map φ _

/--
@isnad1 id=eq.0h4v.s12.f55e61c0cc01 from=translated src=- shape=caabf75a vocab=b30e0244
-/
lemma yOf_map_genericPoint (φ : funField W →ₐ[k] L) :
    yOf (Point.map φ (genericPoint W)) = φ (yGen W) := yOf_map φ _

/-- A `k`-algebra map out of `k(W)` is determined by the image of the generic point.
@isnad1 id=eq.1h5v.s12.2afba4782539 from=translated src=- shape=27cacf42 vocab=b0fa3be3
-/
lemma algHom_ext_of_map_genericPoint {φ ψ : funField W →ₐ[k] L}
    (h : Point.map φ (genericPoint W) = Point.map ψ (genericPoint W)) : φ = ψ := by
  apply algHom_ext_funField
  · rw [← xOf_map_genericPoint, h, xOf_map_genericPoint]
  · rw [← yOf_map_genericPoint, h, yOf_map_genericPoint]

/--
@isnad1 id=eq.2h4v.s11.56622346610c from=translated src=- shape=c19ce339 vocab=bd3357a2
-/
lemma map_liftFF_genericPoint {P : (W.toAffine⁄L).Point} (hP : P ≠ 0)
    (hx : Transcendental k (xOf P)) :
    Point.map (liftFF (xOf P) (yOf P) (equation_xOf_yOf hP) hx) (genericPoint W) = P := by
  refine Point.ext_xOf_yOf ?_ hP ?_ ?_
  · exact fun h => genericPoint_ne_zero W ((map_eq_zero_iff _).mp h)
  · rw [xOf_map_genericPoint, liftFF_xGen]
  · rw [yOf_map_genericPoint, liftFF_yGen]

end Lift

/-! ### Affine automorphisms -/

variable [DecidableEq k]

/-- The affine automorphism `P ↦ ε • P + m` of `W`, for `ε = ±1` and `m ∈ W(k)`. -/
@[ext]
structure AffAut : Type u where
  /-- The linear part `ε = ±1`. -/
  ε : ℤˣ
  /-- The translation part `m ∈ W(k)`. -/
  m : W.toAffine.Point

namespace AffAut

variable {W}

instance : Group (AffAut W) where
  mul g h := ⟨g.ε * h.ε, g.ε • h.m + g.m⟩
  one := ⟨1, 0⟩
  inv g := ⟨g.ε⁻¹, -(g.ε⁻¹ • g.m)⟩
  mul_assoc g h l := by
    refine AffAut.ext (mul_assoc g.ε h.ε l.ε) ?_
    change (g.ε * h.ε) • l.m + (g.ε • h.m + g.m) = g.ε • (h.ε • l.m + h.m) + g.m
    rw [smul_add, mul_smul, add_assoc]
  one_mul g := by
    refine AffAut.ext (one_mul g.ε) ?_
    change (1 : ℤˣ) • g.m + 0 = g.m
    rw [one_smul, add_zero]
  mul_one g := by
    refine AffAut.ext (mul_one g.ε) ?_
    change g.ε • (0 : W.toAffine.Point) + g.m = g.m
    rw [smul_zero, zero_add]
  inv_mul_cancel g := by
    refine AffAut.ext (inv_mul_cancel g.ε) ?_
    change g.ε⁻¹ • g.m + -(g.ε⁻¹ • g.m) = 0
    rw [add_neg_cancel]

/--
@isnad1 id=eq.0h4v.s6.3a4a7a87804e from=translated src=- shape=9b5d1540 vocab=e5b96da9
-/
@[simp] lemma mul_ε (g h : AffAut W) : (g * h).ε = g.ε * h.ε := rfl
/--
@isnad1 id=eq.0h4v.s7.ceeb2e7295b9 from=translated src=- shape=ba01de65 vocab=bcf5585b
-/
@[simp] lemma mul_m (g h : AffAut W) : (g * h).m = g.ε • h.m + g.m := rfl
/--
@isnad1 id=eq.0h2v.s6.c8da6f55425c from=translated src=- shape=61991260 vocab=4542c603
-/
@[simp] lemma one_ε : (1 : AffAut W).ε = 1 := rfl
/--
@isnad1 id=eq.0h2v.s6.4559c175adb6 from=translated src=- shape=2b67225d vocab=77e3e516
-/
@[simp] lemma one_m : (1 : AffAut W).m = 0 := rfl
/--
@isnad1 id=eq.0h3v.s6.5488cfd8afab from=translated src=- shape=d2d54619 vocab=9fba1776
-/
@[simp] lemma inv_ε (g : AffAut W) : g⁻¹.ε = g.ε⁻¹ := rfl
/--
@isnad1 id=eq.0h3v.s7.5a605e2567ca from=translated src=- shape=056d1d0e vocab=1530a22b
-/
@[simp] lemma inv_m (g : AffAut W) : g⁻¹.m = -(g.ε⁻¹ • g.m) := rfl

/-- The action of an affine automorphism on the `L`-points: `P ↦ ε • P + m`. -/
def act (L : Type*) [Field L] [DecidableEq L] [Algebra k L] (g : AffAut W)
    (P : (W.toAffine⁄L).Point) :
    (W.toAffine⁄L).Point :=
  g.ε • P + bc W L g.m

variable (L : Type*) [Field L] [DecidableEq L] [Algebra k L]

/--
@isnad1 id=eq.0h5v.s9.93358f1f5575 from=translated src=- shape=9c19a01b vocab=dd8e5dc6
-/
lemma act_def (g : AffAut W) (P : (W.toAffine⁄L).Point) : g.act L P = g.ε • P + bc W L g.m :=
  rfl

/--
@isnad1 id=eq.0h6v.s7.ba26a164b5f6 from=translated src=- shape=612601e2 vocab=fc9d4a26
-/
lemma act_mul (g h : AffAut W) (P : (W.toAffine⁄L).Point) :
    (g * h).act L P = g.act L (h.act L P) := by
  simp only [act_def, mul_ε, mul_m, map_add, bc_units_smul, smul_add, mul_smul, add_assoc]

/--
@isnad1 id=eq.0h4v.s6.c65f31de1bae from=translated src=- shape=72b67d60 vocab=4c02b971
-/
lemma act_one (P : (W.toAffine⁄L).Point) : (1 : AffAut W).act L P = P := by
  simp [act_def]

/--
@isnad1 id=eq.0h5v.s7.f5e6fb7ef886 from=translated src=- shape=64e8c1c9 vocab=f002b412
-/
lemma act_inv_act (g : AffAut W) (P : (W.toAffine⁄L).Point) : g⁻¹.act L (g.act L P) = P := by
  rw [← act_mul, inv_mul_cancel, act_one]

variable {L} in
/--
@isnad1 id=eq.0h7v.s9.45c0bc1f6f9b from=translated src=- shape=8d24389e vocab=cf7d35a1
-/
lemma map_act {K : Type*} [Field K] [DecidableEq K] [Algebra k K] (φ : L →ₐ[k] K) (g : AffAut W)
    (P : (W.toAffine⁄L).Point) : Point.map φ (g.act L P) = g.act K (Point.map φ P) := by
  rw [act_def, act_def, map_add, map_units_smul, map_bc]

/-- The action of affine automorphisms on the rational points. -/
instance : MulAction (AffAut W) W.toAffine.Point where
  smul g P := g.ε • P + g.m
  one_smul P := by
    change (1 : ℤˣ) • P + 0 = P
    rw [one_smul, add_zero]
  mul_smul g h P := by
    change (g.ε * h.ε) • P + (g.ε • h.m + g.m) = g.ε • (h.ε • P + h.m) + g.m
    rw [smul_add, mul_smul, add_assoc]

/--
@isnad1 id=eq.0h4v.s8.21e24744650a from=translated src=- shape=2af9aa1d vocab=eebdedbe
-/
lemma smul_def (g : AffAut W) (P : W.toAffine.Point) : g • P = g.ε • P + g.m := rfl

/--
@isnad1 id=eq.0h5v.s9.24d93eef41a9 from=translated src=- shape=8dffe0f0 vocab=bedbef0a
-/
lemma bc_smul (g : AffAut W) (P : W.toAffine.Point) : bc W L (g • P) = g.act L (bc W L P) := by
  rw [smul_def, act_def, map_add, bc_units_smul]

end AffAut

/-! ### Pullback of functions -/

section Pullback

variable [W.IsElliptic]

/-- The algebraic closure of `k` in `k(W)`. -/
local notation "K₀" => algebraicClosure k (funField W)

omit [DecidableEq k] [W.IsElliptic] in
/--
@isnad1 id=mem.1h3v.s16.348e2dbf96ff from=translated src=- shape=4602cccb vocab=7add0191
-/
lemma mem_range_of_isAlgebraic {Q : (W.toAffine⁄(funField W)).Point}
    (hQ : Q ≠ 0 → IsAlgebraic k (xOf Q)) : Q ∈ Set.range (Point.map (K₀).val) := by
  by_cases hQ0 : Q = 0
  · exact ⟨0, by rw [hQ0, map_zero]⟩
  have hx : xOf Q ∈ K₀ := mem_algebraicClosure_iff.mpr (hQ hQ0)
  set x : K₀ := ⟨xOf Q, hx⟩
  have hns := nonsingular_xOf_yOf hQ0
  have hy : IsAlgebraic k (yOf Q) := by
    obtain ⟨b, hb⟩ : ∃ b : K₀, b = algebraMap k K₀ W.a₁ * x + algebraMap k K₀ W.a₃ := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : K₀, c = x ^ 3 + algebraMap k K₀ W.a₂ * x ^ 2 +
      algebraMap k K₀ W.a₄ * x + algebraMap k K₀ W.a₆ := ⟨_, rfl⟩
    let p : (K₀)[X] := X ^ 2 + C b * X - C c
    have hp : p ≠ 0 := fun h => by simpa [p] using congrArg (coeff · 2) h
    have hpy : aeval (yOf Q) p = 0 := by
      have := (equation_iff _ _).mp hns.1
      simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
        WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at this
      simp only [p, hb, hc, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
        IntermediateField.algebraMap_apply, IntermediateField.coe_algebraMap_apply, x]
      linear_combination this
    exact IsAlgebraic.restrictScalars k ⟨p, hp, hpy⟩
  set y : K₀ := ⟨yOf Q, mem_algebraicClosure_iff.mpr hy⟩
  have hns' : (W.toAffine⁄K₀).Nonsingular x y :=
    (W.toAffine.baseChange_nonsingular (f := (K₀).val) Subtype.val_injective x y).mp hns
  refine ⟨.some x y hns', Point.ext_xOf_yOf ?_ hQ0 rfl rfl⟩
  rw [Ne, map_eq_zero_iff]
  exact Point.some_ne_zero _

omit [DecidableEq k] in
/--
@isnad1 id=not.0h2v.s16.c14accff358b from=translated src=- shape=7739c70a vocab=3ee83451
-/
lemma genericPoint_notMem_range : genericPoint W ∉ Set.range (Point.map (K₀).val) := by
  rintro ⟨Q, hQ⟩
  have hx : xGen W = (K₀).val (xOf Q) := by
    rw [← xOf_genericPoint, ← hQ]
    exact xOf_map _ Q
  apply transcendental_xGen W
  rw [hx]
  exact mem_algebraicClosure_iff.mp (xOf Q).2

/--
@isnad1 id=and.0h3v.s11.767b9c6ec3d4 from=translated src=- shape=1f77d936 vocab=5dbb2e8f
-/
lemma act_genericPoint_ne_zero_and (g : AffAut W) :
    g.act _ (genericPoint W) ≠ 0 ∧ Transcendental k (xOf (g.act _ (genericPoint W))) := by
  by_contra h
  rw [not_and_or, not_not, Transcendental, not_not] at h
  have hmem := mem_range_of_isAlgebraic W (Q := g.act _ (genericPoint W))
    fun h0 => h.resolve_left h0
  obtain ⟨Q, hQ⟩ := hmem
  apply genericPoint_notMem_range W
  refine ⟨g⁻¹.act _ Q, ?_⟩
  rw [AffAut.map_act, hQ, AffAut.act_inv_act]

/--
@isnad1 id=ne.0h3v.s10.bec95fd54a1d from=translated src=- shape=6d8a190f vocab=68a0c220
-/
lemma act_genericPoint_ne_zero (g : AffAut W) : g.act _ (genericPoint W) ≠ 0 :=
  (act_genericPoint_ne_zero_and W g).1

/--
@isnad1 id=transcen.0h3v.s10.f747749b0a22 from=translated src=- shape=5b9104e2 vocab=d79074d7
-/
lemma transcendental_xOf_act (g : AffAut W) :
    Transcendental k (xOf (g.act _ (genericPoint W))) :=
  (act_genericPoint_ne_zero_and W g).2

/-- The pullback of functions along an affine automorphism `g`: the `k`-algebra endomorphism
`f ↦ f ∘ g` of `k(W)`, characterized by sending the generic point to `g(genericPoint W)`. -/
def pullback (g : AffAut W) : funField W →ₐ[k] funField W :=
  liftFF _ _ (equation_xOf_yOf (act_genericPoint_ne_zero W g)) (transcendental_xOf_act W g)

/--
@isnad1 id=eq.0h3v.s12.c79769e0d25a from=translated src=- shape=1c77ce1a vocab=185719cd
-/
lemma map_pullback_genericPoint (g : AffAut W) :
    Point.map (pullback W g) (genericPoint W) = g.act _ (genericPoint W) :=
  map_liftFF_genericPoint (act_genericPoint_ne_zero W g) _

/--
@isnad1 id=eq.0h3v.s11.ea890afb5807 from=translated src=- shape=5cc29f4e vocab=d813e69e
-/
lemma pullback_xGen (g : AffAut W) : pullback W g (xGen W) = xOf (g.act _ (genericPoint W)) :=
  liftFF_xGen _ _ _ _

/--
@isnad1 id=eq.0h3v.s11.f517b68b0bd3 from=translated src=- shape=5cc29f4e vocab=98130160
-/
lemma pullback_yGen (g : AffAut W) : pullback W g (yGen W) = yOf (g.act _ (genericPoint W)) :=
  liftFF_yGen _ _ _ _

lemma eq_pullback_of (g : AffAut W) {φ : funField W →ₐ[k] funField W}
    (h : Point.map φ (genericPoint W) = g.act _ (genericPoint W)) : φ = pullback W g :=
  algHom_ext_of_map_genericPoint (by rw [h, map_pullback_genericPoint])

/--
@isnad1 id=eq.0h4v.s11.13c7a9756d71 from=translated src=- shape=35483417 vocab=071b511f
-/
lemma pullback_mul (g h : AffAut W) :
    pullback W (g * h) = (pullback W h).comp (pullback W g) := by
  symm
  apply eq_pullback_of
  rw [← Point.map_map, map_pullback_genericPoint, AffAut.map_act, map_pullback_genericPoint,
    AffAut.act_mul]

/--
@isnad1 id=eq.0h2v.s10.73cdddeeb450 from=translated src=- shape=11072b1a vocab=f00d1881
-/
lemma pullback_one : pullback W 1 = AlgHom.id k (funField W) := by
  symm
  apply eq_pullback_of
  rw [AffAut.act_one]
  rfl

/-- The pullback along `g` as a `k`-algebra automorphism of `k(W)`. -/
def pullbackEquiv (g : AffAut W) : funField W ≃ₐ[k] funField W :=
  AlgEquiv.ofAlgHom (pullback W g) (pullback W g⁻¹)
    (by rw [← pullback_mul, inv_mul_cancel, pullback_one])
    (by rw [← pullback_mul, mul_inv_cancel, pullback_one])

/--
@isnad1 id=eq.0h4v.s11.042796fffa47 from=translated src=- shape=959b6bd1 vocab=0f053ee7
-/
@[simp] lemma pullbackEquiv_apply (g : AffAut W) (f : funField W) :
    pullbackEquiv W g f = pullback W g f := rfl

/-- The left action of affine automorphisms on the function field: `g • f = f ∘ g⁻¹`. -/
instance : MulSemiringAction (AffAut W) (funField W) where
  smul g f := pullback W g⁻¹ f
  one_smul f := by
    change pullback W 1⁻¹ f = f
    rw [inv_one, pullback_one]
    rfl
  mul_smul g h f := by
    change pullback W (g * h)⁻¹ f = pullback W g⁻¹ (pullback W h⁻¹ f)
    rw [mul_inv_rev, pullback_mul]
    rfl
  smul_zero g := map_zero (pullback W g⁻¹)
  smul_add g := map_add (pullback W g⁻¹)
  smul_one g := map_one (pullback W g⁻¹)
  smul_mul g := map_mul (pullback W g⁻¹)

/--
@isnad1 id=eq.0h4v.s11.ddf80ab79324 from=translated src=- shape=66697f6c vocab=a73e3100
-/
lemma smul_funField_def (g : AffAut W) (f : funField W) : g • f = pullback W g⁻¹ f := rfl

instance : SMulCommClass (AffAut W) k (funField W) :=
  ⟨fun g c f => by simp only [smul_funField_def, map_smul]⟩

end Pullback

end

end TemperedFundamentalGroups.Orbicurve
