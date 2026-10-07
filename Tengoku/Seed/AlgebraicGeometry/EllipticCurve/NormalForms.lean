/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.VariableChange
public import Tengoku.Seed.Algebra.CharP.Defs

/-!

# Some normal forms of elliptic curves

This file defines some normal forms of Weierstrass equations of elliptic curves.

## Main definitions and results

The following normal forms are in [silverman2009], section III.1, page 42.

- `WeierstrassCurve.IsCharNeTwoNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² = X³ + a₂X² + a₄X + a₆`. It is the normal form of characteristic ≠ 2.

  If 2 is invertible in the ring (for example, if it is a field of characteristic ≠ 2),
  then for any `WeierstrassCurve` there exists a change of variables which will change
  it into such normal form (`WeierstrassCurve.exists_variableChange_isCharNeTwoNF`).
  See also `WeierstrassCurve.toCharNeTwoNF` and `WeierstrassCurve.toCharNeTwoNF_spec`.

The following normal forms are in [silverman2009], Appendix A, Proposition 1.1.

- `WeierstrassCurve.IsShortNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² = X³ + a₄X + a₆`. It is the normal form of characteristic ≠ 2 or 3, and
  also the normal form of characteristic = 3 and j = 0.

  If 2 and 3 are invertible in the ring (for example, if it is a field of characteristic ≠ 2 or 3),
  then for any `WeierstrassCurve` there exists a change of variables which will change
  it into such normal form (`WeierstrassCurve.exists_variableChange_isShortNF`).
  See also `WeierstrassCurve.toShortNF` and `WeierstrassCurve.toShortNF_spec`.

  If the ring is of characteristic = 3, then for any `WeierstrassCurve` with `b₂ = 0` (for an
  elliptic curve, this is equivalent to j = 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toShortNFOfCharThree`
  and `WeierstrassCurve.toShortNFOfCharThree_spec`).

- `WeierstrassCurve.IsCharThreeJNeZeroNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² = X³ + a₂X² + a₆`. It is the normal form of characteristic = 3 and j ≠ 0.

  If the field is of characteristic = 3, then for any `WeierstrassCurve` with `b₂ ≠ 0` (for an
  elliptic curve, this is equivalent to j ≠ 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toCharThreeNF`
  and `WeierstrassCurve.toCharThreeNF_spec_of_b₂_ne_zero`).

- `WeierstrassCurve.IsCharThreeNF` is the combination of the above two, that is, asserts that
  a `WeierstrassCurve` is of form `Y² = X³ + a₂X² + a₆` or `Y² = X³ + a₄X + a₆`.
  It is the normal form of characteristic = 3.

  If the field is of characteristic = 3, then for any `WeierstrassCurve` there exists a change of
  variables which will change it into such normal form
  (`WeierstrassCurve.exists_variableChange_isCharThreeNF`).
  See also `WeierstrassCurve.toCharThreeNF` and `WeierstrassCurve.toCharThreeNF_spec`.

- `WeierstrassCurve.IsCharTwoJEqZeroNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² + a₃Y = X³ + a₄X + a₆`. It is the normal form of characteristic = 2 and j = 0.

  If the ring is of characteristic = 2, then for any `WeierstrassCurve` with `a₁ = 0` (for an
  elliptic curve, this is equivalent to j = 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toCharTwoJEqZeroNF`
  and `WeierstrassCurve.toCharTwoJEqZeroNF_spec`).

- `WeierstrassCurve.IsCharTwoJNeZeroNF` is a type class which asserts that a `WeierstrassCurve` is
  of form `Y² + XY = X³ + a₂X² + a₆`. It is the normal form of characteristic = 2 and j ≠ 0.

  If the field is of characteristic = 2, then for any `WeierstrassCurve` with `a₁ ≠ 0` (for an
  elliptic curve, this is equivalent to j ≠ 0), there exists a change of variables which will
  change it into such normal form (see `WeierstrassCurve.toCharTwoJNeZeroNF`
  and `WeierstrassCurve.toCharTwoJNeZeroNF_spec`).

- `WeierstrassCurve.IsCharTwoNF` is the combination of the above two, that is, asserts that
  a `WeierstrassCurve` is of form `Y² + XY = X³ + a₂X² + a₆` or
  `Y² + a₃Y = X³ + a₄X + a₆`. It is the normal form of characteristic = 2.

  If the field is of characteristic = 2, then for any `WeierstrassCurve` there exists a change of
  variables which will change it into such normal form
  (`WeierstrassCurve.exists_variableChange_isCharTwoNF`).
  See also `WeierstrassCurve.toCharTwoNF` and `WeierstrassCurve.toCharTwoNF_spec`.

## References

* [J Silverman, *The Arithmetic of Elliptic Curves*][silverman2009]

## Tags

elliptic curve, weierstrass equation, normal form

-/

@[expose] public section

variable {R : Type*} [CommRing R] {F : Type*} [Field F] (W : WeierstrassCurve R)

namespace WeierstrassCurve

/-! ## Normal forms of characteristic ≠ 2 -/

/-- A `WeierstrassCurve` is in normal form of characteristic ≠ 2, if its `a₁, a₃ = 0`.
In other words it is `Y² = X³ + a₂X² + a₄X + a₆`. -/
@[mk_iff]
class IsCharNeTwoNF : Prop where
  a₁ : W.a₁ = 0
  a₃ : W.a₃ = 0

section Quantity

variable [W.IsCharNeTwoNF]

/--
@isnad1 id=eq.0h2v.s5.da807fa2e612 from=seed src=0 shape=2f86dcb3 vocab=6a5d129a
-/
@[simp]
theorem a₁_of_isCharNeTwoNF : W.a₁ = 0 := IsCharNeTwoNF.a₁

/--
@isnad1 id=eq.0h2v.s5.34e4e804754a from=seed src=0 shape=2f86dcb3 vocab=3b0a0011
-/
@[simp]
theorem a₃_of_isCharNeTwoNF : W.a₃ = 0 := IsCharNeTwoNF.a₃

/--
@isnad1 id=eq.0h2v.s5.4b32c71ba464 from=seed src=0 shape=4a8b4290 vocab=30c243b0
-/
@[simp]
theorem b₂_of_isCharNeTwoNF : W.b₂ = 4 * W.a₂ := by
  rw [b₂, a₁_of_isCharNeTwoNF]
  ring1

/--
@isnad1 id=eq.0h2v.s5.ad7839c64965 from=seed src=0 shape=4a8b4290 vocab=d4c3d6e4
-/
@[simp]
theorem b₄_of_isCharNeTwoNF : W.b₄ = 2 * W.a₄ := by
  rw [b₄, a₃_of_isCharNeTwoNF]
  ring1

/--
@isnad1 id=eq.0h2v.s5.6307c6022792 from=seed src=0 shape=4a8b4290 vocab=770ae4bd
-/
@[simp]
theorem b₆_of_isCharNeTwoNF : W.b₆ = 4 * W.a₆ := by
  rw [b₆, a₃_of_isCharNeTwoNF]
  ring1

/--
@isnad1 id=eq.0h2v.s6.7fc7f83d9a65 from=seed src=0 shape=717573d6 vocab=401348e0
-/
@[simp]
theorem b₈_of_isCharNeTwoNF : W.b₈ = 4 * W.a₂ * W.a₆ - W.a₄ ^ 2 := by
  rw [b₈, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  ring1

/--
@isnad1 id=eq.0h2v.s6.df5ffdb65a26 from=seed src=0 shape=6b334d24 vocab=1868cf73
-/
@[simp]
theorem c₄_of_isCharNeTwoNF : W.c₄ = 16 * W.a₂ ^ 2 - 48 * W.a₄ := by
  rw [c₄, b₂_of_isCharNeTwoNF, b₄_of_isCharNeTwoNF]
  ring1

/--
@isnad1 id=eq.0h2v.s7.e1fa82e4a60a from=seed src=0 shape=f3362d5d vocab=7b2d9a52
-/
@[simp]
theorem c₆_of_isCharNeTwoNF : W.c₆ = -64 * W.a₂ ^ 3 + 288 * W.a₂ * W.a₄ - 864 * W.a₆ := by
  rw [c₆, b₂_of_isCharNeTwoNF, b₄_of_isCharNeTwoNF, b₆_of_isCharNeTwoNF]
  ring1

/--
@isnad1 id=eq.0h2v.s8.9c4864260848 from=seed src=0 shape=55596395 vocab=4dcca088
-/
@[simp]
theorem Δ_of_isCharNeTwoNF : W.Δ = -64 * W.a₂ ^ 3 * W.a₆ + 16 * W.a₂ ^ 2 * W.a₄ ^ 2 - 64 * W.a₄ ^ 3
    - 432 * W.a₆ ^ 2 + 288 * W.a₂ * W.a₄ * W.a₆ := by
  rw [Δ, b₂_of_isCharNeTwoNF, b₄_of_isCharNeTwoNF, b₆_of_isCharNeTwoNF, b₈_of_isCharNeTwoNF]
  ring1

end Quantity

section VariableChange

variable [Invertible (2 : R)]

/-- There is an explicit change of variables of a `WeierstrassCurve` to
a normal form of characteristic ≠ 2, provided that 2 is invertible in the ring. -/
@[simps]
def toCharNeTwoNF : VariableChange R := ⟨1, 0, ⅟2 * -W.a₁, ⅟2 * -W.a₃⟩

/--
@isnad1 id=ischarne.0h2v.s6.dafad1b98e2e from=seed src=0 shape=f3c85080 vocab=7f01027a
-/
instance toCharNeTwoNF_spec : (W.toCharNeTwoNF • W).IsCharNeTwoNF := by
  constructor <;> simp [variableChange_a₁, variableChange_a₃]

/--
@isnad1 id=ex.0h2v.s6.902f970b874c from=seed src=0 shape=adc1bc54 vocab=a905ae8b
-/
theorem exists_variableChange_isCharNeTwoNF : ∃ C : VariableChange R, (C • W).IsCharNeTwoNF :=
  ⟨_, W.toCharNeTwoNF_spec⟩

end VariableChange

/-! ## Short normal form -/

/-- A `WeierstrassCurve` is in short normal form, if its `a₁, a₂, a₃ = 0`.
In other words it is `Y² = X³ + a₄X + a₆`.

This is the normal form of characteristic ≠ 2 or 3, and
also the normal form of characteristic = 3 and j = 0. -/
@[mk_iff]
class IsShortNF : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 0
  a₃ : W.a₃ = 0

section Quantity

variable [W.IsShortNF]

/--
@isnad1 id=ischarne.0h2v.s4.2041a0a57705 from=seed src=0 shape=93e860ac vocab=f55874df
-/
instance isCharNeTwoNF_of_isShortNF : W.IsCharNeTwoNF := ⟨IsShortNF.a₁, IsShortNF.a₃⟩

/--
@isnad1 id=eq.0h2v.s5.193a48b628ef from=seed src=0 shape=2f86dcb3 vocab=ace29739
-/
theorem a₁_of_isShortNF : W.a₁ = 0 := IsShortNF.a₁

/--
@isnad1 id=eq.0h2v.s5.bd5457920dd6 from=seed src=0 shape=2f86dcb3 vocab=fa3c94c2
-/
@[simp]
theorem a₂_of_isShortNF : W.a₂ = 0 := IsShortNF.a₂

/--
@isnad1 id=eq.0h2v.s5.5065d3ce5d72 from=seed src=0 shape=2f86dcb3 vocab=1d45125d
-/
theorem a₃_of_isShortNF : W.a₃ = 0 := IsShortNF.a₃

/--
@isnad1 id=eq.0h2v.s5.36c9cf9acfae from=seed src=0 shape=2f86dcb3 vocab=b32d474d
-/
theorem b₂_of_isShortNF : W.b₂ = 0 := by
  simp

/--
@isnad1 id=eq.0h2v.s5.12cd1def07ba from=seed src=0 shape=4a8b4290 vocab=43f0fc9d
-/
theorem b₄_of_isShortNF : W.b₄ = 2 * W.a₄ := W.b₄_of_isCharNeTwoNF

/--
@isnad1 id=eq.0h2v.s5.a5d0588778a6 from=seed src=0 shape=4a8b4290 vocab=8bc12347
-/
theorem b₆_of_isShortNF : W.b₆ = 4 * W.a₆ := W.b₆_of_isCharNeTwoNF

/--
@isnad1 id=eq.0h2v.s5.6d1d3714cff4 from=seed src=0 shape=45a2ce88 vocab=b45348a3
-/
theorem b₈_of_isShortNF : W.b₈ = -W.a₄ ^ 2 := by
  simp

/--
@isnad1 id=eq.0h2v.s6.4740192770c5 from=seed src=0 shape=787d882d vocab=f976d015
-/
theorem c₄_of_isShortNF : W.c₄ = -48 * W.a₄ := by
  simp

/--
@isnad1 id=eq.0h2v.s6.75a78f83f67e from=seed src=0 shape=787d882d vocab=c12fb590
-/
theorem c₆_of_isShortNF : W.c₆ = -864 * W.a₆ := by
  simp

/--
@isnad1 id=eq.0h2v.s7.f4cdc9710042 from=seed src=0 shape=ce1f572c vocab=0edad6ce
-/
theorem Δ_of_isShortNF : W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  rw [Δ_of_isCharNeTwoNF, a₂_of_isShortNF]
  ring1

variable [CharP R 3]

/--
@isnad1 id=eq.0h2v.s5.645084d52998 from=seed src=0 shape=e236ca59 vocab=898a5fec
-/
theorem b₄_of_isShortNF_of_char_three : W.b₄ = -W.a₄ := by
  rw [b₄_of_isShortNF]
  linear_combination W.a₄ * CharP.cast_eq_zero R 3

/--
@isnad1 id=eq.0h2v.s5.880174d10af1 from=seed src=0 shape=0015e8da vocab=2fdbf6ee
-/
theorem b₆_of_isShortNF_of_char_three : W.b₆ = W.a₆ := by
  rw [b₆_of_isShortNF]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

/--
@isnad1 id=eq.0h2v.s5.0d85989cec06 from=seed src=0 shape=dda2d81c vocab=d269e003
-/
theorem c₄_of_isShortNF_of_char_three : W.c₄ = 0 := by
  rw [c₄_of_isShortNF]
  linear_combination -16 * W.a₄ * CharP.cast_eq_zero R 3

/--
@isnad1 id=eq.0h2v.s5.c1b8b978c81b from=seed src=0 shape=dda2d81c vocab=115cf11a
-/
theorem c₆_of_isShortNF_of_char_three : W.c₆ = 0 := by
  rw [c₆_of_isShortNF]
  linear_combination -288 * W.a₆ * CharP.cast_eq_zero R 3

/--
@isnad1 id=eq.0h2v.s6.5845e5b56b39 from=seed src=0 shape=f51dc596 vocab=f55f666c
-/
theorem Δ_of_isShortNF_of_char_three : W.Δ = -W.a₄ ^ 3 := by
  rw [Δ_of_isShortNF]
  linear_combination (-21 * W.a₄ ^ 3 - 144 * W.a₆ ^ 2) * CharP.cast_eq_zero R 3

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsShortNF]

/--
@isnad1 id=eq.0h2v.s7.4a99293a2e1c from=seed src=0 shape=57497065 vocab=7ef3f789
-/
theorem j_of_isShortNF : W.j = 6912 * W.a₄ ^ 3 / (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) := by
  have h := W.Δ'.ne_zero
  rw [coe_Δ', Δ_of_isShortNF] at h
  rw [j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, coe_Δ',
    c₄_of_isShortNF, Δ_of_isShortNF, div_eq_div_iff h (right_ne_zero_of_mul h)]
  ring1

/--
@isnad1 id=eq.0h2v.s6.7bfa35ff5b20 from=seed src=0 shape=3908a880 vocab=9def223e
-/
@[simp]
theorem j_of_isShortNF_of_char_three [CharP F 3] : W.j = 0 := by
  rw [j, c₄_of_isShortNF_of_char_three]; simp

end Quantity

section VariableChange

variable [Invertible (2 : R)] [Invertible (3 : R)]

/-- There is an explicit change of variables of a `WeierstrassCurve` to
a short normal form, provided that 2 and 3 are invertible in the ring.
It is the composition of an explicit change of variables with `WeierstrassCurve.toCharNeTwoNF`. -/
def toShortNF : VariableChange R :=
  ⟨1, ⅟3 * -(W.toCharNeTwoNF • W).a₂, 0, 0⟩ * W.toCharNeTwoNF

/--
@isnad1 id=isshortn.0h2v.s6.caca8577c4eb from=seed src=0 shape=6b6db785 vocab=a9656585
-/
instance toShortNF_spec : (W.toShortNF • W).IsShortNF := by
  rw [toShortNF, mul_smul]
  constructor <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃]

/--
@isnad1 id=ex.0h2v.s6.7d5311b2dace from=seed src=0 shape=27e80dc5 vocab=f45d7122
-/
theorem exists_variableChange_isShortNF : ∃ C : VariableChange R, (C • W).IsShortNF :=
  ⟨_, W.toShortNF_spec⟩

end VariableChange

/-! ## Normal forms of characteristic = 3 and j ≠ 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 3 and j ≠ 0, if its
`a₁, a₃, a₄ = 0`. In other words it is `Y² = X³ + a₂X² + a₆`. -/
@[mk_iff]
class IsCharThreeJNeZeroNF : Prop where
  a₁ : W.a₁ = 0
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = 0

section Quantity

variable [W.IsCharThreeJNeZeroNF]

/--
@isnad1 id=ischarne.0h2v.s4.a72e80036150 from=seed src=0 shape=93e860ac vocab=33fa624e
-/
instance isCharNeTwoNF_of_isCharThreeJNeZeroNF : W.IsCharNeTwoNF :=
  ⟨IsCharThreeJNeZeroNF.a₁, IsCharThreeJNeZeroNF.a₃⟩

/--
@isnad1 id=eq.0h2v.s5.6954249c096c from=seed src=0 shape=2f86dcb3 vocab=37c3cf79
-/
theorem a₁_of_isCharThreeJNeZeroNF : W.a₁ = 0 := IsCharThreeJNeZeroNF.a₁

/--
@isnad1 id=eq.0h2v.s5.5bba926d3b79 from=seed src=0 shape=2f86dcb3 vocab=ca5059b5
-/
theorem a₃_of_isCharThreeJNeZeroNF : W.a₃ = 0 := IsCharThreeJNeZeroNF.a₃

/--
@isnad1 id=eq.0h2v.s5.3537cf5eaac1 from=seed src=0 shape=2f86dcb3 vocab=1b38fa41
-/
@[simp]
theorem a₄_of_isCharThreeJNeZeroNF : W.a₄ = 0 := IsCharThreeJNeZeroNF.a₄

/--
@isnad1 id=eq.0h2v.s5.b64f69f44a99 from=seed src=0 shape=4a8b4290 vocab=8373acea
-/
theorem b₂_of_isCharThreeJNeZeroNF : W.b₂ = 4 * W.a₂ := W.b₂_of_isCharNeTwoNF

/--
@isnad1 id=eq.0h2v.s5.3f6e76f00b35 from=seed src=0 shape=2f86dcb3 vocab=ce1fe45c
-/
theorem b₄_of_isCharThreeJNeZeroNF : W.b₄ = 0 := by
  simp

/--
@isnad1 id=eq.0h2v.s5.d241a70ff2a8 from=seed src=0 shape=4a8b4290 vocab=d98e2442
-/
theorem b₆_of_isCharThreeJNeZeroNF : W.b₆ = 4 * W.a₆ := W.b₆_of_isCharNeTwoNF

/--
@isnad1 id=eq.0h2v.s6.b67e62ab86b9 from=seed src=0 shape=0ee50f15 vocab=2512bed2
-/
theorem b₈_of_isCharThreeJNeZeroNF : W.b₈ = 4 * W.a₂ * W.a₆ := by
  simp

/--
@isnad1 id=eq.0h2v.s6.c9e3730c80c4 from=seed src=0 shape=23d4d626 vocab=0cb764ed
-/
theorem c₄_of_isCharThreeJNeZeroNF : W.c₄ = 16 * W.a₂ ^ 2 := by
  simp

/--
@isnad1 id=eq.0h2v.s7.98a2b872da76 from=seed src=0 shape=3f9e4ed5 vocab=9eb4a648
-/
theorem c₆_of_isCharThreeJNeZeroNF : W.c₆ = -64 * W.a₂ ^ 3 - 864 * W.a₆ := by
  simp

/--
@isnad1 id=eq.0h2v.s7.c853b17ff6d3 from=seed src=0 shape=c03ace6b vocab=785390ae
-/
theorem Δ_of_isCharThreeJNeZeroNF : W.Δ = -64 * W.a₂ ^ 3 * W.a₆ - 432 * W.a₆ ^ 2 := by
  simp

variable [CharP R 3]

/--
@isnad1 id=eq.0h2v.s5.78095cf21033 from=seed src=0 shape=0015e8da vocab=aa9b7233
-/
theorem b₂_of_isCharThreeJNeZeroNF_of_char_three : W.b₂ = W.a₂ := by
  rw [b₂_of_isCharThreeJNeZeroNF]
  linear_combination W.a₂ * CharP.cast_eq_zero R 3

/--
@isnad1 id=eq.0h2v.s5.9537d6f12ef2 from=seed src=0 shape=0015e8da vocab=f6c9ee90
-/
theorem b₆_of_isCharThreeJNeZeroNF_of_char_three : W.b₆ = W.a₆ := by
  rw [b₆_of_isCharThreeJNeZeroNF]
  linear_combination W.a₆ * CharP.cast_eq_zero R 3

/--
@isnad1 id=eq.0h2v.s5.4f6d4b7630e1 from=seed src=0 shape=7a322d6b vocab=661b6812
-/
theorem b₈_of_isCharThreeJNeZeroNF_of_char_three : W.b₈ = W.a₂ * W.a₆ := by
  rw [b₈_of_isCharThreeJNeZeroNF]
  linear_combination W.a₂ * W.a₆ * CharP.cast_eq_zero R 3

/--
@isnad1 id=eq.0h2v.s5.e9c099b1dca0 from=seed src=0 shape=2e1db007 vocab=1cf2e534
-/
theorem c₄_of_isCharThreeJNeZeroNF_of_char_three : W.c₄ = W.a₂ ^ 2 := by
  rw [c₄_of_isCharThreeJNeZeroNF]
  linear_combination 5 * W.a₂ ^ 2 * CharP.cast_eq_zero R 3

/--
@isnad1 id=eq.0h2v.s6.f2421600e771 from=seed src=0 shape=f51dc596 vocab=17782303
-/
theorem c₆_of_isCharThreeJNeZeroNF_of_char_three : W.c₆ = -W.a₂ ^ 3 := by
  rw [c₆_of_isCharThreeJNeZeroNF]
  linear_combination (-21 * W.a₂ ^ 3 - 288 * W.a₆) * CharP.cast_eq_zero R 3

/--
@isnad1 id=eq.0h2v.s6.b83c919fa2da from=seed src=0 shape=bec25670 vocab=7b26f380
-/
theorem Δ_of_isCharThreeJNeZeroNF_of_char_three : W.Δ = -W.a₂ ^ 3 * W.a₆ := by
  rw [Δ_of_isCharThreeJNeZeroNF]
  linear_combination (-21 * W.a₂ ^ 3 * W.a₆ - 144 * W.a₆ ^ 2) * CharP.cast_eq_zero R 3

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharThreeJNeZeroNF] [CharP F 3]

/--
@isnad1 id=eq.0h2v.s6.0cd2604eef94 from=seed src=0 shape=4f3be0d5 vocab=ae06323f
-/
@[simp]
theorem j_of_isCharThreeJNeZeroNF_of_char_three : W.j = -W.a₂ ^ 3 / W.a₆ := by
  have h := W.Δ'.ne_zero
  rw [coe_Δ', Δ_of_isCharThreeJNeZeroNF_of_char_three] at h
  rw [j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, coe_Δ',
    c₄_of_isCharThreeJNeZeroNF_of_char_three, Δ_of_isCharThreeJNeZeroNF_of_char_three,
    div_eq_div_iff h (right_ne_zero_of_mul h)]
  ring1

/--
@isnad1 id=ne.0h2v.s6.e897cebb0b6b from=seed src=0 shape=3908a880 vocab=bc4ff48d
-/
theorem j_ne_zero_of_isCharThreeJNeZeroNF_of_char_three : W.j ≠ 0 := by
  rw [j_of_isCharThreeJNeZeroNF_of_char_three, div_ne_zero_iff]
  have h := W.Δ'.ne_zero
  rwa [coe_Δ', Δ_of_isCharThreeJNeZeroNF_of_char_three, mul_ne_zero_iff] at h

end Quantity

/-! ## Normal forms of characteristic = 3 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 3, if it is
`Y² = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharThreeJNeZeroNF`) or
`Y² = X³ + a₄X + a₆` (`WeierstrassCurve.IsShortNF`). -/
class inductive IsCharThreeNF : Prop
| of_j_ne_zero [W.IsCharThreeJNeZeroNF] : IsCharThreeNF
| of_j_eq_zero [W.IsShortNF] : IsCharThreeNF

/--
@isnad1 id=ischarth.0h2v.s4.926f62213052 from=seed src=0 shape=93e860ac vocab=cee13674
-/
instance isCharThreeNF_of_isCharThreeJNeZeroNF [W.IsCharThreeJNeZeroNF] : W.IsCharThreeNF :=
  IsCharThreeNF.of_j_ne_zero

/--
@isnad1 id=ischarth.0h2v.s4.421555ef5368 from=seed src=0 shape=93e860ac vocab=984f6ace
-/
instance isCharThreeNF_of_isShortNF [W.IsShortNF] : W.IsCharThreeNF :=
  IsCharThreeNF.of_j_eq_zero

/--
@isnad1 id=ischarne.0h2v.s4.b485e1a80a97 from=seed src=0 shape=93e860ac vocab=75fc4858
-/
instance isCharNeTwoNF_of_isCharThreeNF [W.IsCharThreeNF] : W.IsCharNeTwoNF := by
  cases ‹W.IsCharThreeNF› <;> infer_instance

section VariableChange

variable [CharP R 3] [CharP F 3]

/-- For a `WeierstrassCurve` defined over a ring of characteristic = 3,
there is an explicit change of variables of it to `Y² = X³ + a₄X + a₆`
(`WeierstrassCurve.IsShortNF`) if its j = 0.
This is in fact given by `WeierstrassCurve.toCharNeTwoNF`. -/
def toShortNFOfCharThree : VariableChange R :=
  have h : (2 : R) * 2 = 1 := by linear_combination CharP.cast_eq_zero R 3
  letI : Invertible (2 : R) := ⟨2, h, h⟩
  W.toCharNeTwoNF

/--
@isnad1 id=eq.0h2v.s5.53db70604796 from=seed src=0 shape=a42df26c vocab=3e30d6a3
-/
lemma toShortNFOfCharThree_a₂ : (W.toShortNFOfCharThree • W).a₂ = W.b₂ := by
  simp_rw [toShortNFOfCharThree, toCharNeTwoNF, variableChange_a₂, inv_one, Units.val_one, b₂]
  linear_combination (-W.a₂ - W.a₁ ^ 2) * CharP.cast_eq_zero R 3

/--
@isnad1 id=isshortn.1h2v.s6.8f6bf121c7ba from=seed src=0 shape=74e4ed8b vocab=2c27a21b
-/
theorem toShortNFOfCharThree_spec (hb₂ : W.b₂ = 0) : (W.toShortNFOfCharThree • W).IsShortNF := by
  have h : (2 : R) * 2 = 1 := by linear_combination CharP.cast_eq_zero R 3
  let : Invertible (2 : R) := ⟨2, h, h⟩
  have H := W.toCharNeTwoNF_spec
  exact ⟨H.a₁, hb₂ ▸ W.toShortNFOfCharThree_a₂, H.a₃⟩

variable (W : WeierstrassCurve F)

/-- For a `WeierstrassCurve` defined over a field of characteristic = 3,
there is an explicit change of variables of it to `WeierstrassCurve.IsCharThreeNF`, that is,
`Y² = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharThreeJNeZeroNF`) or
`Y² = X³ + a₄X + a₆` (`WeierstrassCurve.IsShortNF`).
It is the composition of an explicit change of variables with
`WeierstrassCurve.toShortNFOfCharThree`. -/
def toCharThreeNF : VariableChange F :=
  ⟨1, (W.toShortNFOfCharThree • W).a₄ /
    (W.toShortNFOfCharThree • W).a₂, 0, 0⟩ * W.toShortNFOfCharThree

/--
@isnad1 id=ischarth.1h2v.s6.30f52add55d0 from=seed src=0 shape=0ae63402 vocab=fc43f7a9
-/
theorem toCharThreeNF_spec_of_b₂_ne_zero (hb₂ : W.b₂ ≠ 0) :
    (W.toCharThreeNF • W).IsCharThreeJNeZeroNF := by
  have h : (2 : F) * 2 = 1 := by linear_combination CharP.cast_eq_zero F 3
  let : Invertible (2 : F) := ⟨2, h, h⟩
  rw [toCharThreeNF, mul_smul]
  set W' := W.toShortNFOfCharThree • W
  have : W'.IsCharNeTwoNF := W.toCharNeTwoNF_spec
  constructor
  · simp [variableChange_a₁]
  · simp [variableChange_a₃]
  · have ha₂ : W'.a₂ ≠ 0 := W.toShortNFOfCharThree_a₂ ▸ hb₂
    simp [field, variableChange_a₄, -mul_eq_zero]
    linear_combination (W'.a₄ * W'.a₂ ^ 2 + W'.a₄ ^ 2) * CharP.cast_eq_zero F 3

/--
@isnad1 id=isshortn.1h2v.s6.d9c0cde2107c from=seed src=0 shape=0ae63402 vocab=30d6491f
-/
theorem toCharThreeNF_spec_of_b₂_eq_zero (hb₂ : W.b₂ = 0) : (W.toCharThreeNF • W).IsShortNF := by
  rw [toCharThreeNF, toShortNFOfCharThree_a₂, hb₂, div_zero, ← VariableChange.one_def, one_mul]
  exact W.toShortNFOfCharThree_spec hb₂

/--
@isnad1 id=ischarth.0h2v.s5.f2a7859675ec from=seed src=0 shape=5d16abe9 vocab=b802f2e4
-/
instance toCharThreeNF_spec : (W.toCharThreeNF • W).IsCharThreeNF := by
  by_cases hb₂ : W.b₂ = 0
  · have := W.toCharThreeNF_spec_of_b₂_eq_zero hb₂
    infer_instance
  · have := W.toCharThreeNF_spec_of_b₂_ne_zero hb₂
    infer_instance

/--
@isnad1 id=ex.0h2v.s6.1ddb7592613a from=seed src=0 shape=feb9ac51 vocab=ece261bf
-/
theorem exists_variableChange_isCharThreeNF : ∃ C : VariableChange F, (C • W).IsCharThreeNF :=
  ⟨_, W.toCharThreeNF_spec⟩

end VariableChange

/-! ## Normal forms of characteristic = 2 and j ≠ 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 2 and j ≠ 0, if its `a₁ = 1` and
`a₃, a₄ = 0`. In other words it is `Y² + XY = X³ + a₂X² + a₆`. -/
@[mk_iff]
class IsCharTwoJNeZeroNF : Prop where
  a₁ : W.a₁ = 1
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = 0

section Quantity

variable [W.IsCharTwoJNeZeroNF]

/--
@isnad1 id=eq.0h2v.s5.a937fdd47188 from=seed src=0 shape=2f86dcb3 vocab=81ebd77b
-/
@[simp]
theorem a₁_of_isCharTwoJNeZeroNF : W.a₁ = 1 := IsCharTwoJNeZeroNF.a₁

/--
@isnad1 id=eq.0h2v.s5.ff8fcad25f12 from=seed src=0 shape=2f86dcb3 vocab=64d59976
-/
@[simp]
theorem a₃_of_isCharTwoJNeZeroNF : W.a₃ = 0 := IsCharTwoJNeZeroNF.a₃

/--
@isnad1 id=eq.0h2v.s5.d57a63ce9a44 from=seed src=0 shape=2f86dcb3 vocab=09c14056
-/
@[simp]
theorem a₄_of_isCharTwoJNeZeroNF : W.a₄ = 0 := IsCharTwoJNeZeroNF.a₄

/--
@isnad1 id=eq.0h2v.s6.94af4d86bf3c from=seed src=0 shape=136d6233 vocab=9b5c5d6f
-/
@[simp]
theorem b₂_of_isCharTwoJNeZeroNF : W.b₂ = 1 + 4 * W.a₂ := by
  rw [b₂, a₁_of_isCharTwoJNeZeroNF]
  ring1

/--
@isnad1 id=eq.0h2v.s5.03bab436a021 from=seed src=0 shape=2f86dcb3 vocab=b4ed6452
-/
@[simp]
theorem b₄_of_isCharTwoJNeZeroNF : W.b₄ = 0 := by
  rw [b₄, a₃_of_isCharTwoJNeZeroNF, a₄_of_isCharTwoJNeZeroNF]
  ring1

/--
@isnad1 id=eq.0h2v.s5.7b4f21e82c97 from=seed src=0 shape=4a8b4290 vocab=5119ab88
-/
@[simp]
theorem b₆_of_isCharTwoJNeZeroNF : W.b₆ = 4 * W.a₆ := by
  rw [b₆, a₃_of_isCharTwoJNeZeroNF]
  ring1

/--
@isnad1 id=eq.0h2v.s6.206992b20eaa from=seed src=0 shape=a989320f vocab=36e8e08a
-/
@[simp]
theorem b₈_of_isCharTwoJNeZeroNF : W.b₈ = W.a₆ + 4 * W.a₂ * W.a₆ := by
  rw [b₈, a₁_of_isCharTwoJNeZeroNF, a₃_of_isCharTwoJNeZeroNF, a₄_of_isCharTwoJNeZeroNF]
  ring1

/--
@isnad1 id=eq.0h2v.s5.393063947711 from=seed src=0 shape=1c89acb4 vocab=d23c01e4
-/
@[simp]
theorem c₄_of_isCharTwoJNeZeroNF : W.c₄ = W.b₂ ^ 2 := by
  rw [c₄, b₄_of_isCharTwoJNeZeroNF]
  ring1

/--
@isnad1 id=eq.0h2v.s6.f1829d0f51ea from=seed src=0 shape=5ab3fffa vocab=15b21b89
-/
@[simp]
theorem c₆_of_isCharTwoJNeZeroNF : W.c₆ = -W.b₂ ^ 3 - 864 * W.a₆ := by
  rw [c₆, b₄_of_isCharTwoJNeZeroNF, b₆_of_isCharTwoJNeZeroNF]
  ring1

variable [CharP R 2]

/--
@isnad1 id=eq.0h2v.s5.385504d77223 from=seed src=0 shape=dda2d81c vocab=f69f8c59
-/
theorem b₂_of_isCharTwoJNeZeroNF_of_char_two : W.b₂ = 1 := by
  rw [b₂_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

/--
@isnad1 id=eq.0h2v.s5.58ea3eb3b27d from=seed src=0 shape=dda2d81c vocab=af86d3c2
-/
theorem b₆_of_isCharTwoJNeZeroNF_of_char_two : W.b₆ = 0 := by
  rw [b₆_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₆ * CharP.cast_eq_zero R 2

/--
@isnad1 id=eq.0h2v.s5.8c3ea034ec13 from=seed src=0 shape=0015e8da vocab=1f18a123
-/
theorem b₈_of_isCharTwoJNeZeroNF_of_char_two : W.b₈ = W.a₆ := by
  rw [b₈_of_isCharTwoJNeZeroNF]
  linear_combination 2 * W.a₂ * W.a₆ * CharP.cast_eq_zero R 2

/--
@isnad1 id=eq.0h2v.s5.842af1b48781 from=seed src=0 shape=dda2d81c vocab=3ad92245
-/
theorem c₄_of_isCharTwoJNeZeroNF_of_char_two : W.c₄ = 1 := by
  rw [c₄_of_isCharTwoJNeZeroNF, b₂_of_isCharTwoJNeZeroNF_of_char_two]
  ring1

/--
@isnad1 id=eq.0h2v.s5.a5c5276e1313 from=seed src=0 shape=dda2d81c vocab=1eedfa36
-/
theorem c₆_of_isCharTwoJNeZeroNF_of_char_two : W.c₆ = 1 := by
  rw [c₆_of_isCharTwoJNeZeroNF, b₂_of_isCharTwoJNeZeroNF_of_char_two]
  linear_combination (-1 - 432 * W.a₆) * CharP.cast_eq_zero R 2

/--
@isnad1 id=eq.0h2v.s5.5ea81b4d7e35 from=seed src=0 shape=0015e8da vocab=75b83b71
-/
@[simp]
theorem Δ_of_isCharTwoJNeZeroNF_of_char_two : W.Δ = W.a₆ := by
  rw [Δ, b₂_of_isCharTwoJNeZeroNF_of_char_two, b₄_of_isCharTwoJNeZeroNF,
    b₆_of_isCharTwoJNeZeroNF_of_char_two, b₈_of_isCharTwoJNeZeroNF_of_char_two]
  linear_combination -W.a₆ * CharP.cast_eq_zero R 2

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJNeZeroNF] [CharP F 2]

/--
@isnad1 id=eq.0h2v.s6.97716a777593 from=seed src=0 shape=d6820840 vocab=d766d88b
-/
@[simp]
theorem j_of_isCharTwoJNeZeroNF_of_char_two : W.j = 1 / W.a₆ := by
  rw [j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, coe_Δ',
    c₄_of_isCharTwoJNeZeroNF_of_char_two, Δ_of_isCharTwoJNeZeroNF_of_char_two, one_pow]

/--
@isnad1 id=ne.0h2v.s6.02b73df2d51a from=seed src=0 shape=3908a880 vocab=3fcc5b1d
-/
theorem j_ne_zero_of_isCharTwoJNeZeroNF_of_char_two : W.j ≠ 0 := by
  rw [j_of_isCharTwoJNeZeroNF_of_char_two, div_ne_zero_iff]
  have h := W.Δ'.ne_zero
  rw [coe_Δ', Δ_of_isCharTwoJNeZeroNF_of_char_two] at h
  exact ⟨one_ne_zero, h⟩

end Quantity

/-! ## Normal forms of characteristic = 2 and j = 0 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 2 and j = 0, if its `a₁, a₂ = 0`.
In other words it is `Y² + a₃Y = X³ + a₄X + a₆`. -/
@[mk_iff]
class IsCharTwoJEqZeroNF : Prop where
  a₁ : W.a₁ = 0
  a₂ : W.a₂ = 0

section Quantity

variable [W.IsCharTwoJEqZeroNF]

/--
@isnad1 id=eq.0h2v.s5.1bb991d5dcf5 from=seed src=0 shape=2f86dcb3 vocab=fc7176d2
-/
@[simp]
theorem a₁_of_isCharTwoJEqZeroNF : W.a₁ = 0 := IsCharTwoJEqZeroNF.a₁

/--
@isnad1 id=eq.0h2v.s5.c8b66a2f313e from=seed src=0 shape=2f86dcb3 vocab=ca6cea3c
-/
@[simp]
theorem a₂_of_isCharTwoJEqZeroNF : W.a₂ = 0 := IsCharTwoJEqZeroNF.a₂

/--
@isnad1 id=eq.0h2v.s5.856377e43f60 from=seed src=0 shape=2f86dcb3 vocab=3875acab
-/
@[simp]
theorem b₂_of_isCharTwoJEqZeroNF : W.b₂ = 0 := by
  rw [b₂, a₁_of_isCharTwoJEqZeroNF, a₂_of_isCharTwoJEqZeroNF]
  ring1

/--
@isnad1 id=eq.0h2v.s5.ce1ce3b6c8b8 from=seed src=0 shape=4a8b4290 vocab=cfa3368d
-/
@[simp]
theorem b₄_of_isCharTwoJEqZeroNF : W.b₄ = 2 * W.a₄ := by
  rw [b₄, a₁_of_isCharTwoJEqZeroNF]
  ring1

/--
@isnad1 id=eq.0h2v.s5.d676c1e89206 from=seed src=0 shape=45a2ce88 vocab=061d85d7
-/
@[simp]
theorem b₈_of_isCharTwoJEqZeroNF : W.b₈ = -W.a₄ ^ 2 := by
  rw [b₈, a₁_of_isCharTwoJEqZeroNF, a₂_of_isCharTwoJEqZeroNF]
  ring1

/--
@isnad1 id=eq.0h2v.s6.a282662bbdeb from=seed src=0 shape=787d882d vocab=951b7998
-/
@[simp]
theorem c₄_of_isCharTwoJEqZeroNF : W.c₄ = -48 * W.a₄ := by
  rw [c₄, b₂_of_isCharTwoJEqZeroNF, b₄_of_isCharTwoJEqZeroNF]
  ring1

/--
@isnad1 id=eq.0h2v.s6.3c6db296c560 from=seed src=0 shape=787d882d vocab=2c192bdc
-/
@[simp]
theorem c₆_of_isCharTwoJEqZeroNF : W.c₆ = -216 * W.b₆ := by
  rw [c₆, b₂_of_isCharTwoJEqZeroNF, b₄_of_isCharTwoJEqZeroNF]
  ring1

/--
@isnad1 id=eq.0h2v.s7.2c9a70eb2619 from=seed src=0 shape=c95f1eaf vocab=24ebf15a
-/
@[simp]
theorem Δ_of_isCharTwoJEqZeroNF : W.Δ = -(64 * W.a₄ ^ 3 + 27 * W.b₆ ^ 2) := by
  rw [Δ, b₂_of_isCharTwoJEqZeroNF, b₄_of_isCharTwoJEqZeroNF]
  ring1

variable [CharP R 2]

/--
@isnad1 id=eq.0h2v.s5.4200843885b4 from=seed src=0 shape=dda2d81c vocab=315d6635
-/
theorem b₄_of_isCharTwoJEqZeroNF_of_char_two : W.b₄ = 0 := by
  rw [b₄_of_isCharTwoJEqZeroNF]
  linear_combination W.a₄ * CharP.cast_eq_zero R 2

/--
@isnad1 id=eq.0h2v.s5.cf671266dc08 from=seed src=0 shape=2e1db007 vocab=401e3b98
-/
theorem b₈_of_isCharTwoJEqZeroNF_of_char_two : W.b₈ = W.a₄ ^ 2 := by
  rw [b₈_of_isCharTwoJEqZeroNF]
  linear_combination -W.a₄ ^ 2 * CharP.cast_eq_zero R 2

/--
@isnad1 id=eq.0h2v.s5.af4116ab78a4 from=seed src=0 shape=dda2d81c vocab=a267e82a
-/
theorem c₄_of_isCharTwoJEqZeroNF_of_char_two : W.c₄ = 0 := by
  rw [c₄_of_isCharTwoJEqZeroNF]
  linear_combination -24 * W.a₄ * CharP.cast_eq_zero R 2

/--
@isnad1 id=eq.0h2v.s5.0bbf7332b5de from=seed src=0 shape=dda2d81c vocab=7df714b4
-/
theorem c₆_of_isCharTwoJEqZeroNF_of_char_two : W.c₆ = 0 := by
  rw [c₆_of_isCharTwoJEqZeroNF]
  linear_combination -108 * W.b₆ * CharP.cast_eq_zero R 2

/--
@isnad1 id=eq.0h2v.s5.82c2fcabba57 from=seed src=0 shape=2e1db007 vocab=4292f71e
-/
theorem Δ_of_isCharTwoJEqZeroNF_of_char_two : W.Δ = W.a₃ ^ 4 := by
  rw [Δ_of_isCharTwoJEqZeroNF, b₆_of_char_two]
  linear_combination (-32 * W.a₄ ^ 3 - 14 * W.a₃ ^ 4) * CharP.cast_eq_zero R 2

variable (W : WeierstrassCurve F) [W.IsElliptic] [W.IsCharTwoJEqZeroNF]

/--
@isnad1 id=eq.0h2v.s7.a3c70d944139 from=seed src=0 shape=57497065 vocab=3ac0d6be
-/
theorem j_of_isCharTwoJEqZeroNF : W.j = 110592 * W.a₄ ^ 3 / (64 * W.a₄ ^ 3 + 27 * W.b₆ ^ 2) := by
  have h := W.Δ'.ne_zero
  rw [coe_Δ', Δ_of_isCharTwoJEqZeroNF] at h
  rw [j, Units.val_inv_eq_inv_val, ← div_eq_inv_mul, coe_Δ',
    c₄_of_isCharTwoJEqZeroNF, Δ_of_isCharTwoJEqZeroNF, div_eq_div_iff h (neg_ne_zero.1 h)]
  ring1

/--
@isnad1 id=eq.0h2v.s6.06010388b554 from=seed src=0 shape=3908a880 vocab=345f3865
-/
@[simp]
theorem j_of_isCharTwoJEqZeroNF_of_char_two [CharP F 2] : W.j = 0 := by
  rw [j, c₄_of_isCharTwoJEqZeroNF_of_char_two]; simp

end Quantity

/-! ## Normal forms of characteristic = 2 -/

/-- A `WeierstrassCurve` is in normal form of characteristic = 2, if it is
`Y² + XY = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharTwoJNeZeroNF`) or
`Y² + a₃Y = X³ + a₄X + a₆` (`WeierstrassCurve.IsCharTwoJEqZeroNF`). -/
class inductive IsCharTwoNF : Prop
| of_j_ne_zero [W.IsCharTwoJNeZeroNF] : IsCharTwoNF
| of_j_eq_zero [W.IsCharTwoJEqZeroNF] : IsCharTwoNF

/--
@isnad1 id=ischartw.0h2v.s4.1f4f77bdf7cf from=seed src=0 shape=93e860ac vocab=f98c8030
-/
instance isCharTwoNF_of_isCharTwoJNeZeroNF [W.IsCharTwoJNeZeroNF] : W.IsCharTwoNF :=
  IsCharTwoNF.of_j_ne_zero

/--
@isnad1 id=ischartw.0h2v.s4.68a586ce98c3 from=seed src=0 shape=93e860ac vocab=4d71fb68
-/
instance isCharTwoNF_of_isCharTwoJEqZeroNF [W.IsCharTwoJEqZeroNF] : W.IsCharTwoNF :=
  IsCharTwoNF.of_j_eq_zero

section VariableChange

variable [CharP R 2] [CharP F 2]

/-- For a `WeierstrassCurve` defined over a ring of characteristic = 2,
there is an explicit change of variables of it to `Y² + a₃Y = X³ + a₄X + a₆`
(`WeierstrassCurve.IsCharTwoJEqZeroNF`) if its j = 0. -/
def toCharTwoJEqZeroNF : VariableChange R := ⟨1, W.a₂, 0, 0⟩

/--
@isnad1 id=ischartw.1h2v.s6.136fd770ecbb from=seed src=0 shape=74e4ed8b vocab=d4db86f2
-/
theorem toCharTwoJEqZeroNF_spec (ha₁ : W.a₁ = 0) :
    (W.toCharTwoJEqZeroNF • W).IsCharTwoJEqZeroNF := by
  constructor
  · simp [toCharTwoJEqZeroNF, ha₁, variableChange_a₁]
  · simp_rw [toCharTwoJEqZeroNF, variableChange_a₂, inv_one, Units.val_one]
    linear_combination 2 * W.a₂ * CharP.cast_eq_zero R 2

variable (W : WeierstrassCurve F)

/-- For a `WeierstrassCurve` defined over a field of characteristic = 2,
there is an explicit change of variables of it to `Y² + XY = X³ + a₂X² + a₆`
(`WeierstrassCurve.IsCharTwoJNeZeroNF`) if its j ≠ 0. -/
def toCharTwoJNeZeroNF (W : WeierstrassCurve F) (ha₁ : W.a₁ ≠ 0) : VariableChange F :=
  ⟨Units.mk0 _ ha₁, W.a₃ / W.a₁, 0, (W.a₁ ^ 2 * W.a₄ + W.a₃ ^ 2) / W.a₁ ^ 3⟩

/--
@isnad1 id=ischartw.1h2v.s6.59d430aeafb0 from=seed src=0 shape=a1cc63e7 vocab=a3d9a821
-/
theorem toCharTwoJNeZeroNF_spec (ha₁ : W.a₁ ≠ 0) :
    (W.toCharTwoJNeZeroNF ha₁ • W).IsCharTwoJNeZeroNF := by
  constructor
  · simp [toCharTwoJNeZeroNF, ha₁, variableChange_a₁]
  · simp [field, toCharTwoJNeZeroNF, variableChange_a₃, -mul_eq_zero]
    linear_combination (W.a₃ * W.a₁ ^ 3 + W.a₁ ^ 2 * W.a₄ + W.a₃ ^ 2) * CharP.cast_eq_zero F 2
  · simp [field, toCharTwoJNeZeroNF, variableChange_a₄, -mul_eq_zero]
    linear_combination (W.a₃ ^ 2 + W.a₁ * W.a₃ * W.a₂) * CharP.cast_eq_zero F 2

/-- For a `WeierstrassCurve` defined over a field of characteristic = 2,
there is an explicit change of variables of it to `WeierstrassCurve.IsCharTwoNF`, that is,
`Y² + XY = X³ + a₂X² + a₆` (`WeierstrassCurve.IsCharTwoJNeZeroNF`) or
`Y² + a₃Y = X³ + a₄X + a₆` (`WeierstrassCurve.IsCharTwoJEqZeroNF`). -/
def toCharTwoNF [DecidableEq F] : VariableChange F :=
  if ha₁ : W.a₁ = 0 then W.toCharTwoJEqZeroNF else W.toCharTwoJNeZeroNF ha₁

/--
@isnad1 id=ischartw.0h2v.s5.fb51b4570218 from=seed src=0 shape=d5763655 vocab=1a013187
-/
instance toCharTwoNF_spec [DecidableEq F] : (W.toCharTwoNF • W).IsCharTwoNF := by
  by_cases ha₁ : W.a₁ = 0
  · rw [toCharTwoNF, dite_eq_left ha₁]
    have := W.toCharTwoJEqZeroNF_spec ha₁
    infer_instance
  · rw [toCharTwoNF, dite_eq_right ha₁]
    have := W.toCharTwoJNeZeroNF_spec ha₁
    infer_instance

/--
@isnad1 id=ex.0h2v.s6.8e191d49c318 from=seed src=0 shape=feb9ac51 vocab=d8b9919e
-/
theorem exists_variableChange_isCharTwoNF : ∃ C : VariableChange F, (C • W).IsCharTwoNF := by
  classical
  exact ⟨_, W.toCharTwoNF_spec⟩

end VariableChange

end WeierstrassCurve
