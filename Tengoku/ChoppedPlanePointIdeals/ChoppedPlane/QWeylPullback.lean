module

public import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-!
# Polynomial identities for the cubic rank-three witness

This file contains the explicit algebraic identities behind the quartic
pullback of the cyclic three-dimensional binary-polynomial module.  Every
statement is an identity in a commutative ring; the cubic relation is stated
as an equation rather than imported from geometry.
-/

namespace ChoppedPlane.QWeyl

variable {A : Type*} [CommRing A]

/-- First binary quartic in the cubic pullback.-/
def quarticU (u v : A) : A := u * (u ^ 3 + 2 * v ^ 3)

/-- Second binary quartic in the cubic pullback.-/
def quarticV (u v : A) : A := -v * (2 * u ^ 3 + v ^ 3)

/-- The third quartic, after adjoining a cubic root.-/
def quarticZ (u v z : A) : A := z * (u ^ 3 - v ^ 3)

/--
@isnad1 id=eq.0h3v.s7.2a233f2ccf42 from=translated src=- shape=6d092bc7 vocab=25d159da
-/
theorem quartic_binary_cubic (u v : A) :
    quarticU u v ^ 3 + quarticV u v ^ 3 =
      (u ^ 3 + v ^ 3) * (u ^ 3 - v ^ 3) ^ 3 := by
  unfold quarticU quarticV
  ring

/--
@isnad1 id=eq.1h4v.s7.a9c0acbabd57 from=translated src=- shape=a9e969b0 vocab=06cdedc1
-/
theorem quartic_preserves_cubic (u v z : A) (hz : z ^ 3 = u ^ 3 + v ^ 3) :
    quarticU u v ^ 3 + quarticV u v ^ 3 = quarticZ u v z ^ 3 := by
  rw [quartic_binary_cubic]
  unfold quarticZ
  rw [mul_pow, hz]

/-- These identities supply a right inverse for the quartic row on the
`u` chart, without using a projective no-common-zero argument.
@isnad1 id=eq.0h3v.s8.5e65b74f3bca from=translated src=- shape=9cbe3f7d vocab=014e35a3
-/
theorem quartic_bezout_u (u v : A) :
    (3 * u ^ 3 + 2 * v ^ 3) * quarticU u v +
      4 * u * v ^ 2 * quarticV u v = 3 * u ^ 7 := by
  unfold quarticU quarticV
  ring

/-- The corresponding identity on the `v` chart.
@isnad1 id=eq.0h3v.s8.eefb1fe8010f from=translated src=- shape=b15d24c7 vocab=4f88b79b
-/
theorem quartic_bezout_v (u v : A) :
    -4 * u ^ 2 * v * quarticU u v -
      (3 * v ^ 3 + 2 * u ^ 3) * quarticV u v = 3 * v ^ 7 := by
  unfold quarticU quarticV
  ring

/-- The first quadratic syzygy of the quartic row.
@isnad1 id=eq.0h4v.s7.74770ae24ef0 from=translated src=- shape=4f6a4ab9 vocab=f736fa7b
-/
theorem quartic_quadratic_syzygy_one (u v z : A) :
    quarticU u v * (v * z) + quarticV u v * (z * u) +
      quarticZ u v z * (u * v) = 0 := by
  unfold quarticU quarticV quarticZ
  ring

/-- The second quadratic syzygy, modulo the cubic equation.
@isnad1 id=eq.1h4v.s8.1ac0fa2121c0 from=translated src=- shape=e41b035b vocab=05ed1e88
-/
theorem quartic_quadratic_syzygy_two (u v z : A)
    (hz : z ^ 3 = u ^ 3 + v ^ 3) :
    quarticU u v * u ^ 2 + quarticV u v * v ^ 2 -
      quarticZ u v z * z ^ 2 = 0 := by
  unfold quarticU quarticV quarticZ
  calc
    _ = (u ^ 3 - v ^ 3) * (u ^ 3 + v ^ 3 - z ^ 3) := by ring
    _ = 0 := by rw [hz]; ring

/-- The first maximal minor of the two quadratic syzygies.
@isnad1 id=eq.1h4v.s8.282b4456ccbc from=translated src=- shape=b7dd9de5 vocab=13a21da8
-/
theorem quadratic_minor_u (u v z : A) (hz : z ^ 3 = u ^ 3 + v ^ 3) :
    (z * u) * (-z ^ 2) - (u * v) * v ^ 2 = -quarticU u v := by
  unfold quarticU
  calc
    _ = -u * z ^ 3 - u * v ^ 3 := by ring
    _ = _ := by rw [hz]; ring

/-- The second maximal minor.
@isnad1 id=eq.1h4v.s8.de9390a7aca5 from=translated src=- shape=df42df57 vocab=af1a9d17
-/
theorem quadratic_minor_v (u v z : A) (hz : z ^ 3 = u ^ 3 + v ^ 3) :
    (u * v) * u ^ 2 - (v * z) * (-z ^ 2) = -quarticV u v := by
  unfold quarticV
  calc
    _ = u ^ 3 * v + v * z ^ 3 := by ring
    _ = _ := by rw [hz]; ring

/-- The third maximal minor.
@isnad1 id=eq.0h4v.s7.97d6aeb60080 from=translated src=- shape=79d104ca vocab=fbb9e000
-/
theorem quadratic_minor_z (u v z : A) :
    (v * z) * v ^ 2 - (z * u) * u ^ 2 = -quarticZ u v z := by
  unfold quarticZ
  ring

/-- A root of `T²+T+1` is a cube root of unity.
@isnad1 id=eq.1h2v.s7.fca9c5180df3 from=translated src=- shape=0bb6bc7e vocab=fd68a3c8
-/
theorem cube_eq_one (q : A) (hq : q ^ 2 + q + 1 = 0) : q ^ 3 = 1 := by
  linear_combination (q - 1) * hq

/-- The quartic coefficient along one cyclic basis vector.
@isnad1 id=eq.0h3v.s6.bed99166e3f9 from=translated src=- shape=502cbeec vocab=25d159da
-/
theorem quartic_factor_zero (u v : A) :
    quarticU u v + quarticV u v = (u + v) * (u - v) ^ 3 := by
  unfold quarticU quarticV
  ring

/-- The quartic factorization for any cube root of unity.
@isnad1 id=eq.1h4v.s7.15c3c8d70e34 from=translated src=- shape=299f07c1 vocab=25d159da
-/
theorem quartic_factor_of_cube (u v q : A) (hq3 : q ^ 3 = 1) :
    quarticU u v + q * quarticV u v =
      (u + q * v) * (u - q * v) ^ 3 := by
  have hq4 : q ^ 4 = q := by
    calc
      q ^ 4 = q ^ 3 * q := by ring
      _ = q := by rw [hq3]; ring
  unfold quarticU quarticV
  ring_nf
  rw [hq3, hq4]
  ring

/-- The factorization along the second cyclic basis vector.
@isnad1 id=eq.1h4v.s7.701a34b4bd85 from=translated src=- shape=dd4eeb5d vocab=25d159da
-/
theorem quartic_factor_one (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    quarticU u v + q * quarticV u v =
      (u + q * v) * (u - q * v) ^ 3 :=
  quartic_factor_of_cube u v q (cube_eq_one q hq)

/-- The factorization along the third cyclic basis vector.
@isnad1 id=eq.1h4v.s8.1a6aa629c986 from=translated src=- shape=907ac1e6 vocab=25d159da
-/
theorem quartic_factor_two (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    quarticU u v + q ^ 2 * quarticV u v =
      (u + q ^ 2 * v) * (u - q ^ 2 * v) ^ 3 := by
  apply quartic_factor_of_cube
  rw [← pow_mul, show 2 * 3 = 3 * 2 from by omega, pow_mul,
    cube_eq_one q hq, one_pow]

/-- The factorization of the product of the three binary chart factors.
@isnad1 id=eq.1h4v.s8.4097bd17c270 from=translated src=- shape=1f63b45a vocab=9c1cdc1d
-/
theorem binary_cubic_factor (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    (u - v) * (u - q * v) * (u - q ^ 2 * v) = u ^ 3 - v ^ 3 := by
  have hq3 : q ^ 3 = 1 := cube_eq_one q hq
  calc
    _ = u ^ 3 - u ^ 2 * v * (q ^ 2 + q + 1) +
        u * v ^ 2 * (q ^ 3 + q ^ 2 + q) - q ^ 3 * v ^ 3 := by ring
    _ = _ := by
      rw [hq3]
      linear_combination (-u ^ 2 * v + u * v ^ 2) * hq

/-- First weight of the semilinear coefficient-module pullback.-/
def weightZero (u v q : A) : A := (u - v) ^ 2 * (u - q * v)

/-- Second weight of the semilinear coefficient-module pullback.-/
def weightOne (u v q : A) : A := (u - q * v) ^ 2 * (u - q ^ 2 * v)

/-- Third weight of the semilinear coefficient-module pullback.-/
def weightTwo (u v q : A) : A := (u - q ^ 2 * v) ^ 2 * (u - v)

/-- The first cyclic intertwining identity.
@isnad1 id=eq.1h4v.s8.8ab432483028 from=translated src=- shape=72fb5db4 vocab=e5e1bcaa
-/
theorem intertwiner_zero (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    (u + v) * (u ^ 3 - v ^ 3) * weightZero u v q =
      (quarticU u v + quarticV u v) * weightOne u v q := by
  rw [quartic_factor_zero, ← binary_cubic_factor u v q hq]
  unfold weightZero weightOne
  ring

/-- The second cyclic intertwining identity.
@isnad1 id=eq.1h4v.s8.104379611e56 from=translated src=- shape=5dfd5cdc vocab=b57070f1
-/
theorem intertwiner_one (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    (u + q * v) * (u ^ 3 - v ^ 3) * weightOne u v q =
      (quarticU u v + q * quarticV u v) * weightTwo u v q := by
  rw [quartic_factor_one u v q hq, ← binary_cubic_factor u v q hq]
  unfold weightOne weightTwo
  ring

/-- The third cyclic intertwining identity.
@isnad1 id=eq.1h4v.s8.4e0cbb60ad0a from=translated src=- shape=ede5bbf2 vocab=2390fa27
-/
theorem intertwiner_two (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    (u + q ^ 2 * v) * (u ^ 3 - v ^ 3) * weightTwo u v q =
      (quarticU u v + q ^ 2 * quarticV u v) * weightZero u v q := by
  rw [quartic_factor_two u v q hq, ← binary_cubic_factor u v q hq]
  unfold weightTwo weightZero
  ring

/-- Reverse cyclic identities for the binary-module dual, whose three
generators have degree two.
@isnad1 id=other.1h4v.s10.83abe3b7ebac from=translated src=- shape=a3544286 vocab=25d159da
-/
theorem dual_intertwiners (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    let d0 := u - v
    let d1 := u - q * v
    let d2 := u - q ^ 2 * v
    let f0 := quarticU u v + quarticV u v
    let f1 := quarticU u v + q * quarticV u v
    let f2 := quarticU u v + q ^ 2 * quarticV u v
    ((u + q ^ 2 * v) * (u ^ 3 - v ^ 3) * (d1 * d2 ^ 2) =
        f2 * (d0 * d1 ^ 2)) ∧
    ((u + v) * (u ^ 3 - v ^ 3) * (d2 * d0 ^ 2) =
        f0 * (d1 * d2 ^ 2)) ∧
    ((u + q * v) * (u ^ 3 - v ^ 3) * (d0 * d1 ^ 2) =
        f1 * (d2 * d0 ^ 2)) := by
  dsimp
  rw [quartic_factor_zero, quartic_factor_one u v q hq,
    quartic_factor_two u v q hq, ← binary_cubic_factor u v q hq]
  constructor
  · ring
  constructor <;> ring

/-- The shifted module with generator degrees `(0,0,1)` has cyclic
coefficients `(u+v,1,(u+q*v)*(u+q²*v))`.
@isnad1 id=other.1h4v.s10.db85529bb3f2 from=translated src=- shape=7f4889c9 vocab=25d159da
-/
theorem shifted_two_intertwiners (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    let d0 := u - v
    let d1 := u - q * v
    let d2 := u - q ^ 2 * v
    let f0 := quarticU u v + quarticV u v
    let f1 := quarticU u v + q * quarticV u v
    let f2 := quarticU u v + q ^ 2 * quarticV u v
    ((u + v) * (u ^ 3 - v ^ 3) * d0 ^ 2 = f0 * (d1 * d2)) ∧
    ((u ^ 3 - v ^ 3) * (d1 * d2) = d2 ^ 2 * d0 * d1 ^ 2) ∧
    ((u + q * v) * (u + q ^ 2 * v) * (u ^ 3 - v ^ 3) *
        (d2 ^ 2 * d0 * d1 ^ 2) = f1 * f2 * d0 ^ 2) := by
  dsimp
  rw [quartic_factor_zero, quartic_factor_one u v q hq,
    quartic_factor_two u v q hq, ← binary_cubic_factor u v q hq]
  constructor
  · ring
  constructor <;> ring

/-- The dual of the preceding shifted module has generator degrees
`(2,2,1)` and the reverse cyclic action.
@isnad1 id=other.1h4v.s10.da859d776143 from=translated src=- shape=ac807a36 vocab=25d159da
-/
theorem shifted_two_dual_intertwiners (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    let d0 := u - v
    let d1 := u - q * v
    let d2 := u - q ^ 2 * v
    let f0 := quarticU u v + quarticV u v
    let f1 := quarticU u v + q * quarticV u v
    let f2 := quarticU u v + q ^ 2 * quarticV u v
    ((u + q * v) * (u + q ^ 2 * v) * (u ^ 3 - v ^ 3) *
        (d1 ^ 2 * d2 ^ 2) = f1 * f2 * d0) ∧
    ((u + v) * (u ^ 3 - v ^ 3) * (d1 * d2 * d0 ^ 2) =
        f0 * (d1 ^ 2 * d2 ^ 2)) ∧
    ((u ^ 3 - v ^ 3) * d0 = d1 * d2 * d0 ^ 2) := by
  dsimp
  rw [quartic_factor_zero, quartic_factor_one u v q hq,
    quartic_factor_two u v q hq, ← binary_cubic_factor u v q hq]
  constructor
  · ring
  constructor <;> ring

/-- The shifted module with generator degrees `(0,1,1)` has cyclic
coefficients `(1,u+q*v,(u+v)*(u+q²*v))`.
@isnad1 id=other.1h4v.s10.ccab150deaaf from=translated src=- shape=cf13ed0a vocab=25d159da
-/
theorem shifted_one_intertwiners (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    let d0 := u - v
    let d1 := u - q * v
    let d2 := u - q ^ 2 * v
    let f0 := quarticU u v + quarticV u v
    let f1 := quarticU u v + q * quarticV u v
    let f2 := quarticU u v + q ^ 2 * quarticV u v
    ((u ^ 3 - v ^ 3) * d1 = d0 * d1 ^ 2 * d2) ∧
    ((u + q * v) * (u ^ 3 - v ^ 3) * (d0 * d1 ^ 2 * d2) =
        f1 * (d0 ^ 2 * d2 ^ 2)) ∧
    ((u + v) * (u + q ^ 2 * v) * (u ^ 3 - v ^ 3) *
        (d0 ^ 2 * d2 ^ 2) = f0 * f2 * d1) := by
  dsimp
  rw [quartic_factor_zero, quartic_factor_one u v q hq,
    quartic_factor_two u v q hq, ← binary_cubic_factor u v q hq]
  constructor
  · ring
  constructor <;> ring

/-- Its dual has generator degrees `(2,1,1)` and reverse cyclic action.
@isnad1 id=other.1h4v.s10.0c964c0285fe from=translated src=- shape=43a4f680 vocab=25d159da
-/
theorem shifted_one_dual_intertwiners (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    let d0 := u - v
    let d1 := u - q * v
    let d2 := u - q ^ 2 * v
    let f0 := quarticU u v + quarticV u v
    let f1 := quarticU u v + q * quarticV u v
    let f2 := quarticU u v + q ^ 2 * quarticV u v
    ((u + v) * (u + q ^ 2 * v) * (u ^ 3 - v ^ 3) *
        (d0 ^ 2 * d1 * d2 ^ 2) = f0 * f2 * d1 ^ 2) ∧
    ((u ^ 3 - v ^ 3) * (d0 * d2) = d0 ^ 2 * d1 * d2 ^ 2) ∧
    ((u + q * v) * (u ^ 3 - v ^ 3) * d1 ^ 2 = f1 * (d0 * d2)) := by
  dsimp
  rw [quartic_factor_zero, quartic_factor_one u v q hq,
    quartic_factor_two u v q hq, ← binary_cubic_factor u v q hq]
  constructor
  · ring
  constructor <;> ring

end ChoppedPlane.QWeyl
