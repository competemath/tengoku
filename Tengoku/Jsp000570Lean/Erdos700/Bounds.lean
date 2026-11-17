import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Universal polynomial inequalities for the four-prime criterion.
Generated using nonnegative substitutions; each identity and sign is checked
by Lean. These statements concern all parameters in the stated range. -/

namespace Erdos700.FourPrime.Bounds
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/--
@isnad1 id=lt.3h3v.s6.551c4b718794 from=translated src=- shape=0d8ffe28 vocab=3b732f86
-/
theorem c_at_least_9 (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < c - 8 := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : c - 8 = 8 * x + 3 * y + z + 1 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s7.44ef27f2f53b from=translated src=- shape=250d428f vocab=e94596d0
-/
theorem T1_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < 3 * a ^ 2 - 2 * a * (b + c) + b * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 3 * a ^ 2 - 2 * a * (b + c) + b * c = 5 * x ^ 2 + 9 * x * y + x * z + 11 * x + 3 * y ^ 2 + y * z + 10 * y + z + 6 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s7.008133c81e3f from=translated src=- shape=510e9bcb vocab=197ab3fc
-/
theorem T1_less_than_bc (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -3 * a ^ 2 + 2 * a * (b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -3 * a ^ 2 + 2 * a * (b + c) = 19 * x ^ 2 + 8 * x * y + 2 * x * z + 40 * x + 8 * y + 2 * z + 21 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.e5bcb8346aaf from=translated src=- shape=5864999a vocab=64f7d5e9
-/
theorem S1_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -3 * a + b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -3 * a + b + c = 8 * x + 4 * y + z + 9 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=le.3h3v.s6.9c93b5df38e9 from=translated src=- shape=975bf3f9 vocab=80f27b39
-/
theorem R_at_least_one (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 ≤ a - 3 * b + c - 1 := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a - 3 * b + c - 1 = z := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.98bdd0495fb1 from=translated src=- shape=2c136112 vocab=64f7d5e9
-/
theorem R_less_than_c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -a + 3 * b := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a + 3 * b = 8 * x + 3 * y + 8 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s7.51db46b90816 from=translated src=- shape=641943ff vocab=197ab3fc
-/
theorem B_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) = 19 * x ^ 2 + 15 * x * y + 5 * x * z + 43 * x + 3 * y ^ 2 + 2 * y * z + 17 * y + 5 * z + 24 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s7.03907d50b74a from=translated src=- shape=cbf3e663 vocab=197ab3fc
-/
theorem B_less_than_2bc (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -2 * a * b + 3 * b ^ 2 + 2 * b * c - c * (-a + 2 * b) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -2 * a * b + 3 * b ^ 2 + 2 * b * c - c * (-a + 2 * b) = 29 * x ^ 2 + 19 * x * y + x * z + 59 * x + 3 * y ^ 2 + 19 * y + z + 30 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s7.8d7b4ca156cf from=translated src=- shape=05bb8440 vocab=e94596d0
-/
theorem U_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < a * b + 3 * c ^ 2 - 2 * c * (a + b) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * b + 3 * c ^ 2 - 2 * c * (a + b) = 131 * x ^ 2 + 105 * x * y + 40 * x * z + 302 * x + 21 * y ^ 2 + 16 * y * z + 121 * y + 3 * z ^ 2 + 46 * z + 174 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s7.ee010427e2dc from=translated src=- shape=2456ca81 vocab=64f7d5e9
-/
theorem U_less_than_3c_squared (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -a * b + 2 * c * (a + b) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b + 2 * c * (a + b) = 61 * x ^ 2 + 39 * x * y + 8 * x * z + 130 * x + 6 * y ^ 2 + 2 * y * z + 41 * y + 8 * z + 69 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.864249b0e979 from=translated src=- shape=99cc027a vocab=64f7d5e9
-/
theorem c_greater_than_a_plus_b (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -a - b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a - b + c = 4 * x + 2 * y + z + 5 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.c74c67359a56 from=translated src=- shape=877fabc3 vocab=e94596d0
-/
theorem L_less_c_squared (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < c ^ 2 - b * (b - a) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : c ^ 2 - b * (b - a) = 58 * x ^ 2 + 43 * x * y + 16 * x * z + 132 * x + 8 * y ^ 2 + 6 * y * z + 49 * y + z ^ 2 + 18 * z + 75 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s8.a96ae06e7945 from=translated src=- shape=ff3ef685 vocab=197ab3fc
-/
theorem p1_to_p2_h0_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) - (-2 * a + 2 * b) * (a - 3 * b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 2 * a * b - 3 * b ^ 2 + c * (-a + 2 * b) - (-2 * a + 2 * b) * (a - 3 * b + c) = 19 * x ^ 2 + 15 * x * y + x * z + 39 * x + 3 * y ^ 2 + 15 * y + z + 20 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s7.6e5187b53c94 from=translated src=- shape=231d3f4d vocab=64f7d5e9
-/
theorem p1_to_p3_low_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < (-a + c) * (3 * a - 2 * b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : (-a + c) * (3 * a - 2 * b + c) = 35 * x ^ 2 + 22 * x * y + 12 * x * z + 82 * x + 3 * y ^ 2 + 4 * y * z + 26 * y + z ^ 2 + 14 * z + 48 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s7.94cc74785909 from=translated src=- shape=73123250 vocab=64f7d5e9
-/
theorem p0_to_p3_low_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -a * b * c + c * (-a + c) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b * c + c * (-a + c) * (-b + c) = 256 * x ^ 3 + 320 * x ^ 2 * y + 128 * x ^ 2 * z + 896 * x ^ 2 + 132 * x * y ^ 2 + 104 * x * y * z + 744 * x * y + 20 * x * z ^ 2 + 296 * x * z + 1044 * x + 18 * y ^ 3 + 21 * y ^ 2 * z + 153 * y ^ 2 + 8 * y * z ^ 2 + 120 * y * z + 432 * y + z ^ 3 + 23 * z ^ 2 + 171 * z + 405 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s7.2fb692c29e69 from=translated src=- shape=703a6cb0 vocab=64f7d5e9
-/
theorem p2_to_p3_low_gap (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -b * (-a + b) + c * (-a + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -b * (-a + b) + c * (-a + c) = 50 * x ^ 2 + 40 * x * y + 15 * x * z + 115 * x + 8 * y ^ 2 + 6 * y * z + 46 * y + z ^ 2 + 17 * z + 66 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.71e9721b216c from=translated src=- shape=01d09498 vocab=64f7d5e9
-/
theorem a_less_b (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -a + b := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a + b = 2 * x + y + 2 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.234a6960f92e from=translated src=- shape=4802c21d vocab=64f7d5e9
-/
theorem b_less_c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -b + c = 5 * x + 2 * y + z + 6 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.57925570ce4e from=translated src=- shape=3e5579b1 vocab=3b732f86
-/
theorem S_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < a + b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a + b + c = 12 * x + 4 * y + z + 13 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.da247290198e from=translated src=- shape=75dcc110 vocab=64f7d5e9
-/
theorem S_less_3c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -a - b + 2 * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a - b + 2 * c = 12 * x + 5 * y + 2 * z + 14 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.d25795cb49e3 from=translated src=- shape=6b891ca5 vocab=3b732f86
-/
theorem T_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < a * b + a * c + b * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * b + a * c + b * c = 35 * x ^ 2 + 21 * x * y + 4 * x * z + 74 * x + 3 * y ^ 2 + y * z + 22 * y + 4 * z + 39 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s7.b75c55d1cd47 from=translated src=- shape=729fab22 vocab=197ab3fc
-/
theorem T_less_3c_squared (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -a * b - a * c - b * c + 3 * c ^ 2 := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b - a * c - b * c + 3 * c ^ 2 = 157 * x ^ 2 + 123 * x * y + 44 * x * z + 358 * x + 24 * y ^ 2 + 17 * y * z + 140 * y + 3 * z ^ 2 + 50 * z + 204 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.750c27a5e4c3 from=translated src=- shape=1e4ebead vocab=3b732f86
-/
theorem Z_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < a * b * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * b * c = 24 * x ^ 3 + 17 * x ^ 2 * y + 3 * x ^ 2 * z + 75 * x ^ 2 + 3 * x * y ^ 2 + x * y * z + 35 * x * y + 6 * x * z + 78 * x + 3 * y ^ 2 + y * z + 18 * y + 3 * z + 27 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.c1f59a03feb0 from=translated src=- shape=bce4558e vocab=197ab3fc
-/
theorem Z_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -a * b * c + c ^ 3 := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * b * c + c ^ 3 = 488 * x ^ 3 + 559 * x ^ 2 * y + 189 * x ^ 2 * z + 1653 * x ^ 2 + 213 * x * y ^ 2 + 143 * x * y * z + 1261 * x * y + 24 * x * z ^ 2 + 426 * x * z + 1866 * x + 27 * y ^ 3 + 27 * y ^ 2 * z + 240 * y ^ 2 + 9 * y * z ^ 2 + 161 * y * z + 711 * y + z ^ 3 + 27 * z ^ 2 + 240 * z + 702 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.0130d27c09f2 from=translated src=- shape=dee72ed3 vocab=3b732f86
-/
theorem S1_less_2c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < 3 * a - b + c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : 3 * a - b + c = 8 * x + 2 * y + z + 9 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.efedcf92ab0a from=translated src=- shape=75dcc110 vocab=64f7d5e9
-/
theorem D_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -a - b + 3 * c := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a - b + 3 * c = 20 * x + 8 * y + 3 * z + 23 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.4719e8d77121 from=translated src=- shape=38e77c6f vocab=3b732f86
-/
theorem D_less_3c (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < a + b := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a + b = 4 * x + y + 4 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.5925fc43a2a1 from=translated src=- shape=cb5d5245 vocab=64f7d5e9
-/
theorem A_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < a * (-a + b) * (-a + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : a * (-a + b) * (-a + c) = 14 * x ^ 3 + 13 * x ^ 2 * y + 2 * x ^ 2 * z + 44 * x ^ 2 + 3 * x * y ^ 2 + x * y * z + 27 * x * y + 4 * x * z + 46 * x + 3 * y ^ 2 + y * z + 14 * y + 2 * z + 16 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s7.103deccb240a from=translated src=- shape=bf9bbbab vocab=197ab3fc
-/
theorem A_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -a * (-a + b) * (-a + c) + c ^ 3 := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -a * (-a + b) * (-a + c) + c ^ 3 = 498 * x ^ 3 + 563 * x ^ 2 * y + 190 * x ^ 2 * z + 1684 * x ^ 2 + 213 * x * y ^ 2 + 143 * x * y * z + 1269 * x * y + 24 * x * z ^ 2 + 428 * x * z + 1898 * x + 27 * y ^ 3 + 27 * y ^ 2 * z + 240 * y ^ 2 + 9 * y * z ^ 2 + 161 * y * z + 715 * y + z ^ 3 + 27 * z ^ 2 + 241 * z + 713 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.9c3d8c2b2c7a from=translated src=- shape=e24c607c vocab=64f7d5e9
-/
theorem C_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < b * (-a + b) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : b * (-a + b) * (-b + c) = 30 * x ^ 3 + 37 * x ^ 2 * y + 6 * x ^ 2 * z + 96 * x ^ 2 + 15 * x * y ^ 2 + 5 * x * y * z + 79 * x * y + 12 * x * z + 102 * x + 2 * y ^ 3 + y ^ 2 * z + 16 * y ^ 2 + 5 * y * z + 42 * y + 6 * z + 36 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s7.5fcf20456408 from=translated src=- shape=703a717b vocab=197ab3fc
-/
theorem C_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < -b * (-a + b) * (-b + c) + c ^ 3 := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : -b * (-a + b) * (-b + c) + c ^ 3 = 482 * x ^ 3 + 539 * x ^ 2 * y + 186 * x ^ 2 * z + 1632 * x ^ 2 + 201 * x * y ^ 2 + 139 * x * y * z + 1217 * x * y + 24 * x * z ^ 2 + 420 * x * z + 1842 * x + 25 * y ^ 3 + 26 * y ^ 2 * z + 227 * y ^ 2 + 9 * y * z ^ 2 + 157 * y * z + 687 * y + z ^ 3 + 27 * z ^ 2 + 237 * z + 693 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s6.f08b5d969c29 from=translated src=- shape=36c67094 vocab=64f7d5e9
-/
theorem F_positive (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < c * (-a + c) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : c * (-a + c) * (-b + c) = 280 * x ^ 3 + 337 * x ^ 2 * y + 131 * x ^ 2 * z + 971 * x ^ 2 + 135 * x * y ^ 2 + 105 * x * y * z + 779 * x * y + 20 * x * z ^ 2 + 302 * x * z + 1122 * x + 18 * y ^ 3 + 21 * y ^ 2 * z + 156 * y ^ 2 + 8 * y * z ^ 2 + 121 * y * z + 450 * y + z ^ 3 + 23 * z ^ 2 + 174 * z + 432 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=lt.3h3v.s7.ab37ebe7eafd from=translated src=- shape=1eb363f6 vocab=197ab3fc
-/
theorem F_less_c_cubed (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 3*a ≤ b) (hc : 3*b-a+1 ≤ c) :
    0 < c ^ 3 - c * (-a + c) * (-b + c) := by
  let x := a-1
  let y := b-3*a
  let z := c-(3*b-a+1)
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hz : 0 ≤ z := by dsimp [z]; linarith
  have hid : c ^ 3 - c * (-a + c) * (-b + c) = 232 * x ^ 3 + 239 * x ^ 2 * y + 61 * x ^ 2 * z + 757 * x ^ 2 + 81 * x * y ^ 2 + 39 * x * y * z + 517 * x * y + 4 * x * z ^ 2 + 130 * x * z + 822 * x + 9 * y ^ 3 + 6 * y ^ 2 * z + 87 * y ^ 2 + y * z ^ 2 + 41 * y * z + 279 * y + 4 * z ^ 2 + 69 * z + 297 := by
    dsimp [x, y, z]
    ring
  rw [hid]
  positivity

/--
@isnad1 id=and.2h2v.s7.c4e066c303e6 from=translated src=- shape=3833ede0 vocab=0dd99490
-/
theorem large_base_thresholds (c p : ℤ) (hc : 2 ≤ c) (hp : 12*c^3 ≤ p) :
    11*c^3 < p ∧ 13*c^2 < p ∧ 7*c^3 < p := by
  have hpos : 0 < c^3 := pow_pos (by linarith : 0 < c) 3
  have hsq : 0 < c^2 := pow_pos (by linarith : 0 < c) 2
  have h2 : 2*c^2 ≤ c^3 := by
    nlinarith only [mul_nonneg (by linarith : 0 ≤ c - 2) (sq_nonneg c)]
  constructor
  · nlinarith only [hpos, hp]
  constructor <;> nlinarith only [h2, hsq, hpos, hp]

end Erdos700.FourPrime.Bounds
