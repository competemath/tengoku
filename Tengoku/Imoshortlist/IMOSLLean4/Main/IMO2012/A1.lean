/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Tengoku

/-!
# IMO 2012 A1 (P4)

A triple $(a, b, c)$ of integers is called a *Heron triple* if
$$ a^2 + b^2 + c^2 = 2ab + 2bc + 2ca. $$
Find all functions $f : ℤ → ℤ$ such that $(f(a), f(b), f(c))$ is
  a Heron triple for any $a, b, c ∈ ℤ$ satisfying $a + b + c = 0$.

### Answer

They are precisely the functions of one of the following form:
$$ n ↦ cn^2, \quad
  n ↦ \begin{cases} c & \text{if } 2 ∤ n, \\ 0 & \text{if } 2 ∣ n, \end{cases} \quad
  n ↦ \begin{cases} c & \text{if } n ≡ 1, 3 \pmod{4}, \\
    4c & \text{if } n ≡ 2 \pmod{4}, \\ 0 & \text{if } n ≡ 0 \pmod{4}. \end{cases} $$

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2012SL.pdf).
Our implementation is slightly more complicated at the final step in the case where
  $f(2) = 4f(1)$ and $f(3) = 9f(1)$, but it works even when the range of the function
  is generalized to any integral domain (of characteristic not equal to $3$).
The difference is that $k(n - 1)^2 ≠ k(n - 3)^2$ is not always true this time,
  but $k(n - 1)^2 = k(n - 3)^2$ would imply either $k = 0$, $R$ has characteristic $2$,
  or $n = 2$ in $R$, and in all cases we still get $f(n + 1) = k(n + 1)^2$.

The same solution holds if the codomain is an integral domain of characteristic not $3$.
Thus will be reflected in our implementation.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A1

/-! ### Heron triples -/

/-- A triple `(a, b, c) ∈ R^3` is called a *Heron triple*
  if `a^2 + b^2 + c^2 = 2ab + 2bc + 2ca`. -/
def HeronTriple [CommSemiring R] (a b c : R) :=
  a ^ 2 + b ^ 2 + c ^ 2 = 2 * (a * b + b * c + c * a)

namespace HeronTriple

instance [CommSemiring R] [DecidableEq R] (a b c : R) : Decidable (HeronTriple a b c) :=
  decEq _ _

section

variable [CommSemiring R] {a b c : R} (h : HeronTriple a b c)
include h

/-- If `(a, b, c)` is a Heron triple, then `(b, c, a)` is a Heron triple.
@isnad1 id=herontri.1h4v.s4.0a2c0389ddd7 from=translated src=- shape=56a72084 vocab=b6c9d3ad
-/
theorem perm231 : HeronTriple b c a := by
  rw [HeronTriple, ← add_rotate, h, add_rotate]

/-- If `(a, b, c)` is a Heron triple, then `(c, a, b)` is a Heron triple.
@isnad1 id=herontri.1h4v.s4.e35a345aa8c3 from=translated src=- shape=3b87931e vocab=b6c9d3ad
-/
theorem perm312 : HeronTriple c a b :=
  h.perm231.perm231

/-- If `(a, b, c)` is a Heron triple, then `(b, a, c)` is a Heron triple.
@isnad1 id=herontri.1h4v.s4.2b58436cc698 from=translated src=- shape=c9d3a1fb vocab=b6c9d3ad
-/
theorem perm213 : HeronTriple b a c := by
  rw [HeronTriple, add_comm (b ^ 2), h, add_right_comm, mul_comm a, mul_comm c, mul_comm b c]

/-- If `(a, b, c)` is a Heron triple, then `(c, b, a)` is a Heron triple.
@isnad1 id=herontri.1h4v.s4.7b54e0c8092f from=translated src=- shape=dc490b2b vocab=b6c9d3ad
-/
theorem perm321 : HeronTriple c b a :=
  h.perm231.perm213

/-- If `(a, b, c)` is a Heron triple, then `(a, c, b)` is a Heron triple.
@isnad1 id=herontri.1h4v.s4.e00aafb2036e from=translated src=- shape=d62196e8 vocab=b6c9d3ad
-/
theorem perm132 : HeronTriple a c b :=
  h.perm213.perm231

/-- If `(a, b, c)` is a Heron triple, then `(ra, rb, rc)` is a Heron triple for any `r`.
@isnad1 id=herontri.1h5v.s6.8d01ababaffd from=translated src=- shape=d34be024 vocab=5f554d86
-/
theorem mul_left (r : R) : HeronTriple (r * a) (r * b) (r * c) := by
  unfold HeronTriple
  iterate 3 rw [mul_pow, mul_mul_mul_comm r _ r]
  iterate 4 rw [← mul_add]
  rw [h, mul_left_comm, sq]

/-- If `(a, b, c)` is a Heron triple, then `(φ(a), φ(b), φ(c))` is a Heron triple,
  `φ : R → R₀` is a ring homomorphism to an arbitrary commutative semiring.
@isnad1 id=herontri.1h6v.s7.0110febb0c52 from=translated src=- shape=395b1918 vocab=8cac0cf5
-/
theorem RingHom_apply [CommSemiring R₀] (φ : R →+* R₀) : HeronTriple (φ a) (φ b) (φ c) := by
  simp_rw [HeronTriple, ← φ.map_pow, ← φ.map_mul, ← φ.map_add]
  rw [h, φ.map_mul, map_ofNat]

end

section

variable [CommRing R]

/-- An (asymmetric) alternative formulation of Heron triple.
@isnad1 id=iff.0h4v.s7.97b3923d1ad0 from=translated src=- shape=56ff9bce vocab=8cf47324
-/
theorem alt_def {a b c : R} : HeronTriple a b c ↔ (c - (a + b)) ^ 2 = 2 ^ 2 * a * b :=
  calc a ^ 2 + b ^ 2 + c ^ 2 = 2 * (a * b + b * c + c * a)
  _ ↔ c ^ 2 + (a + b) ^ 2 = 2 * (a * b + b * c + c * a) + 2 * a * b := by
    rw [add_sq', add_left_comm, ← add_assoc, add_left_inj]
  _ ↔ c ^ 2 + (a + b) ^ 2 = (2 + 2) * (a * b) + 2 * (c * (a + b)) := by
    apply Eq.congr_right; rw [add_assoc, mul_comm b, ← mul_add c,
      mul_add, add_comm b, add_right_comm, mul_assoc, ← add_mul]
  _ ↔ (c - (a + b)) ^ 2 = 2 ^ 2 * a * b := by
    rw [← two_mul, ← sq, sub_sq', sub_eq_iff_eq_add, ← mul_assoc, ← mul_assoc]

/-- The triple `(a^2, b^2, c^2)` is a Heron triple if `a + b + c = 0`.
@isnad1 id=herontri.1h4v.s7.87f82b6e519a from=translated src=- shape=8ceede05 vocab=478040bf
-/
theorem squares_of_add_eq_zero {a b c : R} (h : a + b + c = 0) :
    HeronTriple (a ^ 2) (b ^ 2) (c ^ 2) := by
  rw [eq_neg_of_add_eq_zero_right h, neg_sq, alt_def,
    add_sq', add_sub_cancel_left, mul_pow, mul_pow]

end

section

variable [CommRing R] [NoZeroDivisors R]

/-- If `char(R) ≠ 3` and `(x, x, x)` is a Heron triple, then `x = 0`. -/
theorem eq_zero_of_const (hR : (3 : R) ≠ 0) {c : R} (hc : HeronTriple c c c) : c = 0 := by
  rwa [HeronTriple, sq, two_mul, right_eq_add, ← two_mul, ← add_one_mul,
    mul_eq_zero, two_add_one_eq_three, or_iff_right hR, mul_self_eq_zero] at hc

/-- The triple `(x, y, 0)` is a Heron triple if and only if `x = y`.
@isnad1 id=iff.0h3v.s5.a3a2d8744868 from=translated src=- shape=509ce428 vocab=79cd081c
-/
theorem iff_eq_of_zero_right {x y : R} : HeronTriple x y 0 ↔ x = y := by
  rw [HeronTriple, sq 0, mul_zero, add_zero, mul_zero, add_zero, zero_mul,
    add_zero, ← mul_assoc, ← sub_eq_zero, ← sub_sq', sq_eq_zero_iff, sub_eq_zero]

/-- The triple `(rx^2, ry^2, z)` is a Heron triple if and only if
  either `z = r(x + y)^2` or `z = r(x - y)^2`.
@isnad1 id=iff.0h5v.s7.71c9704364e3 from=translated src=- shape=2198d0bb vocab=58969948
-/
theorem iff_eq_mul_add_or_sub_sq {r x y z : R} :
    HeronTriple (r * x ^ 2) (r * y ^ 2) z ↔ z = r * (x + y) ^ 2 ∨ z = r * (x - y) ^ 2 := by
  rw [alt_def, ← mul_add, mul_assoc, mul_mul_mul_comm, ← sq, ← mul_pow,
    ← mul_pow, ← mul_pow, mul_left_comm, ← mul_assoc,sq_eq_sq_iff_eq_or_eq_neg]
  apply or_congr
  · rw [add_sq', sub_eq_iff_eq_add', mul_assoc, ← mul_add, mul_assoc]
  · rw [sub_sq', sub_eq_iff_eq_add', mul_assoc, ← sub_eq_add_neg, ← mul_sub, mul_assoc]

/-- The triple `(r, r, z)` is a Heron triple if and only if `z = 4r` or `z = 0`.
@isnad1 id=iff.0h3v.s6.d9463d607536 from=translated src=- shape=18d8f27a vocab=61230039
-/
theorem iff_of_left_mid_eq {r z : R} : HeronTriple r r z ↔ z = r * 2 ^ 2 ∨ z = 0 := calc
  _ ↔ HeronTriple (r * 1 ^ 2) (r * 1 ^ 2) z := by rw [one_pow, mul_one]
  _ ↔ z = r * (1 + 1) ^ 2 ∨ z = r * (1 - 1) ^ 2 := iff_eq_mul_add_or_sub_sq
  _ ↔ z = r * 2 ^ 2 ∨ z = 0 := by
    rw [one_add_one_eq_two, sub_self, zero_pow (Nat.succ_ne_zero 1), mul_zero]

end

end HeronTriple

/-! ### Start of the problem -/

open HeronTriple

/-- A function `f : G → R` is called *good* if `(f(a), f(b), f(c))` is
  a Heron triple whenever `a, b, c ∈ G` satisfies `a + b + c = 0`. -/
def good [AddZero G] [CommSemiring R] (f : G → R) :=
  ∀ a b c : G, a + b + c = 0 → HeronTriple (f a) (f b) (f c)

instance [DecidableEq G] [Fintype G] [AddZero G] [CommSemiring R] [DecidableEq R]
    (f : G → R) : Decidable (good f) :=
  Fintype.decidableForallFintype

/-- The square function is good.
@isnad1 id=good.0h1v.s5.b76b0d02022e from=translated src=- shape=efe18133 vocab=4ae6c9d3
-/
theorem sq_is_good [CommRing R] : good (λ r : R ↦ r ^ 2) :=
  λ _ _ _ ↦ squares_of_add_eq_zero

/-- The function `f : ZMod 2 → ℕ` defined by `0 ↦ 0, 1 ↦ 1` is good.
@isnad1 id=good.0h0v.s5.e36a8d0e4115 from=translated src=- shape=a4b7d570 vocab=27c0f582
-/
theorem ZMod2_01_is_good : good (![0, 1] : ZMod 2 → ℕ) := by
  decide

/-- The function `f : ZMod 4 → ℕ` defined by `0 ↦ 0, 1 ↦ 1, 2 ↦ 4, 3 ↦ 1` is good.
@isnad1 id=good.0h0v.s6.8695ab2aff42 from=translated src=- shape=80c96293 vocab=27c0f582
-/
theorem ZMod4_0141_is_good : good (![0, 1, 4, 1] : ZMod 4 → ℕ) := by
  decide

namespace good

/-- If `f : G → R` is good, then the function `rf : x ↦ rf(x)` is good for any `r : R`.
@isnad1 id=good.1h4v.s5.a2cbe1025d84 from=translated src=- shape=45484ba9 vocab=3dff5495
-/
theorem smul_left [AddZero G] [CommSemiring R]
    {f : G → R} (hf : good f) (r : R) : good (r • f) :=
  λ a b c h ↦ (hf a b c h).mul_left r

/-- If `f : G → R` is good and `φ : G₀ → G` is a group homomorphism, `f ∘ φ` is good.
@isnad1 id=good.1h5v.s5.7039814cc337 from=translated src=- shape=d4992678 vocab=e0407894
-/
theorem comp_AddMonoidHom [AddZero G₀] [AddZero G] [CommSemiring R]
    {f : G → R} (hf : good f) (φ : G₀ →+ G) : good (f ∘ φ) :=
  λ _ _ _ h ↦ hf _ _ _ (by rw [← φ.map_add, ← φ.map_add, h, φ.map_zero])

/-- if `f : G → R` is good and `φ : R → R₀` is a ring homomorphism, `φ ∘ f` is good.
@isnad1 id=good.1h5v.s6.f1eb0d0c9ea9 from=translated src=- shape=89c1ec5b vocab=ddae5cc7
-/
theorem RingHom_comp [AddZero G] [CommSemiring R] [CommSemiring R₀]
    {f : G → R} (hf : good f) (φ : R →+* R₀) : good (φ ∘ f) :=
  λ _ _ _ h ↦ (hf _ _ _ h).RingHom_apply φ

end good

/-- The function `f : ZMod 2 → R` defined by `0 ↦ 0, 1 ↦ 1` is good.
@isnad1 id=good.0h1v.s6.07ead6958df6 from=translated src=- shape=3568556a vocab=38b30365
-/
theorem ZMod2_Semiring_is_good [CommSemiring R] : good (![0, 1] : ZMod 2 → R) := by
  let φ : ℕ →+* R := Nat.castRingHom R
  have h : φ ∘ ![0, 1] = ![0, 1] :=
    funext λ x ↦ match x with | 0 => φ.map_zero | 1 => φ.map_one
  simpa only [h] using ZMod2_01_is_good.RingHom_comp φ

/-- The function `f : ZMod 4 → ℤ` defined by `0 ↦ 0, 1 ↦ 1, 2 ↦ 4, 3 ↦ 1` is good.
@isnad1 id=good.0h1v.s6.dc90420f868a from=translated src=- shape=9d80ed70 vocab=38b30365
-/
theorem ZMod4_Semiring_is_good [CommSemiring R] : good (![0, 1, 4, 1] : ZMod 4 → R) := by
  let φ : ℕ →+* R := Nat.castRingHom R
  have h : φ ∘ ![0, 1, 4, 1] = ![0, 1, 4, 1] :=
    funext λ x ↦ match x with
      | 0 => φ.map_zero | 1 => φ.map_one | 2 => map_ofNat φ 4 | 3 => φ.map_one
  simpa only [h] using ZMod4_0141_is_good.RingHom_comp φ

namespace good

section

variable [AddGroup G] [CommRing R] [NoZeroDivisors R]

/-- Suppose that `char(R) ≠ 3`. If `f : G → R` is good then `f(0) = 0`.
@isnad1 id=eq.2h3v.s6.645ec254733c from=translated src=- shape=bc0de5c7 vocab=b5f295dd
-/
theorem map_zero_of_three_ne_zero (hR : (3 : R) ≠ 0) {f : G → R} (hf : good f) : f 0 = 0 :=
  (hf 0 0 0 ((add_zero _).trans (add_zero _))).eq_zero_of_const hR

variable {f : G → R} (hf : good f) (hf0 : f 0 = 0)
include hf hf0

/-- If `f : G → R` is good with `f(0) = 0` then `f` is even.
@isnad1 id=eq.2h4v.s6.b442746ce5a8 from=translated src=- shape=d6225f92 vocab=db9aa538
-/
theorem map_neg_of_map_zero (x) : f (-x) = f x := by
  have h : HeronTriple (f (-x)) (f x) (f 0) :=
    hf (-x) x 0 ((add_zero _).trans (neg_add_cancel x))
  rwa [hf0, iff_eq_of_zero_right] at h

/-- If `f : G → R` is good with `f(0) = 0` then
  `(f(x), f(y), f(x + y))` is a Heron triple for any `x, y : G`.
@isnad1 id=herontri.2h5v.s6.19236e0f11e0 from=translated src=- shape=ec5ce333 vocab=22801544
-/
theorem def_of_map_zero (x y : G) : HeronTriple (f x) (f y) (f (x + y)) := by
  simpa only [hf.map_neg_of_map_zero hf0] using hf x y (-(x + y)) (add_neg_cancel _)

/-- If `f : G → R` is good with `f(0) = 0` and `c : G` satisfies `f(c) = 0`,
  then `f(x + c) = f(x)` for any `x : G`.
@isnad1 id=eq.3h5v.s7.d7d708a53082 from=translated src=- shape=c7a2a26e vocab=a72e2ed8
-/
theorem map_add_of_map_eq_zero {c : G} (hc : f c = 0) (x) : f (x + c) = f x := by
  have h : HeronTriple (f (x + c)) (f x) (f c) := (hf.def_of_map_zero hf0 x c).perm312
  rwa [hc, iff_eq_of_zero_right] at h

/-- If `f : G → R` is good with `f(0) = 0` and `c : G` satisfies `f(c) = 0`,
  then `f(nc) = 0` for every integer `n`.
@isnad1 id=eq.3h5v.s7.9087583c2e7a from=translated src=- shape=084725d5 vocab=4d00b378
-/
theorem map_nsmul_of_map_eq_zero {c : G} (hc : f c = 0) (n : ℤ) : f (n • c) = 0 := by
  induction n using Int.induction_on with
  | zero => rw [zero_zsmul, hf0]
  | succ n n_ih => rw [add_one_zsmul, hf.map_add_of_map_eq_zero hf0 hc, n_ih]
  | pred n n_ih =>
      replace hc : f (-c) = 0 := (hf.map_neg_of_map_zero hf0 c).trans hc
      rw [sub_one_zsmul, hf.map_add_of_map_eq_zero hf0 hc, n_ih]

end

section

variable [CommRing R] [NoZeroDivisors R] {f : ℤ → R} (hf : good f) (hf0 : f 0 = 0)
include hf hf0

/-- If `f(0) = 0` and `f(N) = 0` for some `N : ℕ` nonzero, then for any `n : ℕ`,
  we have `f(x) = f(n)` where `x` is the image of `n` in `ZMod N`.
@isnad1 id=eq.3h4v.s7.89cbaf4cab2a from=translated src=- shape=226340c8 vocab=5008e933
-/
theorem Int_map_ZMod_of_map_eq_zero {N : ℕ} [NeZero N] (hN : f N = 0) (n : ℤ) :
    f (n : ZMod N).val = f n := by
  obtain ⟨k, hk⟩ : (N : ℤ) ∣ n - (n : ZMod N).val := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, ZMod.natCast_val,
      ZMod.intCast_cast, ZMod.cast_intCast (Nat.dvd_refl _), sub_self]
  calc f (n : ZMod N).val
    _ = f ((n : ZMod N).val + k * N) :=
      (hf.map_add_of_map_eq_zero hf0 (hf.map_nsmul_of_map_eq_zero hf0 hN k) _).symm
    _ = f n := by rw [Int.mul_comm, ← hk, add_sub_cancel]

/-- If `f(0) = 0`, then `f(2)` is equal to either `4 f(1)` or `0`.
@isnad1 id=or.2h2v.s7.4586cb631d47 from=translated src=- shape=ee74222f vocab=8e7f1780
-/
theorem Int_map_two_eq : f 2 = f 1 * 2 ^ 2 ∨ f 2 = 0 :=
  iff_of_left_mid_eq.mp (hf.def_of_map_zero hf0 1 1)

/-- If `f(0) = f(2) = 0`, then `f(n) = f(1)` if `n` is odd and `f(n) = 0` if `n` is even.
@isnad1 id=eq.3h2v.s7.a3bfff07d5f3 from=translated src=- shape=955d627b vocab=cd05172a
-/
theorem Int_eq_smul_ZMod2_01_of_map_two (hf1 : f 2 = 0) :
    f = λ n : ℤ ↦ f 1 * ![0, 1] (n : ZMod 2) := by
  have h : ∀ x : ZMod 2, f x.val = f 1 * ![0, 1] x
    | 0 => hf0.trans (mul_zero _).symm
    | 1 => (mul_one _).symm
  funext n; rw [← hf.Int_map_ZMod_of_map_eq_zero hf0 hf1 _, h]

/-- If `f(0) = 0 0` and `f(2) = 4 f(1)`, then `f(3)` is either `9 f(1)` or `f(1)`.
@isnad1 id=or.3h2v.s7.c6d2e9fa814b from=translated src=- shape=2a2d3213 vocab=8e7f1780
-/
theorem Int_map_three_eq_of_map_two (hf1 : f 2 = f 1 * 2 ^ 2) :
    f 3 = f 1 * 3 ^ 2 ∨ f 3 = f 1 := by
  have h : HeronTriple (f 1 * 2 ^ 2) (f 1 * 1 ^ 2) (f 3) := by
    rw [one_pow, mul_one, ← hf1]; exact hf.def_of_map_zero hf0 2 1
  rwa [iff_eq_mul_add_or_sub_sq, two_add_one_eq_three,
    sub_eq_of_eq_add one_add_one_eq_two.symm, one_pow, mul_one] at h

/-- If `f(0) = 0`, `f(2) = 4 f(1)`, and `f(3) = 9 f(1)`,
  then `f(n) = f(1) n^2` for all integers `n`.
@isnad1 id=eq.4h2v.s8.0ed493626e52 from=translated src=- shape=06aae00b vocab=6e32734d
-/
theorem Int_eq_smul_sq_of_map_three (hf1 : f 2 = f 1 * 2 ^ 2) (hf2 : f 3 = f 1 * 3 ^ 2) :
    f = λ n : ℤ ↦ f 1 * n ^ 2 := by
  ---- Since `f` is even, we only need to check `f(n) = f(1) n^2` for `n : ℕ`.
  suffices ∀ n : ℕ, f n = f 1 * n ^ 2 by
    funext n; have h : f n = f n.natAbs := by
      obtain hn | hn : n = n.natAbs ∨ n = -n.natAbs := n.natAbs_eq
      exacts [congrArg f hn, (congrArg f hn).trans (hf.map_neg_of_map_zero hf0 _)]
    rw [h, this, ← Int.cast_natCast, ← Int.cast_pow, Int.natAbs_sq, Int.cast_pow]
  ---- We proceed by strong induction on `n`, with the base cases `n ≤ 3` easy to check.
  intro n; induction n using Nat.strong_induction_on with | h n n_ih => ?_
  have hf3 : f 1 = f 1 * 1 ^ 2 := by rw [one_pow, mul_one]
  match n with
    | 0 => rw [Int.natCast_zero, hf0, Nat.cast_zero, zero_pow (Nat.succ_ne_zero 1), mul_zero]
    | 1 => rw [Int.natCast_one, Nat.cast_one, ← hf3]
    | 2 => exact hf1
    | 3 => exact hf2
    | n + 4 => ?_
  change f (n + 4) = _
  ---- First, `(a, b) = (n + 3, 1)` gives `f(n + 4) ∈ {f(1) (n + 4)^2, f(1) (n + 2)^2}`.
  obtain h | h :
      f (n + 4) = f 1 * ((n + 3 : ℕ) + 1) ^ 2 ∨ f (n + 4) = f 1 * ((n + 3 : ℕ) - 1) ^ 2 := by
    have h := hf.def_of_map_zero hf0 (n + 3 : ℕ) 1
    rwa [hf3, n_ih (n + 3) (Nat.lt_succ_self _), iff_eq_mul_add_or_sub_sq] at h
  · rw [Nat.cast_succ, h]
  ---- Second, `(a, b) = (n + 2, 2)` gives `f(n + 4) ∈ {f(1) (n + 4)^2, f(1) n^2}`.
  obtain h0 | h0 :
      f (n + 4) = f 1 * ((n + 2 : ℕ) + 2) ^ 2 ∨ f (n + 4) = f 1 * ((n + 2 : ℕ) - 2) ^ 2 := by
    have h0 := hf.def_of_map_zero hf0 (n + 2 : ℕ) 2
    rwa [hf1, n_ih _ (Nat.le_add_right _ 1), iff_eq_mul_add_or_sub_sq] at h0
  · rw [Nat.cast_add (n + 2) 2, Nat.cast_two, h0]
  ---- Now assume `f(n + 4) = f(1) (n + 2)^2 = f(1) n^2`.
  replace h0 : f (n + 4) = f 1 * n ^ 2 := by
    rwa [Nat.cast_add, Nat.cast_two, add_sub_cancel_right] at h0
  replace h : f (n + 4) = f 1 * (n + 2) ^ 2 := by
    rwa [Nat.cast_succ, add_sub_cancel_right, Nat.cast_add] at h
  ---- Then we have either `f(1) = 0` or `(n + 2)^2 = n^2` over `R`.
  replace h : f 1 = 0 ∨ (n + 2 : R) ^ 2 = n ^ 2 := by
    rwa [h0, eq_comm, mul_eq_mul_left_iff, or_comm] at h
  ---- The case `f(1) = 0` is trivial, so now assume `(n + 2)^2 = n^2` on `R`.
  rcases h with h | h
  · rw [h0, h, zero_mul, zero_mul]
  ---- Rearranging gives `4(n + 1) = 0`, so either `2 = 0` on `R` or `n + 1 = 0` on `R`.
  replace h : (2 : R) = 0 ∨ (n + 1 : R) = 0 := by
    rwa [add_sq, add_assoc, add_eq_left, mul_right_comm, ← sq, ← mul_add_one,
      mul_eq_zero, pow_eq_zero_iff (Nat.succ_ne_zero 1)] at h
  ---- If `2 = 0` on `R`, we have `f(n + 4) = f(1) n^2 = f(1) (n + 4)^2`.
  rcases h with h | h
  · rw [h0, Nat.cast_add _ 2, Nat.cast_add, Nat.cast_two, h, add_zero, add_zero]
  ---- Finally, if `n + 1 = 0` on `R`, then `f(n + 4) = f(3) = f(1) (n + 4)^2`.
  replace h0 : f (n + 1 : ℕ) = 0 := by
    rw [n_ih (n + 1) (Nat.le_add_right _ 2), Nat.cast_succ, h, sq, mul_zero, mul_zero]
  calc f (n + 4 : ℕ)
    _ = f (3 + (n + 1 : ℕ)) := by rw [Nat.cast_add _ 3, add_comm, Nat.cast_three]
    _ = f 3 := hf.map_add_of_map_eq_zero hf0 h0 3
    _ = f 1 * 3 ^ 2 := hf2
    _ = f 1 * (n + 4 : ℕ) ^ 2 := by rw [Nat.cast_add _ 3, Nat.cast_succ, h, zero_add]; rfl

end

section

variable [CommRing R] [NoZeroDivisors R] (hR : (3 : R) ≠ 0) {f : ℤ → R} (hf : good f)
include hR hf

/-- If `char(R) ≠ 3`, `f(2) = 4 f(1)`, and `f(3) = f(1)`, then `f(n) = f(1)` if `n` is odd,
  `f(n) = 4f(1)` if `n ≡ 2 (mod 4)`, and `f(n) = 0` if `4 ∣ n`.
@isnad1 id=eq.4h2v.s8.54405107545d from=translated src=- shape=827f13ed vocab=304272f6
-/
theorem Int_eq_smul_ZMod4_0141_of_map_three (hf0 : f 2 = f 1 * 2 ^ 2) (hf1 : f 3 = f 1) :
    f = λ n : ℤ ↦ f 1 * ![0, 1, 4, 1] (n : ZMod 4) := by
  have hR0 : (2 : R) ^ 2 = 4 := by rw [sq, mul_two, two_add_two_eq_four]
  have hf2 : f 0 = 0 := hf.map_zero_of_three_ne_zero hR
  ---- It suffices to prove `f(4) = 0` by periodicity.
  suffices f 4 = 0 by
    have h : ∀ x : ZMod 4, f x.val = f 1 * ![0, 1, 4, 1] x
      | 0 =>  hf2.trans (mul_zero _).symm
      | 1 =>  (mul_one _).symm
      | 2 =>  hf0.trans (congrArg (f 1 * ·) hR0)
      | 3 =>  hf1.trans (mul_one _).symm
    funext n; rw [← hf.Int_map_ZMod_of_map_eq_zero hf2 this _, h]
  ---- First, since `f(3) = f(1)`, we have `f(4) ∈ {0, 4f(1)}`; assume the latter.
  obtain hf3 | hf3 : f 4 = 0 ∨ f 4 = f 1 * 2 ^ 2 := by
    have h : HeronTriple (f 3) (f 1) (f 4) := hf.def_of_map_zero hf2 3 1
    rwa [hf1, iff_of_left_mid_eq, or_comm] at h
  · exact hf3
  ---- Next, we also have `f(4) ∈ {0, 4f(2)}`; assume the latter as well.
  obtain hf4 | hf4 : f 4 = 0 ∨ f 4 = f 2 * 2 ^ 2 :=
    (iff_of_left_mid_eq.mp (hf.def_of_map_zero hf2 2 2)).symm
  · exact hf4
  ---- Then `4f(1) = 4f(2) = 16f(1) ↔ 12f(1) = 0 → f(4) = 4f(1) = 0` since `3 ≠ 0` in `R`.
  rwa [hf0, ← hf3, eq_comm, ← sub_eq_zero, ← mul_sub_one, hR0, mul_eq_zero,
    sub_eq_of_eq_add three_add_one_eq_four.symm, or_iff_left hR] at hf4

open Fin.IntCast in
/-- If `char(R) ≠ 3`, then a good function `f : ℤ → R` takes one of the
  three forms we see above; squares, mod 2 functions, or mod 4 functions.
@isnad1 id=or.2h2v.s8.6e6b2bc9ce81 from=translated src=- shape=2ead37f7 vocab=f6fe3fd3
-/
theorem Int_solution_of_char_ne_three :
    (∃ c, f = λ n : ℤ ↦ c * ![0, 1] n) ∨ (∃ c, f = λ n : ℤ ↦ c * ![0, 1, 4, 1] n)
      ∨ (∃ c : R, f = λ n : ℤ ↦ c * n ^ 2) := by
  have hf0 : f 0 = 0 := hf.map_zero_of_three_ne_zero hR
  exact (hf.Int_map_two_eq hf0).symm.imp
    (λ hf1 ↦ ⟨f 1, hf.Int_eq_smul_ZMod2_01_of_map_two hf0 hf1⟩)
    (λ hf1 ↦ (hf.Int_map_three_eq_of_map_two hf0 hf1).symm.imp
      (λ hf2 ↦ ⟨f 1, hf.Int_eq_smul_ZMod4_0141_of_map_three hR hf1 hf2⟩)
      (λ hf2 ↦ ⟨f 1, hf.Int_eq_smul_sq_of_map_three hf0 hf1 hf2⟩))

end

end good

open Fin.IntCast in
/-- Final solution
@isnad1 id=iff.1h2v.s8.92feded55fc5 from=translated src=- shape=a8d9177c vocab=f6fe3fd3
-/
theorem final_solution [CommRing R] [NoZeroDivisors R] (hR : (3 : R) ≠ 0) {f : ℤ → R} :
    good f ↔ (∃ c, f = λ n : ℤ ↦ c * ![0, 1] n) ∨ (∃ c, f = λ n : ℤ ↦ c * ![0, 1, 4, 1] n)
      ∨ (∃ c, f = λ n : ℤ ↦ c * (n : R) ^ 2) := by
  refine ⟨λ hf ↦ hf.Int_solution_of_char_ne_three hR, ?_⟩
  rintro (⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact (ZMod2_Semiring_is_good.comp_AddMonoidHom (Int.castAddHom (ZMod 2))).smul_left c
  · exact (ZMod4_Semiring_is_good.comp_AddMonoidHom (Int.castAddHom (ZMod 4))).smul_left c
  · have h : (c • Int.castRingHom R ∘ fun r ↦ r ^ 2) = λ n : ℤ ↦ c * (n : R) ^ 2 :=
      funext λ n ↦ congrArg (c * ·) (Int.cast_pow n 2)
    simpa only [h] using (sq_is_good.RingHom_comp (Int.castRingHom R)).smul_left c
