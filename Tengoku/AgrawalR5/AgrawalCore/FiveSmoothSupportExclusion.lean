/-
Exclusion of the 5-smooth split H4 support.

In the branch `p ≡ 1 (mod 5)`, the primitive H4 level `4rs` is prime
to five.  If `p - 1` had no odd prime divisor other than five, both
coprime semiorders `r` and `s` would divide the same power of two.
Their opposite parity would then force one of them to be one.

The corresponding exact scalar order would be two.  Neither scalar five
nor the coordinated golden square can have order two at a good split
prime.  Hence no H4 prime can satisfy `p - 1 = 2^b * 5^f`.
-/
import Tengoku.AgrawalR5.AgrawalCore.PrimitiveScalarBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

private theorem five_unit_ne_zero (hp5 : p ≠ 5) :
    (5 : ZMod p) ≠ 0 := by
  intro hzero
  have hpdiv : p ∣ 5 :=
    (CharP.cast_eq_zero_iff (ZMod p) p 5).mp hzero
  exact hp5 ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hpdiv)

/-- Scalar five cannot have order two in the split branch `p ≡ 1 mod 5`.-/
theorem orderOf_five_ne_two_of_mod_five_one
    (hp2 : p ≠ 2) (hpmod : p % 5 = 1) :
    orderOf (5 : ZMod p) ≠ 2 := by
  intro hord
  have hneg : (5 : ZMod p) = -1 :=
    (CharP.orderOf_eq_two_iff p hp2).mp hord
  have hsix : (6 : ZMod p) = 0 := by
    linear_combination hneg
  have hpdiv : p ∣ 6 :=
    (CharP.cast_eq_zero_iff (ZMod p) p 6).mp hsix
  have hpdiv' : p ∣ 2 * 3 := by norm_num at hpdiv ⊢; exact hpdiv
  rcases (Fact.out : p.Prime).dvd_mul.mp hpdiv' with hpTwo | hpThree
  · exact hp2 <|
      (Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hpTwo
  · have hpEq : p = 3 :=
      (Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hpThree
    rw [hpEq] at hpmod
    norm_num at hpmod

/-- If `r` and `s` have opposite parity and both divide a power of two,
then one of them is one.-/
theorem one_eq_one_of_opposite_parity_dvd_two_power
    {r s b : ℕ} (hpar : Odd (r + s))
    (hr : r ∣ 2 ^ b) (hs : s ∣ 2 ^ b) :
    r = 1 ∨ s = 1 := by
  rcases Nat.even_or_odd r with hrEven | hrOdd
  · right
    have hsOdd : Odd s := by
      rcases hrEven with ⟨u, hu⟩
      rcases hpar with ⟨v, hv⟩
      exact ⟨v - u, by omega⟩
    have hcop : Nat.Coprime s (2 ^ b) :=
      (Nat.coprime_two_right.mpr hsOdd).pow_right b
    exact hcop.eq_one_of_dvd hs
  · left
    have hcop : Nat.Coprime r (2 ^ b) :=
      (Nat.coprime_two_right.mpr hrOdd).pow_right b
    exact hcop.eq_one_of_dvd hr

/-- **Universal exclusion of 5-smooth split support.**

There is no good split H-profile whose ambient group order has the form
`2^b * 5^f`.  This is an infinite excluded family and is independent of
any finite census.-/
theorem no_split_five_smooth_support
    {b f r s : ℕ}
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) (hpmod : p % 5 = 1)
    (hpar : Odd (r + s))
    (h5level : ¬5 ∣ 4 * r * s)
    (hpform : p - 1 = 2 ^ b * 5 ^ f)
    (hord5 : orderOf (5 : ZMod p) = 2 * r)
    (x : ZMod p) (hx : x ^ 2 = 3 * x - 1)
    (hordx : orderOf x = 2 * s) :
    False := by
  have h5r : ¬5 ∣ r := by
    intro hdvd
    obtain ⟨a, ha⟩ := hdvd
    apply h5level
    refine ⟨4 * a * s, ?_⟩
    rw [ha]
    ring
  have h5s : ¬5 ∣ s := by
    intro hdvd
    obtain ⟨a, ha⟩ := hdvd
    apply h5level
    refine ⟨4 * r * a, ?_⟩
    rw [ha]
    ring
  have hR : 2 * r ∣ p - 1 := by
    rw [← hord5]
    exact ZMod.orderOf_dvd_card_sub_one (five_unit_ne_zero hp5)
  have hx0 : x ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hx
    norm_num at hx
  have hE : 2 * s ∣ p - 1 := by
    rw [← hordx]
    exact ZMod.orderOf_dvd_card_sub_one hx0
  have hrAmbient : r ∣ 2 ^ b * 5 ^ f := by
    rw [← hpform]
    exact (show r ∣ 2 * r from ⟨2, by ring⟩).trans hR
  have hsAmbient : s ∣ 2 ^ b * 5 ^ f := by
    rw [← hpform]
    exact (show s ∣ 2 * s from ⟨2, by ring⟩).trans hE
  have hrTwo : r ∣ 2 ^ b :=
    (Nat.prime_five.coprime_pow_of_not_dvd h5r).dvd_of_dvd_mul_right
      hrAmbient
  have hsTwo : s ∣ 2 ^ b :=
    (Nat.prime_five.coprime_pow_of_not_dvd h5s).dvd_of_dvd_mul_right
      hsAmbient
  rcases one_eq_one_of_opposite_parity_dvd_two_power
      hpar hrTwo hsTwo with hrOne | hsOne
  · apply orderOf_five_ne_two_of_mod_five_one hp2 hpmod
    simpa [hrOne] using hord5
  · apply orderOf_golden_square_ne_two hp2 hp5 x hx
    simpa [hsOne] using hordx

/-- End-to-end four-coefficient form of the 5-smooth exclusion.-/
theorem no_split_five_smooth_primitive_support
    {b f r s k : ℕ}
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) (hpmod : p % 5 = 1)
    (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s) (h5level : ¬5 ∣ 4 * r * s)
    (hpar : Odd (r + s))
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    (hpform : p - 1 = 2 ^ b * 5 ^ f) :
    False := by
  obtain ⟨hord5, hordx⟩ :=
    dvd_D_exact_scalar_profile
      hp5 hr hs hkpos hpm hsig γ hγ hD
  exact no_split_five_smooth_support
    hp2 hp5 hpmod hpar h5level hpform hord5
      (goldenSquareFromGamma γ)
      (goldenSquareFromGamma_sq_eq_three_mul_sub_one hp5 γ hγ)
      hordx

end AgrawalCore
