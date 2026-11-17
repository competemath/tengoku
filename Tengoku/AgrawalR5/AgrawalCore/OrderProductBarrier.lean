/-
The multiplicative-order product barrier behind H4.

For a good divisor of the primitive four-coefficient integer, the
orders of `5` and of the coordinated golden square are exactly `2r`
and `2s`.  Hence their product is the primitive level `4rs`.

In the cyclotomic split branch `p ≡ 1 (mod 5)`, level reciprocity says
that the residual multiplier is divisible by ten.  Consequently ten
times the product of the two exact orders divides `p-1`.

This is a necessary condition, not a proof of H4.  It isolates the
missing universal input as a lower-bound/exclusion theorem for the
product of two multiplicative orders.
-/
import Tengoku.AgrawalR5.AgrawalCore.LevelReciprocity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

variable {p r s k h : ℕ} [Fact p.Prime]

/-- A good primitive divisor factors `p-1` as the product of the two
exact scalar orders and the residual multiplier.
@isnad1 id=eq.9h6v.s8.9919b36bc36f from=translated src=- shape=e795100e vocab=e40f5c60
-/
theorem dvd_D_order_product_residual_factorization
    (hp5 : p ≠ 5) (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    (hfactor : p - 1 = (4 * r * s) * h) :
    p - 1 =
      (orderOf (5 : ZMod p) * orderOf (goldenSquareFromGamma γ)) * h := by
  obtain ⟨hord5, hordx⟩ :=
    dvd_D_exact_scalar_profile
      hp5 hr hs hkpos hpm hsig γ hγ hD
  rw [hord5, hordx]
  calc
    p - 1 = (4 * r * s) * h := hfactor
    _ = ((2 * r) * (2 * s)) * h := by ring

/-- **Exact order-product compression in the `p ≡ 1 (mod 5)` branch.**

Any good primitive divisor in this branch must satisfy

`10 * ord_p(5) * ord_p(ε²) ∣ p - 1`.

The golden square is written intrinsically as
`goldenSquareFromGamma γ`.
@isnad1 id=dvd.11h6v.s8.6103311b7a6e from=translated src=- shape=ff30fb05 vocab=4cdbbc2e
-/
theorem dvd_D_ten_mul_order_product_dvd_card_sub_one
    (hp5 : p ≠ 5) (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s) (h5level : ¬5 ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    (hfactor : p - 1 = (4 * r * s) * h)
    (hpmod : p % 5 = 1) :
    10 * (orderOf (5 : ZMod p) *
      orderOf (goldenSquareFromGamma γ)) ∣ p - 1 := by
  have h10 : 10 ∣ h :=
    (dvd_D_ten_dvd_residual_multiplier_iff_mod_five_one
      hp5 hr hs hkpos hpm h5level hsig γ hγ hD hfactor).mpr hpmod
  have hproduct :
      p - 1 =
        (orderOf (5 : ZMod p) *
          orderOf (goldenSquareFromGamma γ)) * h :=
    dvd_D_order_product_residual_factorization
      hp5 hr hs hkpos hpm hsig γ hγ hD hfactor
  rw [hproduct]
  obtain ⟨c, rfl⟩ := h10
  refine ⟨c, ?_⟩
  ring

/-- Inequality form of the exact divisibility barrier.
@isnad1 id=le.11h6v.s8.987a804781c7 from=translated src=- shape=5b33452f vocab=4cdbbc2e
-/
theorem dvd_D_ten_mul_order_product_le_card_sub_one
    (hp5 : p ≠ 5) (hr : 0 < r) (hs : 0 < s) (hkpos : 1 ≤ k)
    (hpm : ¬p ∣ 4 * r * s) (h5level : ¬5 ∣ 4 * r * s)
    (hsig : CanonicalSignature (4 * r * s) r s k)
    (γ : ZMod p) (hγ : γ ^ 2 = 5 * γ - 5)
    (hD : p ∣ primitiveFourCoefficientD (4 * r * s) k)
    (hfactor : p - 1 = (4 * r * s) * h)
    (hpmod : p % 5 = 1) :
    10 * (orderOf (5 : ZMod p) *
      orderOf (goldenSquareFromGamma γ)) ≤ p - 1 := by
  have hdvd :=
    dvd_D_ten_mul_order_product_dvd_card_sub_one
      hp5 hr hs hkpos hpm h5level hsig γ hγ hD hfactor hpmod
  exact Nat.le_of_dvd (by
    have hpgt : 1 < p := (Fact.out : p.Prime).one_lt
    omega) hdvd

end AgrawalCore
