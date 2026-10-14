/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Tengoku

/-!
# Yield curve bootstrapping

Standard practitioner method to extract zero-coupon bond (ZCB) prices from a
sequence of coupon-bond prices at successive maturities.

Given a coupon bond paying coupon `c i` at time `T_i` for `i ∈ sprev` (the
earlier maturities) plus `c_last + F` at the new (longest) maturity `T_n`,
with observed price `P`, the new ZCB price `B_last` satisfies:

  `P = (∑_{i ∈ sprev} c i · B i) + (c_last + F) · B_last`,

so

  `B_last = (P − ∑_{i ∈ sprev} c i · B i) / (c_last + F)`,

provided `c_last + F ≠ 0`.

This identity, applied recursively starting from a single-period bond (where
`sprev = ∅` and `B_last = P / (c_last + F)`), bootstraps the full discount
curve from coupon-bond market data.

Results:

* `couponBondPricingEq`: the pricing equation for a coupon bond with one new
  maturity and previously-known maturities.
* `bootstrap_solve`: from the pricing equation, recovers `B_last` as a
  closed-form ratio.
* `bootstrap_solve_first`: bootstrap base case for the first bond with empty
  previous schedule: `B_1 = P_1 / (c_1 + F)`.
* `bootstrap_solve_second`: bootstrap step for the second bond:
  `B_2 = (P_2 − c · B_1) / (c + F)`.
-/

@[expose] public section

namespace MathFin

/-- Coupon-bond pricing equation expressed in terms of previously-known ZCB
prices `B : ι → ℝ` and the new ZCB `B_last`. -/
def couponBondPricingEq {ι : Type*} (sprev : Finset ι) (c B : ι → ℝ)
    (P c_last F B_last : ℝ) : Prop :=
  P = (∑ i ∈ sprev, c i * B i) + (c_last + F) * B_last

/-- **Bootstrap solve identity**: from the coupon-bond pricing equation, the
new ZCB price `B_last` is recovered as a closed-form ratio.
@isnad1 id=eq.2h8v.s6.891d07480d7b from=translated src=- shape=74b067d4 vocab=4c3d3f29
-/
lemma bootstrap_solve {ι : Type*} (sprev : Finset ι) (c B : ι → ℝ)
    (P c_last F B_last : ℝ) (h : c_last + F ≠ 0)
    (hP : couponBondPricingEq sprev c B P c_last F B_last) :
    B_last = (P - ∑ i ∈ sprev, c i * B i) / (c_last + F) := by
  unfold couponBondPricingEq at hP
  field_simp
  linarith

/-- **First-bond bootstrap** (empty previous schedule): a single-period coupon
bond with cash flow `c_last + F` at maturity gives `B_last = P / (c_last + F)`.
@isnad1 id=eq.2h4v.s6.cd2fb7754ead from=translated src=- shape=f40e797c vocab=a74ee98d
-/
lemma bootstrap_solve_first (P c_last F B_last : ℝ) (h : c_last + F ≠ 0)
    (hP : P = (c_last + F) * B_last) :
    B_last = P / (c_last + F) := by
  rw [hP]
  field_simp

/-- **Second-bond bootstrap step**: with one previous ZCB price `B_1` and a
two-period bond paying coupon `c` at both dates plus face `F` at the second,
`B_2 = (P − c · B_1) / (c + F)`.
@isnad1 id=eq.2h5v.s6.4c1e2a3869e9 from=translated src=- shape=d1e17cd3 vocab=335f4d48
-/
lemma bootstrap_solve_second (P c F B_1 B_2 : ℝ) (h : c + F ≠ 0)
    (hP : P = c * B_1 + (c + F) * B_2) :
    B_2 = (P - c * B_1) / (c + F) := by
  rw [hP]
  field_simp
  ring

/-- **Recursive consistency**: the bootstrapped ZCB price, plugged back into
the pricing equation, recovers the original bond price.
@isnad1 id=couponbo.1h7v.s6.3e2fb729edad from=translated src=- shape=81d24472 vocab=4c3d3f29
-/
lemma bootstrap_consistency {ι : Type*} (sprev : Finset ι) (c B : ι → ℝ)
    (P c_last F : ℝ) (h : c_last + F ≠ 0) :
    couponBondPricingEq sprev c B P c_last F
      ((P - ∑ i ∈ sprev, c i * B i) / (c_last + F)) := by
  unfold couponBondPricingEq
  field_simp
  ring

end MathFin
