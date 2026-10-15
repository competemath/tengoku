/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Tengoku

/-!
# `ZMod` lemmas

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.
-/

@[expose] public section

/-- If `m ∣ a + b`, then `b ≡ -a mod m`.
@isnad1 id=eq.1h3v.s6.b4c387b079c9 from=translated src=- shape=245ea295 vocab=af32c453
-/
lemma ZMod.intCast_eq_neg_intCast_of_dvd_add {a b : ℤ} {m : ℕ} (h : (m : ℤ) ∣ a + b) :
    (b : ZMod m) = -(a : ZMod m) := by
  have h0 : ((a + b : ℤ) : ZMod m) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr h
  push_cast at h0
  linear_combination h0

/-- If `m` is coprime to `a` and divides `a + b`, then `b` is a unit mod `m`.
@isnad1 id=isunit.2h3v.s5.9c48c2e3a4b0 from=translated src=- shape=dcc0f7db vocab=a9bc471e
-/
lemma ZMod.isUnit_intCast_of_isCoprime_of_dvd_add {a b : ℤ} {m : ℕ}
    (hcop : IsCoprime (m : ℤ) a) (h : (m : ℤ) ∣ a + b) : IsUnit ((b : ZMod m)) := by
  have hu := (ZMod.coe_int_isUnit_iff_isCoprime a m).mpr hcop
  simpa [ZMod.intCast_eq_neg_intCast_of_dvd_add h] using hu.neg
