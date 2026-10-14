/-
Copyright (c) 2026 Carles Marín. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carles Marín
-/
module

public import Tengoku

/-!
# Power-series logarithm lemmas

This module proves the power-series logarithm additivity and coefficient identities used to
transport the Connes-Kreimer Eulerian idempotent calculation to convolution algebras.
-/

@[expose] public section

namespace PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

omit [Algebra ℚ A] in
/-- A series with zero constant coefficient has its `d`-th power vanishing below degree `d`.
@isnad1 id=eq.2h4v.s8.8105708e4b87 from=translated src=- shape=68c11677 vocab=e2427a50
-/
theorem coeff_pow_eq_zero_of_lt {g : A⟦X⟧} (hg : constantCoeff g = 0) {d m : ℕ}
    (hmd : m < d) :
    coeff m (g ^ d) = 0 :=
  (X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hg) d)) m hmd

end PowerSeries
