/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.GCDMonoid.Basic
public import Tengoku.Seed.Algebra.Ring.PUnit

/-!
# `PUnit` is a GCD monoid

This file collects facts about algebraic structures on the one-element type, e.g. that it is has a
GCD.
-/

public section

namespace PUnit

-- This is too high-powered and should be split off also
instance : StrongNormalizedGCDMonoid PUnit where
  gcd _ _ := unit
  lcm _ _ := unit
  normUnit _ := 1
  normUnit_zero := rfl
  normUnit_mul := by subsingleton
  normUnit_coe_units := by subsingleton
  gcd_dvd_left _ _ := ⟨unit, by subsingleton⟩
  gcd_dvd_right _ _ := ⟨unit, by subsingleton⟩
  dvd_gcd {_ _} _ _ _ := ⟨unit, by subsingleton⟩
  gcd_mul_lcm _ _ := ⟨1, by subsingleton⟩
  lcm_zero_left := by subsingleton
  lcm_zero_right := by subsingleton
  normalize_gcd := by subsingleton
  normalize_lcm := by subsingleton

instance normalizedGCDMonoid : NormalizedGCDMonoid PUnit := inferInstance

/--
@isnad1 id=eq.0h2v.s4.719078e86ddd from=seed src=0 shape=40766c62 vocab=1681e888
-/
@[simp]
theorem gcd_eq {x y : PUnit} : gcd x y = unit :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.bd4e074c6516 from=seed src=0 shape=40766c62 vocab=c5cce030
-/
@[simp]
theorem lcm_eq {x y : PUnit} : lcm x y = unit :=
  rfl

/--
@isnad1 id=eq.0h1v.s6.78f1d5c587c4 from=seed src=0 shape=47e22901 vocab=d91a35d2
-/
@[simp]
theorem norm_unit_eq {x : PUnit} : normUnit x = 1 :=
  rfl

end PUnit
