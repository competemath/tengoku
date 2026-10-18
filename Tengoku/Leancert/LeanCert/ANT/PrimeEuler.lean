/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.ANT.EulerProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Prime Euler-product presets

This file keeps arithmetic presets separate from the generic finite
Euler-product certificate machinery.
-/

namespace LeanCert.ANT

open scoped BigOperators

/-- Rational factor `1 - 1/n`. -/
def oneMinusInvRat (n : Nat) : ℚ :=
  1 - 1 / (n : ℚ)

/-- Rational factor `1 + 1/n`. -/
def onePlusInvRat (n : Nat) : ℚ :=
  1 + 1 / (n : ℚ)

/-- Finite prime product `∏_{p ≤ N} (1 - 1/p)`. -/
noncomputable def primeEulerOneMinusInv (N : Nat) : ℝ :=
  finiteProduct (primesLE N) fun p => (1 : ℝ) - 1 / (p : ℝ)

/-- Exact rational value of `∏_{p ≤ N} (1 - 1/p)`. -/
def primeEulerOneMinusInvRat (N : Nat) : ℚ :=
  productLowerRat (primesLE N) oneMinusInvRat

/-- Finite prime product `∏_{p ≤ N} (1 + 1/p)`. -/
noncomputable def primeEulerOnePlusInv (N : Nat) : ℝ :=
  finiteProduct (primesLE N) fun p => (1 : ℝ) + 1 / (p : ℝ)

/-- Exact rational value of `∏_{p ≤ N} (1 + 1/p)`. -/
def primeEulerOnePlusInvRat (N : Nat) : ℚ :=
  productLowerRat (primesLE N) onePlusInvRat

/-- Boolean interval checker for `∏_{p ≤ N} (1 - 1/p)`. -/
def checkPrimeEulerOneMinusInvInterval (N : Nat) (lo hi : ℚ) : Bool :=
  LeanCert.Cert.checkRatInterval (primeEulerOneMinusInvRat N)
    (primeEulerOneMinusInvRat N) lo hi

/-- Boolean interval checker for `∏_{p ≤ N} (1 + 1/p)`. -/
def checkPrimeEulerOnePlusInvInterval (N : Nat) (lo hi : ℚ) : Bool :=
  LeanCert.Cert.checkRatInterval (primeEulerOnePlusInvRat N)
    (primeEulerOnePlusInvRat N) lo hi

end LeanCert.ANT
