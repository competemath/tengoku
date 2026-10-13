/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Tengoku

/-!
# Complements on homological complexes

Material destined for `Mathlib.Algebra.Homology.HomologicalComplex`.
-/

@[expose] public section

/-- The predecessor function of the cochain complex shape on `ℕ` is truncated subtraction.
@isnad1 id=eq.0h1v.s4.76c3ee81195c from=translated src=- shape=39e3a672 vocab=c35c4571
-/
lemma CochainComplex.prev_nat (j : ℕ) : (ComplexShape.up ℕ).prev j = j - 1 := by
  cases j <;> simp
