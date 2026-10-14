/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Tengoku

/-!
# LeanPool.BrauerGroupNew.Mathlib.RingTheory.NonUnitalSubring.Defs

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Mathlib.RingTheory.NonUnitalSubring.Defs`.
-/

@[expose] public section

variable {R : Type*} [NonUnitalRing R]

/--
@isnad1 id=eq.0h2v.s6.fbc670e0974d from=translated src=- shape=dc9eceeb vocab=9986112b
-/
@[simp] lemma NonUnitalSubring.carrier_eq_coe (S : NonUnitalSubring R) : S.carrier = S := rfl
