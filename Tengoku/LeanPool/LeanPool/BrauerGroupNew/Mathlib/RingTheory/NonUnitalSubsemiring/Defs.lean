/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Tengoku

/-!
# LeanPool.BrauerGroupNew.Mathlib.RingTheory.NonUnitalSubsemiring.Defs

Imported Lean Pool material for
`LeanPool.BrauerGroupNew.Mathlib.RingTheory.NonUnitalSubsemiring.Defs`.
-/

@[expose] public section

variable {R : Type*} [NonUnitalSemiring R]

/--
@isnad1 id=eq.0h2v.s5.a10a00fe74ca from=translated src=- shape=d98067e9 vocab=e1a58e59
-/
@[simp]
lemma NonUnitalSubsemiring.carrier_eq_coe (S : NonUnitalSubsemiring R) : S.carrier = S := rfl
