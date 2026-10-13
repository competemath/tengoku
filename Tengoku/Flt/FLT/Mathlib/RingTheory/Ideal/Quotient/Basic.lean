/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
module

public import Tengoku

/-!
# Basic

Material destined for Mathlib.
-/

@[expose] public section

variable {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]

/--
@isnad1 id=mem.0h3v.s7.80b9fb416a37 from=translated src=- shape=8f3f406c vocab=f98f386e
-/
theorem Ideal.Quotient.out_sub (x : R) : (Ideal.Quotient.mk I x).out - x ∈ I := by
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
