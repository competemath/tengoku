/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ruben Van de Velde
-/
module

public import Tengoku

/-!
# Units

Material destined for Mathlib.
-/

@[expose] public section

/--
@isnad1 id=isopen.1h2v.s5.2bb60020ae44 from=translated src=- shape=1757d4b1 vocab=30c54592
-/
lemma Submonoid.units_isOpen {M : Type*} [TopologicalSpace M] [Monoid M]
  {U : Submonoid M} (hU : IsOpen (U : Set M)) : IsOpen (U.units : Set Mˣ) :=
  (hU.preimage Units.continuous_val).inter (hU.preimage Units.continuous_coe_inv)
