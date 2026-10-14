/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Tengoku

/-!
# LeanPool.BrauerGroupNew.Mathlib.RingTheory.TwoSidedIdeal.Lattice

Imported Lean Pool material for `LeanPool.BrauerGroupNew.Mathlib.RingTheory.TwoSidedIdeal.Lattice`.
-/

@[expose] public section

namespace TwoSidedIdeal
variable {R : Type*} [NonUnitalNonAssocRing R] {I J : TwoSidedIdeal R} {x : R}

/--
@isnad1 id=iff.0h3v.s5.76d6e7146046 from=translated src=- shape=49a1ec5b vocab=44d4f9bd
-/
@[simp] lemma ringCon_inj : I.ringCon = J.ringCon ↔ I = J := ringCon_injective.eq_iff

/--
@isnad1 id=iff.0h2v.s8.fa08e041f068 from=translated src=- shape=26d4e51d vocab=ffb8e3f3
-/
@[simp] lemma ringCon_eq_top : I.ringCon = ⊤ ↔ I = ⊤ := by rw [← top_ringCon, ringCon_inj]

end TwoSidedIdeal
