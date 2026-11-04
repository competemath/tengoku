/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Seed.RingTheory.LocalRing.Basic
import Tengoku.Seed.RingTheory.LocalRing.MaximalIdeal.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.5: local rings

A *local ring* `B` is a (nontrivial) ring such that for every `a ∈ B`, either `a` is invertible
or `1 + a` is invertible. A field is always a local ring.

This is Mathlib's `IsLocalRing`, whose built-in characterization uses `1 - a`; the `1 + a` form of
BPR is recorded here (`isUnit_or_isUnit_one_add_self` and `isLocalRing_of_isUnit_or_isUnit_one_add_self`,
equivalent via `a ↦ -a`). That a field is a local ring is a Mathlib instance
(`field_isLocalRing`).
-/

namespace Azurite.BPR.Chapter4

variable {R : Type*} [CommRing R]

/-- **BPR local-ring property (forward).** In a local ring, for every `a` either `a` or `1 + a`
is invertible.
@isnad1 id=or.0h2v.s6.3aec691e1a16 from=translated src=- shape=ad37d328 vocab=f4fbeb52
-/
theorem isUnit_or_isUnit_one_add_self [IsLocalRing R] (a : R) :
    IsUnit a ∨ IsUnit (1 + a) := by
  have h := IsLocalRing.isUnit_or_isUnit_one_sub_self (-a)
  rwa [IsUnit.neg_iff, sub_neg_eq_add] at h

/-- **BPR Definition (local ring).** A nontrivial ring in which, for every `a`, either `a` or
`1 + a` is invertible, is a local ring.
@isnad1 id=islocalr.1h1v.s6.3f41657aeb10 from=translated src=- shape=d91b8b09 vocab=42404d52
-/
theorem isLocalRing_of_isUnit_or_isUnit_one_add_self [Nontrivial R]
    (h : ∀ a : R, IsUnit a ∨ IsUnit (1 + a)) : IsLocalRing R :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    have h' := h (-a)
    rwa [IsUnit.neg_iff, ← sub_eq_add_neg] at h'

/-- **A field is always a local ring.**
@isnad1 id=islocalr.0h1v.s3.68b35c5d4640 from=translated src=- shape=c6850a32 vocab=80346e7b
-/
theorem field_isLocalRing (K : Type*) [Field K] : IsLocalRing K := inferInstance

/-- **BPR Exercise 4.2.** A ring `B` is local if and only if it has a unique maximal (proper) ideal,
which is then the set of non-invertible elements.
@isnad1 id=iff.0h1v.s6.91d0433b26f7 from=translated src=- shape=285ca190 vocab=8ac427e7
-/
theorem exercise_4_2 :
    IsLocalRing R ↔ ∃ I : Ideal R, I.IsMaximal ∧ (∀ J : Ideal R, J.IsMaximal → J = I)
      ∧ (↑I : Set R) = nonunits R := by
  constructor
  · intro _
    refine ⟨IsLocalRing.maximalIdeal R, IsLocalRing.maximalIdeal.isMaximal R,
      fun J hJ => IsLocalRing.eq_maximalIdeal hJ, ?_⟩
    ext x
    rw [SetLike.mem_coe]
    exact IsLocalRing.mem_maximalIdeal x
  · rintro ⟨I, hImax, huniq, -⟩
    exact IsLocalRing.of_unique_max_ideal ⟨I, hImax, huniq⟩

end Azurite.BPR.Chapter4
