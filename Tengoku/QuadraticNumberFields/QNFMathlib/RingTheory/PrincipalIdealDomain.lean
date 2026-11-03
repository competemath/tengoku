/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.Seed.RingTheory.PrincipalIdealDomain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Principal Ideal Rings

Material destined for mathlib.
-/

namespace RingEquiv

section Semiring

variable {R S : Type*} [Semiring R] [Semiring S]

/-- Transport `IsPrincipalIdealRing` across a ring equivalence.
@isnad1 id=isprinci.0h3v.s5.39be4db80f0f from=translated src=- shape=0751dee6 vocab=53ca3b5b
-/
theorem isPrincipalIdealRing (e : R ≃+* S) [IsPrincipalIdealRing R] :
    IsPrincipalIdealRing S :=
  IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective

/-- `IsPrincipalIdealRing` is invariant under ring equivalence.
@isnad1 id=iff.0h3v.s5.b30ebf05318d from=translated src=- shape=b720df5a vocab=53ca3b5b
-/
theorem isPrincipalIdealRing_iff (e : R ≃+* S) :
    IsPrincipalIdealRing R ↔ IsPrincipalIdealRing S := by
  constructor
  · intro _
    exact isPrincipalIdealRing e
  · intro _
    exact isPrincipalIdealRing e.symm

end Semiring

end RingEquiv
