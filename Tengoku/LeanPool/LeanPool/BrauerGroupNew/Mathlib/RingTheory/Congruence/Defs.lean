/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Tengoku

/-!
# Ring congruence induction compatibility

This file restores the upstream eliminator name used by the Brauer group port.
-/

@[expose] public section

namespace RingCon

variable {R : Type*} [Ring R]

/--
@isnad1 id=var.0h5v.s7.6371f238b949 from=translated src=- shape=921c655a vocab=d499d65d
-/
@[elab_as_elim]
lemma quot_ind (r : RingCon R) {motive : r.Quotient → Prop}
    (basic : ∀ x : R, motive (r.mk' x)) : ∀ x : r.Quotient, motive x := by
  intro x
  induction x using Quotient.inductionOn' with
  | h x => exact basic x

end RingCon
