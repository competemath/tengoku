/-
Copyright (c) 2026 Imperial College London. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku

/-!
# Coefficients

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

open Ideal

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- An ideal norm count used in the Odlyzko-bound argument. -/
noncomputable def idealNormCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // absNorm I = n}

/--
@isnad1 id=eq.0h2v.s4.7e97b8d8cee4 from=translated src=- shape=91d50db7 vocab=5d1c5955
-/
lemma dedekindZeta_eq_LSeries_idealNormCount (s : ℂ) :
    NumberField.dedekindZeta K s = LSeries (fun n ↦ (idealNormCount K n : ℂ)) s :=
  rfl

end NumberField.Odlyzko
