/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.DualNumber
public import Tengoku.Seed.Analysis.Normed.Algebra.TrivSqZeroExt

/-!
# Results on `DualNumber R` related to the norm

These are just restatements of similar statements about `TrivSqZeroExt R M`.

## Main results

* `exp_eps`

-/

public section

open NormedSpace -- For `NormedSpace.exp`.

namespace DualNumber

open TrivSqZeroExt

variable {R : Type*}
variable [CommRing R] [Algebra ℚ R]
variable [UniformSpace R] [IsTopologicalRing R] [T2Space R]

/--
@isnad1 id=eq.0h1v.s7.e736435ce42d from=seed src=0 shape=e47ffad3 vocab=4648ed50
-/
@[simp]
theorem exp_eps : exp (eps : DualNumber R) = 1 + eps :=
  exp_inr _

/--
@isnad1 id=eq.0h2v.s7.11278a158972 from=seed src=0 shape=36efa9bb vocab=96612b42
-/
@[simp]
theorem exp_smul_eps (r : R) : exp (r • eps : DualNumber R) = 1 + r • eps := by
  rw [eps, ← inr_smul, exp_inr]

end DualNumber
