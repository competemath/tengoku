/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.AndersonConjecture.Anderson.Jensen.NSubring

/-!
# Close-up: base case

Base cases of the close-up construction (Heitmann, Lemma 4).
For a principal ideal (a) in a Noetherian local domain T with
an A-extension R, one produces a new A-extension containing
a/p for suitable primes p. The divisibility case follows by
induction on the UFD factorisation in R.
-/

noncomputable section

open Cardinal Ideal

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-!
## Base case: principal ideals (n = 1)

If I = yR for y prime in R, and c ∈ yT ∩ R, then c ∈ yR already.
This follows from the N-subring height condition.
-/

/-!
## Generalized close-up for arbitrary elements

In a UFD N-subring R, if y ∈ R and c ∈ yT ∩ R, then c ∈ yR.
Proved by well-founded induction on divisibility, reducing to
close_up_principal.
-/

end
