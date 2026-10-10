/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.AndersonConjecture.Anderson.Jensen.NSubring
import Tengoku

/-!
# Transcendental Extension of N-subrings

Adjoining a transcendental element to an N-subring R of a complete
local domain T and localising at the intersection with the maximal
ideal yields a new N-subring.

Loepp, "Constructing local generic formal fibers", 1997, Lemma 11.
-/

noncomputable section

open Cardinal Ideal Polynomial Set Pointwise

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-!
## Localization Carrier

The subring R[x]_{R[x] ∩ M} inside T, consisting of fractions p(x)/q(x)
where q(x) is a unit in T (equivalently, q(x) ∉ M).
-/

/-- The carrier set of R[x] localized at R[x] ∩ M, viewed inside T.
An element t ∈ T is in this set iff t = p(x)/q(x) for some p,q ∈ R[X]
with q(x) a unit in T (i.e., q(x) ∉ M). -/
def adjoinLocSet (R : NSubring T) (x : T) : Set T :=
  { t : T | ∃ (p q : Polynomial R.carrier),
    (aeval x q : T) ∉ IsLocalRing.maximalIdeal T ∧
    t * (aeval x q : T) = (aeval x p : T) }

/-!
## Transcendental Extension (Loepp Lemma 11)

If x ∈ T is transcendental over Frac(R) and avoids a suitable set of primes,
then R[x] localized at M is again an N-subring.
-/

end
