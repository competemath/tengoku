/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter1.Section1_2.Gcd

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Section 1.2: Least Common Multiple

$G \in K[X]$ is a *least common multiple* of $P$ and $Q$ if $P$ and $Q$
both divide $G$, and any common multiple of $P$ and $Q$ is a multiple of
$G$. Like the GCD, the LCM is unique only up to units.
-/

namespace Azurite.BPR

open Polynomial

variable {K : Type*} [Field K]

/-- BPR: G is a least common multiple of P and Q if
    G is a multiple of both P and Q, and any common multiple of P and Q
    is a multiple of G.-/
def IsLCM (G P Q : K[X]) : Prop :=
  P ∣ G ∧ Q ∣ G ∧ ∀ M : K[X], P ∣ M → Q ∣ M → G ∣ M

/-- Mathlib's `lcm P Q` satisfies the BPR IsLCM relation.
@isnad1 id=islcm.0h3v.s5.e65a9b21bfc0 from=translated src=- shape=7dec5008 vocab=aad83f3a
-/
theorem lcm_isLCM (P Q : K[X]) : IsLCM (lcm P Q) P Q :=
  ⟨dvd_lcm_left P Q, dvd_lcm_right P Q, fun _ hP hQ => lcm_dvd hP hQ⟩

/-- Any two LCMs of P and Q are associates (differ by a unit).
@isnad1 id=associat.2h5v.s6.a64fdfd91c27 from=translated src=- shape=76421fc2 vocab=8d19e0dd
-/
theorem isLCM_associated {G₁ G₂ P Q : K[X]}
    (h₁ : IsLCM G₁ P Q) (h₂ : IsLCM G₂ P Q) :
    Associated G₁ G₂ :=
  associated_of_dvd_dvd (h₁.2.2 G₂ h₂.1 h₂.2.1) (h₂.2.2 G₁ h₁.1 h₁.2.1)

/-- The degree of the LCM of P and Q. Well-defined since any two LCMs
    have the same degree (by `isLCM_associated`).-/
noncomputable def degLcm (P Q : K[X]) : WithBot ℕ := (lcm P Q).degree

/-- Any IsLCM witness has the same degree as `degLcm P Q`.
@isnad1 id=eq.1h4v.s5.d96a881983a5 from=translated src=- shape=c785f603 vocab=5998045f
-/
theorem isLCM_degree_eq_degLcm {G P Q : K[X]} (h : IsLCM G P Q) :
    G.degree = degLcm P Q :=
  degree_eq_degree_of_associated
    (associated_of_dvd_dvd
      (h.2.2 _ (dvd_lcm_left P Q) (dvd_lcm_right P Q))
      ((lcm_isLCM P Q).2.2 _ h.1 h.2.1))

end Azurite.BPR
