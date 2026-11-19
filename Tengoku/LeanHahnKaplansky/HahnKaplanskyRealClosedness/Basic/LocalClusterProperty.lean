/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.LeanHahnKaplansky.HahnKaplanskyRealClosedness.Basic.Cluster

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local-ring odd-cluster hypotheses with coefficient properties

This module contains the coefficient-ring part shared by the Hahn valuation-subring and
fixed-denominator Puiseux routes.  The ambient field or support predicate is deliberately kept
out of this package: a route supplies it through `P` when it needs one.
-/

namespace HahnKaplanskyRealClosedness

noncomputable section

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- Odd-cluster conditions in a local coefficient ring.  This four-field form is kept separate
from the coefficient-property package so specializations without an extra invariant retain their
original tuple shape.-/
def LocalOddClusterHypotheses
    (F : Polynomial R) (m : ℕ) : Prop :=
  0 < m ∧ Odd m ∧
    (∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal R) ∧
      IsUnit (F.coeff m)

/--
@isnad1 id=mem.2h4v.s6.8e96d5b348c3 from=translated src=- shape=966c7dcf vocab=29ab25ed
-/
theorem LocalOddClusterHypotheses.small
    {F : Polynomial R} {m : ℕ}
    (h : LocalOddClusterHypotheses F m) :
    ∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal R :=
  h.2.2.1

/--
@isnad1 id=isunit.1h3v.s5.57e63a77230d from=translated src=- shape=28cfed1b vocab=3809ff7e
-/
theorem LocalOddClusterHypotheses.unit
    {F : Polynomial R} {m : ℕ}
    (h : LocalOddClusterHypotheses F m) :
    IsUnit (F.coeff m) :=
  h.2.2.2

/-- Odd-cluster conditions in a local coefficient ring, together with a property of every
coefficient.-/
def LocalOddClusterHypothesesWithCoeffProperty
    (P : R → Prop) (F : Polynomial R) (m : ℕ) : Prop :=
  0 < m ∧ Odd m ∧
    (∀ i, P (F.coeff i)) ∧
      (∀ i, i < m → F.coeff i ∈ IsLocalRing.maximalIdeal R) ∧
        IsUnit (F.coeff m)

/-- The `m = 1` specialization of a local-ring odd-cluster package.-/
def LocalOneClusterHypothesesWithCoeffProperty
    (P : R → Prop) (F : Polynomial R) : Prop :=
  (∀ i, P (F.coeff i)) ∧
    (∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal R) ∧
      IsUnit (F.coeff 1)

/--
@isnad1 id=var.1h4v.s5.4b8f96157a2c from=translated src=- shape=811de50e vocab=5ffd6680
-/
theorem LocalOneClusterHypothesesWithCoeffProperty.coeff
    {P : R → Prop} {F : Polynomial R}
    (h : LocalOneClusterHypothesesWithCoeffProperty P F) :
    ∀ i, P (F.coeff i) :=
  h.1

/--
@isnad1 id=mem.2h4v.s6.845d15b0b354 from=translated src=- shape=959f2463 vocab=4dd35868
-/
theorem LocalOneClusterHypothesesWithCoeffProperty.small
    {P : R → Prop} {F : Polynomial R}
    (h : LocalOneClusterHypothesesWithCoeffProperty P F) :
    ∀ i, i < 1 → F.coeff i ∈ IsLocalRing.maximalIdeal R :=
  h.2.1

/--
@isnad1 id=isunit.1h3v.s5.332b7a51ffd6 from=translated src=- shape=4409dcf6 vocab=b4ad21b1
-/
theorem LocalOneClusterHypothesesWithCoeffProperty.unit
    {P : R → Prop} {F : Polynomial R}
    (h : LocalOneClusterHypothesesWithCoeffProperty P F) :
    IsUnit (F.coeff 1) :=
  h.2.2

/--
@isnad1 id=localodd.1h3v.s5.e5d6eb72e850 from=translated src=- shape=9924acef vocab=bdfa15aa
-/
theorem LocalOneClusterHypothesesWithCoeffProperty.oddClusterHypotheses
    {P : R → Prop} {F : Polynomial R}
    (h : LocalOneClusterHypothesesWithCoeffProperty P F) :
    LocalOddClusterHypothesesWithCoeffProperty P F 1 :=
  ⟨by norm_num, by norm_num, h.coeff, h.small, h.unit⟩

end

end HahnKaplanskyRealClosedness
