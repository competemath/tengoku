/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteSupremumRioFuture
import Tengoku.Randomsettheory.RandomSetTheory.StrongMomentRioConfidence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Confidence form of the finite future-integrated Rio endpoint

This module removes the free truncation level from
`conditionalValueAtRisk_finiteCoordinateSumSupremum_le_rio` by choosing the
canonical order-`q` confidence scale.  All future-value, Doob, ghost and
replace-one constructions remain internal to the underlying endpoint.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega T Z : Type*} {mOmega : MeasurableSpace Omega}
  [MeasurableSpace Z]

/-- Finite-coordinate Rio bound with no free truncation parameter.
@isnad1 id=le.15h16v.s8.40cb76d5eac1 from=translated src=- shape=14354128 vocab=769b8027
-/
theorem conditionalValueAtRisk_finiteCoordinateSumSupremum_le_rioConfidence
    {mu : Measure Omega} {nu : Measure Z}
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    [StandardBorelSpace Z] [Nonempty Z] [IsProbabilityMeasure nu]
    (z0 : Z) (Y : Nat -> Omega -> Z)
    (hY : forall i, Measurable (Y i)) (hIndep : iIndepFun Y mu)
    (s : Finset T) (hs : s.Nonempty)
    (n q : Nat) (hq : 3 <= q)
    (W : Fin n -> Z -> T -> Real) (A : Fin n -> Z -> Real)
    (hYlaw : forall i, i < n -> mu.map (Y i) = nu)
    (hW : forall j t, t ∈ s -> Measurable (fun z => W j z t))
    (hAq : forall j, MemLp (A j) q nu)
    (hA : forall j z, 0 <= A j z)
    (hdom : forall j z t, t ∈ s -> abs (W j z t) <= A j z)
    {V Q alpha : Real} (hV : 0 < V) (hQ : 0 < Q)
    (hsecond :
      (∑ i : Fin n, replaceOneCenteredMoment nu (A i) 2) <= V)
    (hmomentQ :
      (∑ i : Fin n, replaceOneCenteredMoment nu (A i) q) <= Q)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    conditionalValueAtRisk alpha
        (fun omega =>
          finiteCoordinateSumSupremum s hs W (fun j => Y j omega) -
            ∫ z, finiteCoordinateSumSupremum s hs W
              (fun j => Y j z) ∂mu) mu <=
      rioStrongMomentConfidenceRadius q V Q alpha := by
  have hRio := conditionalValueAtRisk_finiteCoordinateSumSupremum_le_rio
    z0 Y hY hIndep s hs n q hq W A hYlaw hW hAq hA hdom
      hV hQ (rioConfidenceScale_pos hQ halpha0) hsecond hmomentQ
      halpha0 halpha1 (rio_scale_condition (by omega) hQ halpha0)
  exact conditionalValueAtRisk_le_rioStrongMomentConfidenceRadius
    hq hQ halpha0 hRio

end ProbabilityTheory
