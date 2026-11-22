/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteSupremumRioGhost
import Tengoku.Randomsettheory.RandomSetTheory.StrictPrefixFiltration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rio's finite-supremum endpoint on the canonical iid prefix filtration

This file instantiates the filtration, measurability and independence inputs
of `conditionalValueAtRisk_finiteSupremum_le_rio_of_centeredGhostFibers` for a
mutually independent coordinate sequence.  The only structural input still
left to applications is the actual identification of each Doob difference
with the displayed centred replace-one fibre.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega T Z : Type*} {mOmega : MeasurableSpace Omega}
  {mu : Measure Omega} [MeasurableSpace Z] {nu : Measure Z}

/-- Finite-supremum Rio bound on the strict-prefix filtration of mutually
independent coordinates.

Compared with the ghost endpoint, this theorem constructs automatically the
filtration, its trivial time zero, the measurable fixed-codomain past encoding
and the independence of that past from the current coordinate.
@isnad1 id=le.21h19v.s9.7a9acf6719a9 from=translated src=- shape=87c8cc8e vocab=e10a75e8
-/
theorem conditionalValueAtRisk_finiteSupremum_le_rio_of_iidGhostFibers
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    [StandardBorelSpace Z] [Nonempty Z] [IsProbabilityMeasure nu]
    (z0 : Z) (Y : Nat -> Omega -> Z)
    (hY : ∀ i, Measurable (Y i)) (hIndep : iIndepFun Y mu)
    (s : Finset T) (hs : s.Nonempty) (X : T -> Omega -> Real)
    (B : Omega -> Real) (hB : Integrable B mu)
    (hdom : ∀ omega u, u ∈ s -> abs (X u omega) <= abs (B omega))
    (G : Nat -> (Nat -> Z) -> Z -> Real) (Acoord : Nat -> Z -> Real)
    (n q : Nat) (hq : 3 <= q)
    {V Q y alpha : Real} (hV : 0 < V) (hQ : 0 < Q) (hy : 0 < y)
    (hYlaw : ∀ i < n, mu.map (Y i) = nu)
    (hXprefix : ∀ u ∈ s,
      Measurable[strictPrefixFiltration Y hY n] (X u))
    (hG : ∀ i < n, StronglyMeasurable (Function.uncurry (G i)))
    (hAq : ∀ j < n + 1, MemLp (Acoord j) q nu)
    (hA : ∀ j < n + 1, ∀ z, 0 <= Acoord j z)
    (hreplace : ∀ i < n, ∀ b z z',
      abs (G i b z - G i b z') <=
        Acoord (i + 1) z + Acoord (i + 1) z')
    (hnext : ∀ i < n,
      mu[finiteProcessSupremum s hs X |
          strictPrefixFiltration Y hY (i + 1)] =ᵐ[mu]
        fun omega =>
          G i (paddedStrictPrefix z0 Y i omega) (Y i omega))
    (hsecond :
      (∑ j ∈ Finset.range (n + 1),
        replaceOneCenteredMoment nu (Acoord j) 2) <= V)
    (hmomentQ :
      (∑ j ∈ Finset.range (n + 1),
        replaceOneCenteredMoment nu (Acoord j) q) <= Q)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hscale : Q * Real.exp (-Real.log alpha) <= y ^ q) :
    conditionalValueAtRisk alpha
        (fun omega => finiteProcessSupremum s hs X omega -
          ∫ z, finiteProcessSupremum s hs X z ∂mu) mu <=
      Real.sqrt (2 * V * (-Real.log alpha)) +
        (1 + 1 / (q : Real)) * y +
          Real.exp 1 * strongMomentQScale q Q * (-Real.log alpha) / 3 +
        alpha⁻¹ * (Q / ((q : Real) * y ^ (q - 1))) := by
  let filtration : Filtration Nat mOmega := strictPrefixFiltration Y hY
  have hX : ∀ u ∈ s, Measurable (X u) := by
    intro u hu
    exact (hXprefix u hu).mono (filtration.le n) le_rfl
  have hFint : Integrable (finiteProcessSupremum s hs X) mu :=
    integrable_finiteProcessSupremum s hs X B hB hX hdom
  have hFmeas : StronglyMeasurable[filtration n]
      (finiteProcessSupremum s hs X) :=
    (measurable_finiteProcessSupremum
      (mOmega := filtration n) s hs X hXprefix).stronglyMeasurable
  have hterminalEq :
      mu[finiteProcessSupremum s hs X | filtration n] =
        finiteProcessSupremum s hs X :=
    condExp_of_stronglyMeasurable (filtration.le n) hFmeas hFint
  have hterminal :
      mu[finiteProcessSupremum s hs X | filtration n] =ᵐ[mu]
        finiteProcessSupremum s hs X :=
    Filter.Eventually.of_forall fun omega => congrFun hterminalEq omega
  have hzero : doobCenteredDifference filtration mu
      (finiteProcessSupremum s hs X) 0 =ᵐ[mu] 0 := by
    apply doobCenteredDifference_zero_ae_eq_zero_of_filtration_zero_eq_bot
    exact strictPrefixFiltration_zero Y hY
  have hrepresentation : ∀ i < n,
      doobCenteredDifference filtration mu
          (finiteProcessSupremum s hs X) (i + 1) =ᵐ[mu]
        fun omega =>
          G i (paddedStrictPrefix z0 Y i omega) (Y i omega) -
            ∫ z, G i (paddedStrictPrefix z0 Y i omega) z ∂(mu.map (Y i)) := by
    intro i hi
    apply doobCenteredDifference_succ_ae_eq_centeredGhostFiber_of_condExp_next
      filtration (finiteProcessSupremum s hs X) i
        (paddedStrictPrefix z0 Y i) (Y i)
    · exact hIndep.indepFun_paddedStrictPrefix z0 Y hY i
    · exact measurable_paddedStrictPrefix z0 Y hY i
    · exact hY i
    · exact strictPrefixFiltration_eq_comap_paddedStrictPrefix z0 Y hY i
    · exact hG i hi
    · simpa only [filtration] using hnext i hi
  apply conditionalValueAtRisk_finiteSupremum_le_rio_of_centeredGhostFibers
      (nu := nu) filtration s hs X B hB hX hdom
      (fun i => paddedStrictPrefix z0 Y i) Y G Acoord n q hq
      hV hQ hy hterminal hzero
  · intro i hi
    exact hIndep.indepFun_paddedStrictPrefix z0 Y hY i
  · intro i hi
    exact measurable_paddedStrictPrefix z0 Y hY i
  · exact fun i hi => hY i
  · exact hYlaw
  · intro i hi
    exact strictPrefixFiltration_eq_comap_paddedStrictPrefix z0 Y hY i
  · exact hG
  · exact hAq
  · exact hA
  · exact hreplace
  · simpa only [filtration] using hrepresentation
  · exact hsecond
  · exact hmomentQ
  · exact halpha0
  · exact halpha1
  · exact hscale

end ProbabilityTheory
