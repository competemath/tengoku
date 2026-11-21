/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteSupremumRioFuture
import Tengoku.Randomsettheory.RandomSetTheory.SignedSupremum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rio's endpoint for finite absolute empirical suprema

This file is a thin signed-class wrapper around
`FiniteSupremumRioFuture`.  It converts

`sup_t |sum_j W_j(Y_j,t)|`

to the ordinary supremum over the doubled class `T ⊕ T`, then invokes the
existing future-integrated Rio endpoint.  No martingale, ghost-fibre or
chaining argument is repeated here.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega T Z : Type*} {mOmega : MeasurableSpace Omega}
  [MeasurableSpace Z]

/-- **Concrete signed Rio endpoint.**  The conclusion controls the centered
absolute supremum while the hypotheses remain the primitive coordinate
envelopes and their replace-one moments.-/
theorem conditionalValueAtRisk_finiteCoordinateSumAbsSupremum_le_rio
    {mu : Measure Omega} {nu : Measure Z}
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    [StandardBorelSpace Z] [Nonempty Z] [IsProbabilityMeasure nu]
    (z0 : Z) (Y : Nat → Omega → Z)
    (hY : ∀ i, Measurable (Y i)) (hIndep : iIndepFun Y mu)
    (s : Finset T) (hs : s.Nonempty)
    (n q : Nat) (hq : 3 ≤ q)
    (W : Fin n → Z → T → ℝ) (A : Fin n → Z → ℝ)
    (hYlaw : ∀ i, i < n → mu.map (Y i) = nu)
    (hW : ∀ j t, t ∈ s → Measurable (fun z ↦ W j z t))
    (hAq : ∀ j, MemLp (A j) q nu)
    (hA : ∀ j z, 0 ≤ A j z)
    (hdom : ∀ j z t, t ∈ s → |W j z t| ≤ A j z)
    {V Q y alpha : ℝ} (hV : 0 < V) (hQ : 0 < Q) (hy : 0 < y)
    (hsecond :
      (∑ i : Fin n, replaceOneCenteredMoment nu (A i) 2) ≤ V)
    (hmomentQ :
      (∑ i : Fin n, replaceOneCenteredMoment nu (A i) q) ≤ Q)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hscale : Q * Real.exp (-Real.log alpha) ≤ y ^ q) :
    conditionalValueAtRisk alpha
        (fun omega ↦
          finiteCoordinateSumAbsSupremum s hs W
              (fun j ↦ Y j omega) -
            ∫ z, finiteCoordinateSumAbsSupremum s hs W
              (fun j ↦ Y j z) ∂mu) mu ≤
      Real.sqrt (2 * V * (-Real.log alpha)) +
        (1 + 1 / (q : ℝ)) * y +
          Real.exp 1 * strongMomentQScale q Q * (-Real.log alpha) / 3 +
        alpha⁻¹ * (Q / ((q : ℝ) * y ^ (q - 1))) := by
  let ss : Finset (T ⊕ T) := signedFinset s
  have hss : ss.Nonempty := signedFinset_nonempty hs
  let Ws : Fin n → Z → T ⊕ T → ℝ := signedCoordinateKernel W
  have hWs : ∀ j u, u ∈ ss → Measurable (fun z ↦ Ws j z u) := by
    intro j u hu
    cases u with
    | inl t =>
        apply hW j t
        simpa only [ss, signedFinset, Finset.inl_mem_disjSum] using hu
    | inr t =>
        change Measurable (fun z ↦ -W j z t)
        apply (hW j t ?_).neg
        simpa only [ss, signedFinset, Finset.inr_mem_disjSum] using hu
  have hdomSigned : ∀ j z u, u ∈ ss → |Ws j z u| ≤ A j z := by
    intro j z u hu
    cases u with
    | inl t =>
        apply hdom j z t
        simpa only [ss, signedFinset, Finset.inl_mem_disjSum] using hu
    | inr t =>
        change |-W j z t| ≤ A j z
        rw [abs_neg]
        apply hdom j z t
        simpa only [ss, signedFinset, Finset.inr_mem_disjSum] using hu
  have hbase := conditionalValueAtRisk_finiteCoordinateSumSupremum_le_rio
    (mu := mu) (nu := nu) z0 Y hY hIndep ss hss n q hq Ws A
      hYlaw hWs hAq hA hdomSigned hV hQ hy hsecond hmomentQ
      halpha0 halpha1 hscale
  have hsup : ∀ x : Fin n → Z,
      finiteCoordinateSumSupremum ss hss Ws x =
        finiteCoordinateSumAbsSupremum s hs W x := by
    intro x
    change finiteCoordinateSumSupremum (signedFinset s) hss
        (signedCoordinateKernel W) x =
      finiteCoordinateSumAbsSupremum s hs W x
    exact finiteCoordinateSumSupremum_signedCoordinateKernel s hs W x
  simpa only [hsup] using hbase

end ProbabilityTheory
