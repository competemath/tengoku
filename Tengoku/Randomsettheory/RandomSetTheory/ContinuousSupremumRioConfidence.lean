/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteSupremumRioConfidence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rio confidence bounds for continuous additive suprema

The finite future-integrated endpoint is applied uniformly to the canonical
dense prefixes of a continuous index space.  The `L¹`/CVaR passage in
`CVaRDenseSupremum` then gives the full continuous supremum without a new
maximal-process certificate.
-/

open Real Set Finset MeasureTheory TopologicalSpace
open scoped BigOperators ProbabilityTheory ENNReal NNReal Topology

noncomputable section

namespace ProbabilityTheory

variable {Omega T Z : Type*} {mOmega : MeasurableSpace Omega}
  [MeasurableSpace Z]
  [TopologicalSpace T] [SeparableSpace T] [Nonempty T]

/-- Rio's confidence bound for the centered supremum of a continuous
coordinate-additive process.-/
theorem conditionalValueAtRisk_iSup_finiteCoordinateSumProcess_le_rioConfidence
    {mu : Measure Omega} {nu : Measure Z}
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    [StandardBorelSpace Z] [Nonempty Z] [IsProbabilityMeasure nu]
    (z0 : Z) (Y : Nat -> Omega -> Z)
    (hY : forall i, Measurable (Y i)) (hIndep : iIndepFun Y mu)
    (n q : Nat) (hq : 3 <= q)
    (W : Fin n -> Z -> T -> Real) (A : Fin n -> Z -> Real)
    (hYlaw : forall i, i < n -> mu.map (Y i) = nu)
    (hWmeas : forall j t, Measurable (fun z => W j z t))
    (hWcontinuous : forall j z, Continuous (W j z))
    (hAq : forall j, MemLp (A j) q nu)
    (hA : forall j z, 0 <= A j z)
    (hdom : forall j z t, abs (W j z t) <= A j z)
    {V Q alpha : Real} (hV : 0 < V) (hQ : 0 < Q)
    (hsecond :
      (∑ i : Fin n, replaceOneCenteredMoment nu (A i) 2) <= V)
    (hmomentQ :
      (∑ i : Fin n, replaceOneCenteredMoment nu (A i) q) <= Q)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1) :
    conditionalValueAtRisk alpha
        (fun omega =>
          (⨆ t, finiteCoordinateSumProcess Y W t omega) -
            ∫ z, (⨆ t, finiteCoordinateSumProcess Y W t z) ∂mu) mu <=
      rioStrongMomentConfidenceRadius q V Q alpha := by
  let F : Omega -> T -> Real := fun omega t =>
    finiteCoordinateSumProcess Y W t omega
  let B : Omega -> Real := fun omega => ∑ j : Fin n, A j (Y j omega)
  have hqone : (1 : ENNReal) <= (q : ENNReal) := by
    exact_mod_cast (show 1 <= q by omega)
  have hAint : forall j, Integrable (A j) nu := by
    intro j
    exact ((hAq j).mono_exponent hqone).integrable (by norm_num)
  have hBint : Integrable B mu := by
    apply integrable_finsetSum Finset.univ
    intro j _hj
    have hjmap : Integrable (A j) (mu.map (Y j)) := by
      rw [hYlaw j j.isLt]
      exact hAint j
    simpa only [B, Function.comp_def] using
      hjmap.comp_measurable (hY j)
  have hFcontinuous : forall omega, Continuous (F omega) := by
    intro omega
    exact continuous_finsetSum Finset.univ fun j _ =>
      hWcontinuous j (Y j omega)
  have hFmeas : forall k,
      Measurable (fun omega => F omega (denseSeq T k)) := by
    intro k
    exact measurable_finiteCoordinateSumProcess Y hY W (denseSeq T k)
      (fun j => hWmeas j (denseSeq T k))
  have hFdom : forall omega t, abs (F omega t) <= abs (B omega) := by
    intro omega t
    have hsum : abs (∑ j : Fin n, W j (Y j omega) t) <=
        ∑ j : Fin n, A j (Y j omega) := by
      calc
        abs (∑ j : Fin n, W j (Y j omega) t) <=
            ∑ j : Fin n, abs (W j (Y j omega) t) :=
          Finset.abs_sum_le_sum_abs _ _
        _ <= ∑ j : Fin n, A j (Y j omega) :=
          Finset.sum_le_sum fun j _ => hdom j (Y j omega) t
    have hBnonneg : 0 <= B omega :=
      Finset.sum_nonneg fun j _ => hA j (Y j omega)
    simpa only [F, finiteCoordinateSumProcess, B, abs_of_nonneg hBnonneg]
      using hsum
  apply RandomSetTheory.conditionalValueAtRisk_centered_iSup_le_of_densePrefixes
    F B hFcontinuous hFmeas hBint hFdom halpha0 halpha1.le
  intro m
  let Wdense : Fin n -> Z -> Nat -> Real :=
    fun j z k => W j z (denseSeq T k)
  have hfinite :=
    conditionalValueAtRisk_finiteCoordinateSumSupremum_le_rioConfidence
      z0 Y hY hIndep (Finset.range (m + 1))
      Finset.nonempty_range_add_one n q hq Wdense A hYlaw
      (fun j k _hk => hWmeas j (denseSeq T k)) hAq hA
      (fun j z k _hk => hdom j z (denseSeq T k))
      hV hQ hsecond hmomentQ halpha0 halpha1
  simpa only [F, Wdense, finiteCoordinateSumProcess,
    RandomSetTheory.densePrefixSupremum_eq_sup'_range,
    finiteCoordinateSumSupremum] using hfinite

end ProbabilityTheory
