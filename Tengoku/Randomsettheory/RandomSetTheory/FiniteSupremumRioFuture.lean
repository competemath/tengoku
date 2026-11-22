/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteFutureValue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rio's endpoint for future-integrated finite empirical suprema

This file instantiates the canonical iid ghost-fibre endpoint for a finite
supremum of additive coordinate statistics

`sup_{t in s} sum_j W_j(Y_j, t)`.

The next conditional expectations, their Doob representations and their
replace-one moduli are all constructed by `FiniteFutureValue`.  Consequently
the public theorem below has no abstract `G`, `hnext`, `hreplace`, or Doob
certificate.  Its only quantitative hypotheses are ordinary coordinate
envelopes and the two deterministic sums of centred replace-one moments.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega T Z : Type*} {mOmega : MeasurableSpace Omega}
  [MeasurableSpace Z]

/-- The additive finite-coordinate process associated with kernels `W`.-/
def finiteCoordinateSumProcess (Y : Nat -> Omega -> Z)
    (W : Fin n -> Z -> T -> Real) (t : T) (omega : Omega) : Real :=
  ∑ j : Fin n, W j (Y j omega) t

omit [MeasurableSpace Z] in
/--
@isnad1 id=eq.1h8v.s5.39d1a04fb236 from=translated src=- shape=46b95fb1 vocab=f284e61e
-/
@[simp]
theorem finiteProcessSupremum_finiteCoordinateSumProcess
    (s : Finset T) (hs : s.Nonempty) (Y : Nat -> Omega -> Z)
    (W : Fin n -> Z -> T -> Real) (omega : Omega) :
    finiteProcessSupremum s hs (finiteCoordinateSumProcess Y W) omega =
      finiteCoordinateSumSupremum s hs W (fun j => Y j omega) := rfl

/--
@isnad1 id=measurab.2h8v.s6.23a44aa2faae from=translated src=- shape=0067de8f vocab=2055fb0f
-/
theorem measurable_finiteCoordinateSumProcess
    (Y : Nat -> Omega -> Z) (hY : forall j, Measurable (Y j))
    (W : Fin n -> Z -> T -> Real)
    (t : T) (hWt : forall j, Measurable (fun z => W j z t)) :
    Measurable (finiteCoordinateSumProcess Y W t) := by
  exact Finset.measurable_sum Finset.univ fun j _ =>
    (hWt j).comp (hY j)

/-- Every additive process coordinate is measurable with respect to the
terminal strict-prefix sigma-algebra.
@isnad1 id=measurab.2h8v.s6.4236e404f18d from=translated src=- shape=0067de8f vocab=a3dfd217
-/
theorem measurable_finiteCoordinateSumProcess_prefix
    (Y : Nat -> Omega -> Z) (hY : forall j, Measurable (Y j))
    (W : Fin n -> Z -> T -> Real)
    (t : T) (hWt : forall j, Measurable (fun z => W j z t)) :
    Measurable[strictPrefixFiltration Y hY n]
      (finiteCoordinateSumProcess Y W t) := by
  have hvector : Measurable[strictPrefixFiltration Y hY n]
      (fun omega (j : Fin n) => Y j omega) := by
    rw [strictPrefixFiltration_eq_comap Y hY n]
    exact comap_measurable _
  have hsum : Measurable (fun x : Fin n -> Z =>
      ∑ j : Fin n, W j (x j) t) :=
    Finset.measurable_sum Finset.univ fun j _ =>
      (hWt j).comp (measurable_pi_apply j)
  exact hsum.comp hvector

/-- Sum of the primitive observation envelopes.-/
def finiteCoordinateSumEnvelope (Y : Nat -> Omega -> Z)
    (A : Fin n -> Z -> Real) (omega : Omega) : Real :=
  ∑ j : Fin n, A j (Y j omega)

/--
@isnad1 id=eq.1h5v.s6.f09d166a5922 from=translated src=- shape=7828aab1 vocab=e837e9b9
-/
theorem sum_range_replaceOneCenteredMoment_finiteSuccessorEnvelope
    (nu : Measure Z) (A : Fin n -> Z -> Real) (k : Nat) (hk : 0 < k) :
    (∑ j ∈ Finset.range (n + 1),
      replaceOneCenteredMoment nu (finiteSuccessorEnvelope A j) k) =
      ∑ i : Fin n, replaceOneCenteredMoment nu (A i) k := by
  rw [← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
  simp [finiteSuccessorEnvelope, replaceOneCenteredMoment,
    replaceOneCenteredEnvelope, Nat.ne_of_gt hk]

/-- **Concrete future-integrated Rio endpoint.**

All structural martingale data are generated internally.  In particular,
the theorem does not assume conditional-expectation formulae, Doob
representations, or a modulus for an opaque value function.
@isnad1 id=le.17h17v.s9.1a4b979aca8d from=translated src=- shape=ac9c0d48 vocab=c1e47014
-/
theorem conditionalValueAtRisk_finiteCoordinateSumSupremum_le_rio
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
    {V Q y alpha : Real} (hV : 0 < V) (hQ : 0 < Q) (hy : 0 < y)
    (hsecond :
      (∑ i : Fin n, replaceOneCenteredMoment nu (A i) 2) <= V)
    (hmomentQ :
      (∑ i : Fin n, replaceOneCenteredMoment nu (A i) q) <= Q)
    (halpha0 : 0 < alpha) (halpha1 : alpha < 1)
    (hscale : Q * Real.exp (-Real.log alpha) <= y ^ q) :
    conditionalValueAtRisk alpha
        (fun omega =>
          finiteCoordinateSumSupremum s hs W (fun j => Y j omega) -
            ∫ z, finiteCoordinateSumSupremum s hs W
              (fun j => Y j z) ∂mu) mu <=
      Real.sqrt (2 * V * (-Real.log alpha)) +
        (1 + 1 / (q : Real)) * y +
          Real.exp 1 * strongMomentQScale q Q * (-Real.log alpha) / 3 +
        alpha⁻¹ * (Q / ((q : Real) * y ^ (q - 1))) := by
  let X : T -> Omega -> Real := finiteCoordinateSumProcess Y W
  let B : Omega -> Real := finiteCoordinateSumEnvelope Y A
  let Phi : (Fin n -> Z) -> Real := finiteCoordinateSumSupremum s hs W
  let G : Nat -> (Nat -> Z) -> Z -> Real := fun i =>
    finiteFutureValue mu z0 Y i n Phi
  let Acoord : Nat -> Z -> Real := finiteSuccessorEnvelope A
  have hPhiMeas : Measurable Phi := by
    exact measurable_finiteCoordinateSumSupremum s hs W
      (fun j t ht => hW j t ht)
  have hqone : (1 : ENNReal) <= (q : ENNReal) := by
    exact_mod_cast (show 1 <= q by omega)
  have hAintNu : forall j, Integrable (A j) nu := by
    intro j
    exact ((hAq j).mono_exponent hqone).integrable (by norm_num)
  have hXmeas : forall t, t ∈ s -> Measurable (X t) := by
    intro t ht
    exact measurable_finiteCoordinateSumProcess Y hY W t
      (fun j => hW j t ht)
  have hXprefix : forall t, t ∈ s ->
      Measurable[strictPrefixFiltration Y hY n] (X t) := by
    intro t ht
    exact measurable_finiteCoordinateSumProcess_prefix Y hY W t
      (fun j => hW j t ht)
  have hBint : Integrable B mu := by
    apply integrable_finsetSum Finset.univ
    intro j _
    have hjmap : Integrable (A j) (mu.map (Y j)) := by
      rw [hYlaw j j.isLt]
      exact hAintNu j
    simpa only [B, finiteCoordinateSumEnvelope, Function.comp_def] using
      hjmap.comp_measurable (hY j)
  have hBnonneg : forall omega, 0 <= B omega := by
    intro omega
    exact Finset.sum_nonneg fun j _ => hA j _
  have hdomX : forall omega t, t ∈ s ->
      abs (X t omega) <= abs (B omega) := by
    intro omega t ht
    have hsum : abs (∑ j : Fin n, W j (Y j omega) t) <=
        ∑ j : Fin n, A j (Y j omega) := by
      calc
        abs (∑ j : Fin n, W j (Y j omega) t) <=
            ∑ j : Fin n, abs (W j (Y j omega) t) :=
          Finset.abs_sum_le_sum_abs _ _
        _ <= ∑ j : Fin n, A j (Y j omega) :=
          Finset.sum_le_sum fun j _ => hdom j (Y j omega) t ht
    change abs (∑ j : Fin n, W j (Y j omega) t) <=
      abs (∑ j : Fin n, A j (Y j omega))
    calc
      abs (∑ j : Fin n, W j (Y j omega) t) <=
          ∑ j : Fin n, A j (Y j omega) := hsum
      _ = abs (∑ j : Fin n, A j (Y j omega)) :=
        (abs_of_nonneg (Finset.sum_nonneg fun j _ => hA j _)).symm
  have hterminalEq : finiteProcessSupremum s hs X =
      fun omega => Phi (fun j : Fin n => Y j omega) := by
    funext omega
    rfl
  have hFint : Integrable
      (fun omega => Phi (fun j : Fin n => Y j omega)) mu := by
    have hsup := integrable_finiteProcessSupremum
      s hs X B hBint hXmeas hdomX
    rw [← hterminalEq]
    exact hsup
  have hG : forall i, i < n ->
      StronglyMeasurable (Function.uncurry (G i)) := by
    intro i _hi
    exact stronglyMeasurable_uncurry_finiteFutureValue
      (mu := mu) z0 Y i n Phi hPhiMeas.stronglyMeasurable
  have hnext : forall i, i < n ->
      mu[finiteProcessSupremum s hs X |
          strictPrefixFiltration Y hY (i + 1)] =ᵐ[mu]
        fun omega => G i (paddedStrictPrefix z0 Y i omega) (Y i omega) := by
    intro i _hi
    have hbase := condExp_terminal_ae_eq_finiteFutureValue
      z0 Y hY hIndep i n Phi hPhiMeas.stronglyMeasurable hFint
    rw [hterminalEq]
    exact hbase
  have hreplace : forall i, i < n -> forall b z z',
      abs (G i b z - G i b z') <=
        Acoord (i + 1) z + Acoord (i + 1) z' := by
    intro i hi b z z'
    have hbase := abs_finiteFutureValue_coordinateSumSupremum_sub_le
      (mu := mu) (nu := nu) z0 Y hY hIndep i n hi hYlaw
      s hs W A hW hAintNu hA hdom b z z'
    simpa only [G, Acoord, finiteSuccessorEnvelope_succ A i hi] using hbase
  have hAcoordQ : forall j, j < n + 1 -> MemLp (Acoord j) q nu := by
    intro j hj
    cases j with
    | zero => simp [Acoord]
    | succ i =>
        have hi : i < n := by omega
        simpa only [Acoord, finiteSuccessorEnvelope_succ A i hi] using
          hAq (⟨i, hi⟩ : Fin n)
  have hAcoordNonneg : forall j, j < n + 1 -> forall z,
      0 <= Acoord j z := by
    intro j hj z
    cases j with
    | zero => simp [Acoord]
    | succ i =>
        have hi : i < n := by omega
        simpa only [Acoord, finiteSuccessorEnvelope_succ A i hi] using
          hA (⟨i, hi⟩ : Fin n) z
  have hsecondCoord :
      (∑ j ∈ Finset.range (n + 1),
        replaceOneCenteredMoment nu (Acoord j) 2) <= V := by
    rw [show Acoord = finiteSuccessorEnvelope A by rfl,
      sum_range_replaceOneCenteredMoment_finiteSuccessorEnvelope
        nu A 2 (by norm_num)]
    exact hsecond
  have hmomentQCoord :
      (∑ j ∈ Finset.range (n + 1),
        replaceOneCenteredMoment nu (Acoord j) q) <= Q := by
    rw [show Acoord = finiteSuccessorEnvelope A by rfl,
      sum_range_replaceOneCenteredMoment_finiteSuccessorEnvelope
        nu A q (by omega)]
    exact hmomentQ
  have hRio := conditionalValueAtRisk_finiteSupremum_le_rio_of_iidGhostFibers
    (mu := mu) (nu := nu) z0 Y hY hIndep s hs X B hBint hdomX
      G Acoord n q hq hV hQ hy hYlaw hXprefix hG hAcoordQ
      hAcoordNonneg hreplace hnext hsecondCoord hmomentQCoord
      halpha0 halpha1 hscale
  rw [← hterminalEq]
  exact hRio

end ProbabilityTheory
