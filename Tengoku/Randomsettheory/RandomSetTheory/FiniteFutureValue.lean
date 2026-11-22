/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.FiniteSupremumRioIID

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Future-integrated value functions on a finite independent product

This file constructs the concrete value functions which occur in the Doob
decomposition of a statistic of finitely many independent coordinates.  At
time `i + 1`, the coordinates up to `i` are frozen and the block
`[i + 1, n)` is integrated under its joint law.

The construction is deliberately phrased on an arbitrary probability space:
the future product law is obtained as the pushforward of the actual future
block.  Independence identifies the resulting integral with the conditional
expectation.  Most importantly, a terminal replace-one modulus is preserved
by future integration.  Thus no modulus for the (as yet unknown) conditional
expectation is assumed.
-/

open Real Set Finset MeasureTheory
open scoped BigOperators ProbabilityTheory ENNReal NNReal

noncomputable section

namespace ProbabilityTheory

variable {Omega Z : Type*} {mOmega : MeasurableSpace Omega}
  [MeasurableSpace Z]

/-- The coordinates whose indices lie in a finite set, bundled as one random
variable.-/
def finiteCoordinateBlock (Y : Nat -> Omega -> Z) (I : Finset Nat)
    (omega : Omega) : I -> Z :=
  fun j => Y j omega

/--
@isnad1 id=measurab.1h5v.s6.238ab2150a69 from=translated src=- shape=6d8c1f47 vocab=747fb415
-/
theorem measurable_finiteCoordinateBlock
    (Y : Nat -> Omega -> Z) (hY : forall j, Measurable (Y j))
    (I : Finset Nat) :
    Measurable (finiteCoordinateBlock Y I) := by
  exact measurable_pi_lambda _ fun j => hY j

/-- The unrevealed finite block `[i + 1, n)`.-/
abbrev finiteFutureBlock (Y : Nat -> Omega -> Z) (i n : Nat) :=
  finiteCoordinateBlock Y (Finset.Ico (i + 1) n)

/-- A mutually independent sequence makes the padded prefix through `i`
independent of the remaining finite block `[i + 1,n)`.
@isnad1 id=indepfun.2h8v.s7.abf30beb820e from=translated src=- shape=4c0cbffc vocab=f6b9f115
-/
theorem iIndepFun.indepFun_paddedPrefix_futureBlock
    {mu : Measure Omega} (z0 : Z) (Y : Nat -> Omega -> Z)
    (hIndep : iIndepFun Y mu) (hY : forall j, Measurable (Y j))
    (i n : Nat) :
    IndepFun (paddedStrictPrefix z0 Y (i + 1))
      (finiteFutureBlock Y i n) mu := by
  change IndepFun (paddedStrictPrefix z0 Y (i + 1))
    (fun omega (j : Finset.Ico (i + 1) n) => Y j omega) mu
  let S : Finset Nat := Finset.range (i + 1)
  let U : Finset Nat := Finset.Ico (i + 1) n
  have hdisjoint : Disjoint S U := by
    apply Finset.disjoint_left.mpr
    intro j hjS hjU
    have hjlt : j < i + 1 := Finset.mem_range.mp hjS
    have hjle : i + 1 <= j := (Finset.mem_Ico.mp hjU).1
    omega
  have hfinite := hIndep.indepFun_finset S U hdisjoint hY
  let extendPrefix : (S -> Z) -> (Nat -> Z) := fun values j =>
    if h : j < i + 1 then values ⟨j, Finset.mem_range.mpr h⟩ else z0
  have hextend : Measurable extendPrefix := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j < i + 1
    · have hj' : j <= i := by omega
      simpa only [extendPrefix, dite_eq_left hj, ite_eq_left hj'] using
        (measurable_pi_apply (⟨j, Finset.mem_range.mpr hj⟩ : S))
    · have hj' : ¬j <= i := by omega
      simpa only [extendPrefix, dite_eq_right hj, ite_eq_right hj'] using
        (measurable_const : Measurable (fun _ : S -> Z => z0))
  have hcomp := hfinite.comp hextend measurable_id
  have hleft :
      extendPrefix ∘ (fun omega (j : S) => Y j omega) =
        paddedStrictPrefix z0 Y (i + 1) := by
    funext omega j
    by_cases hj : j < i + 1
    · simp only [Function.comp_apply, extendPrefix, dite_eq_left hj,
        paddedStrictPrefix]
    · simp only [Function.comp_apply, extendPrefix, dite_eq_right hj,
        paddedStrictPrefix]
  rw [← hleft]
  simpa only [U, Function.id_comp] using hcomp

/-- Under identical coordinate laws, the unrevealed finite block has the
corresponding finite product law.
@isnad1 id=eq.3h8v.s9.387e9e415021 from=translated src=- shape=6a1eb6f5 vocab=faa6e80b
-/
theorem iIndepFun.map_finiteFutureBlock_eq_pi
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (Y : Nat -> Omega -> Z) (hIndep : iIndepFun Y mu)
    (hY : forall j, Measurable (Y j)) (nu : Measure Z)
    (i n : Nat) (hYlaw : forall j, j < n -> mu.map (Y j) = nu) :
    mu.map (finiteFutureBlock Y i n) =
      Measure.pi (fun _ : Finset.Ico (i + 1) n => nu) := by
  let U : Finset Nat := Finset.Ico (i + 1) n
  have hrestricted : iIndepFun (fun j : U => Y j) mu :=
    hIndep.restrict U
  have hproduct := iIndepFun.map_fun_eq_pi_map
    (f := fun j : U => Y j) (μ := mu)
    (fun j => (hY j).aemeasurable) hrestricted
  change mu.map (fun omega (j : U) => Y j omega) = _ at hproduct
  change mu.map (fun omega (j : U) => Y j omega) = _
  rw [hproduct]
  congr 1
  funext j
  exact hYlaw j (Finset.mem_Ico.mp j.property).2

/-- Merge a padded prefix through `i` and the future block `[i+1,n)` into a
vector indexed by `Fin n`.-/
def mergePrefixFuture (i n : Nat)
    (prefixFuture : (Nat -> Z) × (Finset.Ico (i + 1) n -> Z)) :
    Fin n -> Z :=
  fun j => if h : (j : Nat) < i + 1 then prefixFuture.1 j
    else prefixFuture.2
      ⟨j, Finset.mem_Ico.mpr ⟨Nat.le_of_not_gt h, j.isLt⟩⟩

/--
@isnad1 id=measurab.0h3v.s7.e4d54600c6a0 from=translated src=- shape=edd57d14 vocab=741abd72
-/
theorem measurable_mergePrefixFuture (i n : Nat) :
    Measurable (mergePrefixFuture (Z := Z) i n) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : (j : Nat) < i + 1
  · simp only [mergePrefixFuture, dite_eq_left hj]
    exact (measurable_pi_apply (j : Nat)).comp measurable_fst
  · simp only [mergePrefixFuture, dite_eq_right hj]
    exact (measurable_pi_apply
      (⟨j, Finset.mem_Ico.mpr ⟨Nat.le_of_not_gt hj, j.isLt⟩⟩ :
        Finset.Ico (i + 1) n)).comp measurable_snd

omit [MeasurableSpace Z] in
/-- Merging the actual prefix and future block recovers the first `n`
coordinates exactly.
@isnad1 id=eq.0h7v.s6.553cfa6b47b3 from=translated src=- shape=fd0e492f vocab=082f07dc
-/
theorem mergePrefixFuture_comp
    (z0 : Z) (Y : Nat -> Omega -> Z) (i n : Nat) (omega : Omega) :
    mergePrefixFuture i n
        (paddedStrictPrefix z0 Y (i + 1) omega,
          finiteFutureBlock Y i n omega) =
      fun j : Fin n => Y j omega := by
  funext j
  by_cases hj : (j : Nat) < i + 1
  · simp [mergePrefixFuture, paddedStrictPrefix, hj]
  · simp [mergePrefixFuture, finiteFutureBlock,
      finiteCoordinateBlock, hj]

/-! ## Future-integrated values -/

/-- Integrate a terminal statistic over the finite unrevealed block while
keeping the padded prefix fixed.-/
def nextPrefixFutureValue (mu : Measure Omega)
    (Y : Nat -> Omega -> Z) (i n : Nat)
    (Phi : (Fin n -> Z) -> Real) (pastCurrent : Nat -> Z) : Real :=
  ∫ future, Phi (mergePrefixFuture i n (pastCurrent, future))
    ∂(mu.map (finiteFutureBlock Y i n))

/-- The same value function displayed as a function of the strict past and
the current coordinate.-/
def finiteFutureValue (mu : Measure Omega) (z0 : Z)
    (Y : Nat -> Omega -> Z) (i n : Nat)
    (Phi : (Fin n -> Z) -> Real) (past : Nat -> Z) (current : Z) : Real :=
  nextPrefixFutureValue mu Y i n Phi
    (insertCurrentIntoPaddedPrefix z0 i (past, current))

/--
@isnad1 id=strongly.1h8v.s6.79d319610a3c from=translated src=- shape=1652f65f vocab=60196787
-/
theorem stronglyMeasurable_nextPrefixFutureValue
    {mu : Measure Omega} [SFinite mu]
    (Y : Nat -> Omega -> Z) (i n : Nat)
    (Phi : (Fin n -> Z) -> Real) (hPhi : StronglyMeasurable Phi) :
    StronglyMeasurable (nextPrefixFutureValue mu Y i n Phi) := by
  have hjoint : StronglyMeasurable
      (fun pf : (Nat -> Z) × (Finset.Ico (i + 1) n -> Z) =>
        Phi (mergePrefixFuture i n pf)) :=
    hPhi.comp_measurable (measurable_mergePrefixFuture i n)
  change StronglyMeasurable (fun pastCurrent : Nat -> Z =>
    ∫ future, Phi (mergePrefixFuture i n (pastCurrent, future))
      ∂(mu.map (finiteFutureBlock Y i n)))
  exact hjoint.integral_prod_right'

/--
@isnad1 id=strongly.1h9v.s6.1bfb5d15a10e from=translated src=- shape=2112adbc vocab=235d1606
-/
theorem stronglyMeasurable_uncurry_finiteFutureValue
    {mu : Measure Omega} [SFinite mu]
    (z0 : Z) (Y : Nat -> Omega -> Z)
    (i n : Nat) (Phi : (Fin n -> Z) -> Real)
    (hPhi : StronglyMeasurable Phi) :
    StronglyMeasurable
      (Function.uncurry (finiteFutureValue mu z0 Y i n Phi)) := by
  have hnext := stronglyMeasurable_nextPrefixFutureValue
    (mu := mu) Y i n Phi hPhi
  exact hnext.comp_measurable (measurable_insertCurrentIntoPaddedPrefix z0 i)

/-- A finite sum of coordinatewise integrable envelopes makes every frozen
past/current future slice integrable.  This is the non-bounded integrability
input needed to apply the integral contraction theorem to empirical
statistics.
@isnad1 id=integrab.7h13v.s9.e34cdc08774a from=translated src=- shape=9d2e8363 vocab=59969428
-/
theorem integrable_terminal_futureSlice_of_sum_envelope
    {mu : Measure Omega} {nu : Measure Z}
    [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu]
    (z0 : Z) (Y : Nat -> Omega -> Z)
    (hY : forall j, Measurable (Y j)) (hIndep : iIndepFun Y mu)
    (i n : Nat) (hYlaw : forall j, j < n -> mu.map (Y j) = nu)
    (Phi : (Fin n -> Z) -> Real)
    (hPhi : StronglyMeasurable Phi) (A : Fin n -> Z -> Real)
    (hAint : forall j, Integrable (A j) nu)
    (hA : forall j z, 0 <= A j z)
    (hdom : forall x, abs (Phi x) <= ∑ j : Fin n, A j (x j))
    (past : Nat -> Z) (current : Z) :
    Integrable (fun future => Phi (mergePrefixFuture i n
      (insertCurrentIntoPaddedPrefix z0 i (past, current), future)))
      (mu.map (finiteFutureBlock Y i n)) := by
  rw [hIndep.map_finiteFutureBlock_eq_pi Y hY nu i n hYlaw]
  let I := Finset.Ico (i + 1) n
  let kappa : Measure (I -> Z) := Measure.pi (fun _ : I => nu)
  let fixed : Nat -> Z :=
    insertCurrentIntoPaddedPrefix z0 i (past, current)
  have hcomponent : forall j : Fin n,
      Integrable (fun future : I -> Z =>
        A j (mergePrefixFuture i n (fixed, future) j)) kappa := by
    intro j
    by_cases hj : (j : Nat) < i + 1
    · simpa only [mergePrefixFuture, dite_eq_left hj] using
        (integrable_const (μ := kappa) (A j (fixed j)))
    · let k : I :=
        ⟨j, Finset.mem_Ico.mpr ⟨Nat.le_of_not_gt hj, j.isLt⟩⟩
      have hmap : MeasurePreserving (Function.eval k) kappa nu := by
        exact measurePreserving_eval (fun _ : I => nu) k
      have hcomp := hmap.integrable_comp_of_integrable (hAint j)
      change Integrable (fun future : I -> Z => A j (future k)) kappa at hcomp
      simpa only [kappa, Function.comp_apply, mergePrefixFuture,
        dite_eq_right hj, k] using hcomp
  have henvelope : Integrable (fun future : I -> Z =>
      ∑ j : Fin n, A j (mergePrefixFuture i n (fixed, future) j)) kappa :=
    integrable_finsetSum Finset.univ fun j _ => hcomponent j
  have hterminalStrong : StronglyMeasurable (fun future : I -> Z =>
      Phi (mergePrefixFuture i n (fixed, future))) := by
    exact hPhi.comp_measurable ((measurable_mergePrefixFuture i n).comp
      (measurable_const.prodMk measurable_id))
  apply henvelope.mono' hterminalStrong.aestronglyMeasurable
  filter_upwards [] with future
  have hsumNonneg : 0 <=
      ∑ j : Fin n, A j (mergePrefixFuture i n (fixed, future) j) :=
    Finset.sum_nonneg fun j _ => hA j _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hsumNonneg] using
    hdom (mergePrefixFuture i n (fixed, future))

/-- The future-integrated value is a concrete version of the conditional
expectation at time `i + 1` of a terminal statistic of the first `n`
coordinates.
@isnad1 id=eventual.4h9v.s7.fed9fd160da3 from=translated src=- shape=d3e9c228 vocab=1dfe8eb2
-/
theorem condExp_terminal_ae_eq_finiteFutureValue
    [StandardBorelSpace Z] [Nonempty Z]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (z0 : Z) (Y : Nat -> Omega -> Z)
    (hY : forall j, Measurable (Y j)) (hIndep : iIndepFun Y mu)
    (i n : Nat) (Phi : (Fin n -> Z) -> Real)
    (hPhi : StronglyMeasurable Phi)
    (hterminalInt : Integrable
      (fun omega => Phi (fun j : Fin n => Y j omega)) mu) :
    mu[(fun omega => Phi (fun j : Fin n => Y j omega)) |
        strictPrefixFiltration Y hY (i + 1)] =ᵐ[mu]
      fun omega => finiteFutureValue mu z0 Y i n Phi
        (paddedStrictPrefix z0 Y i omega) (Y i omega) := by
  let P : Omega -> (Nat -> Z) := paddedStrictPrefix z0 Y (i + 1)
  let U : Omega -> (Finset.Ico (i + 1) n -> Z) :=
    finiteFutureBlock Y i n
  let H : (Nat -> Z) × (Finset.Ico (i + 1) n -> Z) -> Real :=
    fun pu => Phi (mergePrefixFuture i n pu)
  have hP : Measurable P := measurable_paddedStrictPrefix z0 Y hY (i + 1)
  have hU : Measurable U :=
    measurable_finiteCoordinateBlock Y hY (Finset.Ico (i + 1) n)
  have hPU : IndepFun P U mu := by
    exact hIndep.indepFun_paddedPrefix_futureBlock z0 Y hY i n
  have hH : StronglyMeasurable H :=
    hPhi.comp_measurable (measurable_mergePrefixFuture i n)
  have hterminalEq :
      (fun omega => H (P omega, U omega)) =
        fun omega => Phi (fun j : Fin n => Y j omega) := by
    funext omega
    exact congrArg Phi (mergePrefixFuture_comp z0 Y i n omega)
  have hreconstructedInt : Integrable
      (fun omega => H (P omega, U omega)) mu := by
    rw [hterminalEq]
    exact hterminalInt
  have hbase := hPU.condExp_prod_ae_eq_integral_map hP hU H hH
    hreconstructedInt
  rw [hterminalEq] at hbase
  rw [strictPrefixFiltration_eq_comap_paddedStrictPrefix
    z0 Y hY (i + 1)]
  filter_upwards [hbase] with omega homega
  rw [homega]
  change (∫ future, Phi (mergePrefixFuture i n
      (paddedStrictPrefix z0 Y (i + 1) omega, future))
        ∂(mu.map (finiteFutureBlock Y i n))) = _
  unfold finiteFutureValue nextPrefixFutureValue
  rw [insertCurrentIntoPaddedPrefix_comp]

/-! ## Contraction of terminal replace-one moduli -/

omit [MeasurableSpace Z] in
/--
@isnad1 id=eq.1h7v.s6.61692786f274 from=translated src=- shape=66f13dca vocab=280f010e
-/
theorem mergePrefixFuture_insertCurrent_apply_current
    (z0 : Z) (i n : Nat) (hi : i < n)
    (past : Nat -> Z) (current : Z)
    (future : Finset.Ico (i + 1) n -> Z) :
    mergePrefixFuture i n
        (insertCurrentIntoPaddedPrefix z0 i (past, current), future)
        (⟨i, hi⟩ : Fin n) = current := by
  simp [mergePrefixFuture, insertCurrentIntoPaddedPrefix]

omit [MeasurableSpace Z] in
/-- Changing the displayed current coordinate leaves every other coordinate
of the merged terminal vector unchanged.
@isnad1 id=eq.2h9v.s7.eb28bf121a29 from=translated src=- shape=5a6f129b vocab=a0e1e823
-/
theorem mergePrefixFuture_insertCurrent_eq_of_ne
    (z0 : Z) (i n : Nat) (hi : i < n)
    (past : Nat -> Z) (current current' : Z)
    (future : Finset.Ico (i + 1) n -> Z) (j : Fin n)
    (hj : j ≠ (⟨i, hi⟩ : Fin n)) :
    mergePrefixFuture i n
        (insertCurrentIntoPaddedPrefix z0 i (past, current), future) j =
      mergePrefixFuture i n
        (insertCurrentIntoPaddedPrefix z0 i (past, current'), future) j := by
  unfold mergePrefixFuture
  by_cases hjprefix : (j : Nat) < i + 1
  · simp only [dite_eq_left hjprefix]
    unfold insertCurrentIntoPaddedPrefix
    by_cases hjpast : (j : Nat) < i
    · simp [hjpast]
    · have hjeq : (j : Nat) = i := by omega
      have : j = (⟨i, hi⟩ : Fin n) := Fin.ext hjeq
      exact (hj this).elim
  · simp only [dite_eq_right hjprefix]

/-- Future integration preserves a terminal replace-one envelope.

Unlike the abstract ghost endpoint, the hypothesis `hreplace` concerns only
the original terminal statistic `Phi`.  The desired modulus of the value
function is a conclusion, so this theorem removes the circular certificate
from the product construction.
@isnad1 id=le.4h13v.s9.307ca26e7b28 from=translated src=- shape=2f38d97d vocab=7d1c4d82
-/
theorem abs_finiteFutureValue_sub_le_of_terminal_replaceOne
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    (z0 : Z) (Y : Nat -> Omega -> Z)
    (hY : forall j, Measurable (Y j))
    (i n : Nat) (hi : i < n)
    (Phi : (Fin n -> Z) -> Real) (A : Z -> Real)
    (hFiberInt : forall past current,
      Integrable (fun future => Phi (mergePrefixFuture i n
        (insertCurrentIntoPaddedPrefix z0 i (past, current), future)))
        (mu.map (finiteFutureBlock Y i n)))
    (hreplace : forall x x' : Fin n -> Z,
      (forall j, j ≠ (⟨i, hi⟩ : Fin n) -> x j = x' j) ->
      abs (Phi x - Phi x') <=
        A (x ⟨i, hi⟩) + A (x' ⟨i, hi⟩))
    (past : Nat -> Z) (current current' : Z) :
    abs (finiteFutureValue mu z0 Y i n Phi past current -
        finiteFutureValue mu z0 Y i n Phi past current') <=
      A current + A current' := by
  let U : Omega -> (Finset.Ico (i + 1) n -> Z) :=
    finiteFutureBlock Y i n
  have hU : Measurable U :=
    measurable_finiteCoordinateBlock Y hY (Finset.Ico (i + 1) n)
  letI : IsProbabilityMeasure (mu.map U) :=
    Measure.isProbabilityMeasure_map hU.aemeasurable
  unfold finiteFutureValue nextPrefixFutureValue
  apply abs_integral_sub_integral_le_add_envelopes
      (kappa := mu.map U)
      (fun past current future => Phi (mergePrefixFuture i n
        (insertCurrentIntoPaddedPrefix z0 i (past, current), future))) A
  · intro b z
    simpa only [U] using hFiberInt b z
  · intro b z z' future
    let x : Fin n -> Z := mergePrefixFuture i n
      (insertCurrentIntoPaddedPrefix z0 i (b, z), future)
    let x' : Fin n -> Z := mergePrefixFuture i n
      (insertCurrentIntoPaddedPrefix z0 i (b, z'), future)
    have hterminal := hreplace x x' (fun j hj =>
      mergePrefixFuture_insertCurrent_eq_of_ne
        z0 i n hi b z z' future j hj)
    have hxi : x ⟨i, hi⟩ = z :=
      mergePrefixFuture_insertCurrent_apply_current
        z0 i n hi b z future
    have hxi' : x' ⟨i, hi⟩ = z' :=
      mergePrefixFuture_insertCurrent_apply_current
        z0 i n hi b z' future
    simpa only [x, x', hxi, hxi'] using hterminal

/-! ## Canonical Doob representation -/

/-- The successor Doob difference of a finite-coordinate statistic is the
centred current fibre of its concrete future-integrated value function.
@isnad1 id=eventual.4h9v.s8.4e02b77f8ab6 from=translated src=- shape=e92ae183 vocab=e0d7db24
-/
theorem doobCenteredDifference_terminal_succ_ae_eq_finiteFutureValue
    {mu : Measure Omega}
    [StandardBorelSpace Omega] [IsProbabilityMeasure mu]
    [StandardBorelSpace Z] [Nonempty Z]
    (z0 : Z) (Y : Nat -> Omega -> Z)
    (hY : forall j, Measurable (Y j)) (hIndep : iIndepFun Y mu)
    (i n : Nat) (Phi : (Fin n -> Z) -> Real)
    (hPhi : StronglyMeasurable Phi)
    (hterminalInt : Integrable
      (fun omega => Phi (fun j : Fin n => Y j omega)) mu) :
    doobCenteredDifference (strictPrefixFiltration Y hY) mu
        (fun omega => Phi (fun j : Fin n => Y j omega)) (i + 1) =ᵐ[mu]
      fun omega =>
        finiteFutureValue mu z0 Y i n Phi
            (paddedStrictPrefix z0 Y i omega) (Y i omega) -
          ∫ z, finiteFutureValue mu z0 Y i n Phi
            (paddedStrictPrefix z0 Y i omega) z ∂(mu.map (Y i)) := by
  apply doobCenteredDifference_succ_ae_eq_centeredGhostFiber_of_condExp_next
    (strictPrefixFiltration Y hY)
    (fun omega => Phi (fun j : Fin n => Y j omega)) i
    (paddedStrictPrefix z0 Y i) (Y i)
  · exact hIndep.indepFun_paddedStrictPrefix z0 Y hY i
  · exact measurable_paddedStrictPrefix z0 Y hY i
  · exact hY i
  · exact strictPrefixFiltration_eq_comap_paddedStrictPrefix z0 Y hY i
  · exact stronglyMeasurable_uncurry_finiteFutureValue
      (mu := mu) z0 Y i n Phi hPhi
  · exact condExp_terminal_ae_eq_finiteFutureValue
      z0 Y hY hIndep i n Phi hPhi hterminalInt

/-! ## Terminal finite empirical suprema -/

/-- A finite supremum of coordinatewise additive statistics, viewed as a
deterministic function of a finite observation vector.-/
def finiteCoordinateSumSupremum {T : Type*}
    (s : Finset T) (hs : s.Nonempty)
    (W : Fin n -> Z -> T -> Real) (x : Fin n -> Z) : Real :=
  s.sup' hs (fun t => ∑ j : Fin n, W j (x j) t)

/-- Put the terminal envelope of coordinate `i` at Doob index `i + 1`;
index zero is the identically zero initial difference.-/
def finiteSuccessorEnvelope (A : Fin n -> Z -> Real) : Nat -> Z -> Real
  | 0 => 0
  | i + 1 => if hi : i < n then A ⟨i, hi⟩ else 0

omit [MeasurableSpace Z] in
/--
@isnad1 id=eq.0h3v.s5.a9de589c925a from=translated src=- shape=6b8c7df9 vocab=ceffba82
-/
@[simp]
theorem finiteSuccessorEnvelope_zero (A : Fin n -> Z -> Real) :
    finiteSuccessorEnvelope A 0 = 0 := rfl

omit [MeasurableSpace Z] in
/--
@isnad1 id=eq.1h4v.s5.5cba0507f1e7 from=translated src=- shape=1ccb2df6 vocab=61e96262
-/
@[simp]
theorem finiteSuccessorEnvelope_succ (A : Fin n -> Z -> Real)
    (i : Nat) (hi : i < n) :
    finiteSuccessorEnvelope A (i + 1) = A ⟨i, hi⟩ := by
  simp [finiteSuccessorEnvelope, hi]

/--
@isnad1 id=measurab.2h5v.s6.7279ef673b52 from=translated src=- shape=8f9b5dc4 vocab=355bdd2c
-/
theorem measurable_finiteCoordinateSumSupremum {T : Type*}
    (s : Finset T) (hs : s.Nonempty)
    (W : Fin n -> Z -> T -> Real)
    (hW : forall j t, t ∈ s -> Measurable (fun z => W j z t)) :
    Measurable (finiteCoordinateSumSupremum s hs W) := by
  apply measurable_finiteProcessSupremum s hs
  intro t ht
  exact Finset.measurable_sum Finset.univ fun j _ =>
    (hW j t ht).comp (measurable_pi_apply j)

omit [MeasurableSpace Z] in
/-- The terminal additive finite supremum has the expected replace-one
modulus, proved directly from the observation envelopes.
@isnad1 id=le.4h9v.s7.61933e36c90a from=translated src=- shape=f6cb34d0 vocab=458f4f80
-/
theorem abs_finiteCoordinateSumSupremum_replace_le_add_envelopes
    {T : Type*} (s : Finset T) (hs : s.Nonempty)
    (W : Fin n -> Z -> T -> Real) (A : Fin n -> Z -> Real)
    (hdom : forall j z t, t ∈ s -> abs (W j z t) <= A j z)
    (i : Nat) (hi : i < n) (x x' : Fin n -> Z)
    (hxeq : forall j, j ≠ (⟨i, hi⟩ : Fin n) -> x j = x' j) :
    abs (finiteCoordinateSumSupremum s hs W x -
        finiteCoordinateSumSupremum s hs W x') <=
      A ⟨i, hi⟩ (x ⟨i, hi⟩) + A ⟨i, hi⟩ (x' ⟨i, hi⟩) := by
  let idx : Fin n := ⟨i, hi⟩
  let r : T -> Real := fun t =>
    ∑ j ∈ (Finset.univ.erase idx), W j (x j) t
  have hsumX : forall t,
      (∑ j : Fin n, W j (x j) t) = r t + W idx (x idx) t := by
    intro t
    symm
    exact Finset.sum_erase_add _ _ (Finset.mem_univ idx)
  have hsumX' : forall t,
      (∑ j : Fin n, W j (x' j) t) = r t + W idx (x' idx) t := by
    intro t
    rw [show (∑ j : Fin n, W j (x' j) t) =
        (∑ j ∈ (Finset.univ.erase idx), W j (x' j) t) +
          W idx (x' idx) t by
      symm
      exact Finset.sum_erase_add _ _ (Finset.mem_univ idx)]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    apply congrArg (fun z => W j z t)
    exact (hxeq j (Finset.mem_erase.mp hj).1).symm
  unfold finiteCoordinateSumSupremum
  simp_rw [hsumX, hsumX']
  exact abs_finset_sup'_sum_replace_one_le_add_envelopes
    s hs r (fun t => W idx (x idx) t) (fun t => W idx (x' idx) t)
      (hdom idx (x idx)) (hdom idx (x' idx))

omit [MeasurableSpace Z] in
/-- The sum of the observation envelopes is a common envelope for the
terminal finite supremum.
@isnad1 id=le.3h7v.s6.8f734972c8e0 from=translated src=- shape=e57a6844 vocab=832d1595
-/
theorem abs_finiteCoordinateSumSupremum_le_sum_envelopes
    {T : Type*} (s : Finset T) (hs : s.Nonempty)
    (W : Fin n -> Z -> T -> Real) (A : Fin n -> Z -> Real)
    (hA : forall j z, 0 <= A j z)
    (hdom : forall j z t, t ∈ s -> abs (W j z t) <= A j z)
    (x : Fin n -> Z) :
    abs (finiteCoordinateSumSupremum s hs W x) <=
      ∑ j : Fin n, A j (x j) := by
  have hsumNonneg : 0 <= ∑ j : Fin n, A j (x j) :=
    Finset.sum_nonneg fun j _ => hA j _
  have hcoordinate : forall t, t ∈ s ->
      abs (∑ j : Fin n, W j (x j) t) <=
        ∑ j : Fin n, A j (x j) := by
    intro t ht
    calc
      abs (∑ j : Fin n, W j (x j) t) <=
          ∑ j : Fin n, abs (W j (x j) t) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ j : Fin n, A j (x j) := by
        exact Finset.sum_le_sum fun j _ => hdom j (x j) t ht
  have hbound := abs_finiteProcessSupremum_le s hs
    (fun t (_ : Unit) => ∑ j : Fin n, W j (x j) t)
    (fun _ : Unit => ∑ j : Fin n, A j (x j))
    (fun _ t ht => by
      simpa only [abs_of_nonneg hsumNonneg] using hcoordinate t ht) ()
  simpa only [finiteCoordinateSumSupremum, finiteProcessSupremum,
    abs_of_nonneg hsumNonneg] using hbound

/-- Every frozen future slice of an additive finite supremum is integrable
from ordinary `L¹` coordinate envelopes.
@isnad1 id=integrab.8h15v.s9.395c2a1ce3d3 from=translated src=- shape=c1be38b4 vocab=030d61a9
-/
theorem integrable_finiteCoordinateSumSupremum_futureSlice
    {T : Type*} {mu : Measure Omega} {nu : Measure Z}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (z0 : Z) (Y : Nat -> Omega -> Z)
    (hY : forall j, Measurable (Y j)) (hIndep : iIndepFun Y mu)
    (i n : Nat) (hYlaw : forall j, j < n -> mu.map (Y j) = nu)
    (s : Finset T) (hs : s.Nonempty)
    (W : Fin n -> Z -> T -> Real) (A : Fin n -> Z -> Real)
    (hW : forall j t, t ∈ s -> Measurable (fun z => W j z t))
    (hAint : forall j, Integrable (A j) nu)
    (hA : forall j z, 0 <= A j z)
    (hdom : forall j z t, t ∈ s -> abs (W j z t) <= A j z)
    (past : Nat -> Z) (current : Z) :
    Integrable (fun future => finiteCoordinateSumSupremum s hs W
      (mergePrefixFuture i n
        (insertCurrentIntoPaddedPrefix z0 i (past, current), future)))
      (mu.map (finiteFutureBlock Y i n)) := by
  apply integrable_terminal_futureSlice_of_sum_envelope
    z0 Y hY hIndep i n hYlaw
    (finiteCoordinateSumSupremum s hs W)
    (measurable_finiteCoordinateSumSupremum s hs W hW).stronglyMeasurable
    A hAint hA
  exact abs_finiteCoordinateSumSupremum_le_sum_envelopes
    s hs W A hA hdom

/-- Concrete, non-circular replace-one modulus for the future-integrated
finite empirical supremum.  Its assumptions mention only the primitive
coordinate summands and their ordinary envelopes.
@isnad1 id=le.9h16v.s8.c314cef021ae from=translated src=- shape=35b22f12 vocab=e497437a
-/
theorem abs_finiteFutureValue_coordinateSumSupremum_sub_le
    {T : Type*} {mu : Measure Omega} {nu : Measure Z}
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (z0 : Z) (Y : Nat -> Omega -> Z)
    (hY : forall j, Measurable (Y j)) (hIndep : iIndepFun Y mu)
    (i n : Nat) (hi : i < n)
    (hYlaw : forall j, j < n -> mu.map (Y j) = nu)
    (s : Finset T) (hs : s.Nonempty)
    (W : Fin n -> Z -> T -> Real) (A : Fin n -> Z -> Real)
    (hW : forall j t, t ∈ s -> Measurable (fun z => W j z t))
    (hAint : forall j, Integrable (A j) nu)
    (hA : forall j z, 0 <= A j z)
    (hdom : forall j z t, t ∈ s -> abs (W j z t) <= A j z)
    (past : Nat -> Z) (current current' : Z) :
    abs (finiteFutureValue mu z0 Y i n
          (finiteCoordinateSumSupremum s hs W) past current -
        finiteFutureValue mu z0 Y i n
          (finiteCoordinateSumSupremum s hs W) past current') <=
      A ⟨i, hi⟩ current + A ⟨i, hi⟩ current' := by
  apply abs_finiteFutureValue_sub_le_of_terminal_replaceOne
    z0 Y hY i n hi (finiteCoordinateSumSupremum s hs W)
      (A ⟨i, hi⟩)
  · exact integrable_finiteCoordinateSumSupremum_futureSlice
      z0 Y hY hIndep i n hYlaw s hs W A hW hAint hA hdom
  · intro x x' hxeq
    exact abs_finiteCoordinateSumSupremum_replace_le_add_envelopes
      s hs W A hdom i hi x x' hxeq

end ProbabilityTheory
