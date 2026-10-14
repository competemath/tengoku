/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Robby Sneiderman
-/

import Tengoku.Formalslt.FormalSLT.AnytimeValid.ComputablePredictableBettingMixture

/-!
# Prior-mixture betting masters over an uncountable strategy class

`ComputablePredictableBettingMixture` aggregates a *finite* catalog of legal
predictable betting strategies: the master bet is the wealth-weighted average
of the catalog bets, its wealth equals the finite prior mixture, and it pays
`- log (weight j)` against any single catalog member.

This module replaces the finite prior sum by an integral against a prior
measure `strategyPrior` on an arbitrary index type `Kappa`, so the competing
class may be uncountable.  Three facts carry over verbatim with `Finset.sum`
replaced by `∫ ... ∂strategyPrior`, under explicit integrability obligations:
the one-step mixture recursion, the aggregation identity (the master's own
betting wealth equals the prior mixture of the component wealths), and the
interval legality of the master bet.

The reason the generalization is not cosmetic is the *price*.  Under a
nonatomic prior, every singleton strategy has mass zero, so
`aggregate_logWealth_regret_le`, which charges `- log (weight j)` for one
atom, has no non-vacuous singleton instance.  The replacement charged here is
the log prior mass of a measurable *set* of strategies,
`- log (strategyPrior.real B)`, against the worst component wealth on that
set.  Specializing `B` to a single atom of a finite uniform catalog recovers
`log (card)`; specializing it to a prior ball is what a covering or
modulus-of-continuity argument would consume.

Three things this module does not do.  The mixture is an integral, so unlike
the finite and dyadic masters it is not an exact rational computation; no
executability claim is made.  The e-process property is not re-proved here:
`continuumMasterWealth_eq_bettingWealthProcess` transports it from whatever
mixture-supermartingale argument supplies it for the prior integral.  And the
conclusion is a statement about realized wealth along the observed path; it is
not a statement about future, stationary, population, or deployment risk, and
no score-to-risk bridge is asserted.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace FormalSLT.AnytimeValid

noncomputable section

variable {Kappa Omega : Type*} [MeasurableSpace Kappa]

/-- The prior mixture of the component betting wealths of a strategy family
indexed by an arbitrary measurable space. -/
def continuumExpertMixtureWealth
    (strategyPrior : Measure Kappa)
    (residual : Nat -> Omega -> Real)
    (strategy : Kappa -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) : Real :=
  ∫ j, algebraicBettingWealth residual (strategy j) n omega ∂strategyPrior

/-- The unnormalized master bet: each component bet weighted by the prior
mass and the wealth that component accumulated strictly before time `n`. -/
def continuumWealthWeightedBetNumerator
    (strategyPrior : Measure Kappa)
    (residual : Nat -> Omega -> Real)
    (strategy : Kappa -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) : Real :=
  ∫ j, algebraicBettingWealth residual (strategy j) n omega *
    strategy j n omega ∂strategyPrior

/-- The master bet obtained by normalizing the prior-weighted component
wealths before the time-`n` residual is revealed. -/
def continuumWealthWeightedBet
    (strategyPrior : Measure Kappa)
    (residual : Nat -> Omega -> Real)
    (strategy : Kappa -> Nat -> Omega -> Real)
    (n : Nat) (omega : Omega) : Real :=
  continuumWealthWeightedBetNumerator strategyPrior residual strategy n omega /
    continuumExpertMixtureWealth strategyPrior residual strategy n omega

/--
@isnad1 id=eq.0h6v.s5.b8bedceeeecc from=translated src=- shape=a3ceef30 vocab=5c14c76a
-/
@[simp]
theorem continuumExpertMixtureWealth_zero
    (strategyPrior : Measure Kappa) [IsProbabilityMeasure strategyPrior]
    (residual : Nat -> Omega -> Real)
    (strategy : Kappa -> Nat -> Omega -> Real) (omega : Omega) :
    continuumExpertMixtureWealth strategyPrior residual strategy 0 omega = 1 := by
  simp [continuumExpertMixtureWealth]

/-- One-step recursion for the prior mixture.  The increment is the current
residual times the unnormalized master bet, exactly as in the finite case.
@isnad1 id=eq.2h7v.s7.e1d43de5e7b8 from=translated src=- shape=9f6500a2 vocab=3dba5685
-/
theorem continuumExpertMixtureWealth_succ
    (strategyPrior : Measure Kappa)
    (residual : Nat -> Omega -> Real)
    (strategy : Kappa -> Nat -> Omega -> Real)
    {n : Nat} {omega : Omega}
    (hwealth_int : Integrable
      (fun j => algebraicBettingWealth residual (strategy j) n omega)
      strategyPrior)
    (hnumerator_int : Integrable
      (fun j => algebraicBettingWealth residual (strategy j) n omega *
        strategy j n omega) strategyPrior) :
    continuumExpertMixtureWealth strategyPrior residual strategy (n + 1) omega =
      continuumExpertMixtureWealth strategyPrior residual strategy n omega +
        residual n omega *
          continuumWealthWeightedBetNumerator
            strategyPrior residual strategy n omega := by
  unfold continuumExpertMixtureWealth continuumWealthWeightedBetNumerator
  have hpoint :
      (fun j => algebraicBettingWealth residual (strategy j) (n + 1) omega) =
        fun j => algebraicBettingWealth residual (strategy j) n omega +
          residual n omega *
            (algebraicBettingWealth residual (strategy j) n omega *
              strategy j n omega) := by
    funext j
    rw [algebraicBettingWealth_succ]
    ring
  rw [hpoint, integral_add hwealth_int
    (hnumerator_int.const_mul (residual n omega)), integral_const_mul]

/-- The realized betting wealth of the single master bet equals the prior
mixture of all component wealths, at every time and on every path.  This is
the uncountable analogue of `aggregateWealth_eq_finiteExpertMixtureWealth`;
the induction is the same algebra with the finite sum replaced by the prior
integral.
@isnad1 id=eq.3h7v.s7.126dea2898b1 from=translated src=- shape=f0936269 vocab=1ff8ec8d
-/
theorem continuumAggregateWealth_eq_continuumExpertMixtureWealth
    (strategyPrior : Measure Kappa) [IsProbabilityMeasure strategyPrior]
    (residual : Nat -> Omega -> Real)
    (strategy : Kappa -> Nat -> Omega -> Real)
    (hwealth_int : forall n omega, Integrable
      (fun j => algebraicBettingWealth residual (strategy j) n omega)
      strategyPrior)
    (hnumerator_int : forall n omega, Integrable
      (fun j => algebraicBettingWealth residual (strategy j) n omega *
        strategy j n omega) strategyPrior)
    (hmix_ne : forall n omega,
      continuumExpertMixtureWealth strategyPrior residual strategy n omega ≠ 0) :
    forall n omega,
      algebraicBettingWealth residual
          (continuumWealthWeightedBet strategyPrior residual strategy) n omega =
        continuumExpertMixtureWealth strategyPrior residual strategy n omega := by
  intro n
  induction n with
  | zero =>
      intro omega
      simp
  | succ n ih =>
      intro omega
      rw [algebraicBettingWealth_succ, ih omega,
        continuumExpertMixtureWealth_succ strategyPrior residual strategy
          (hwealth_int n omega) (hnumerator_int n omega)]
      unfold continuumWealthWeightedBet
      have hne :
          continuumExpertMixtureWealth
            strategyPrior residual strategy n omega ≠ 0 := hmix_ne n omega
      field_simp [hne]

/-- The prior mixture dominates the prior mass of any measurable set of
strategies times the worst component wealth on that set.  This remains useful
for nonatomic priors, where singleton strategies have zero mass and the
atom-level `finiteExpertMixtureWealth_competes` has no useful instance.
@isnad1 id=le.4h9v.s7.225a08bfbbd4 from=translated src=- shape=aca09673 vocab=cafe6be9
-/
theorem continuumExpertMixtureWealth_competes_of_priorMass
    (strategyPrior : Measure Kappa) [IsFiniteMeasure strategyPrior]
    {residual : Nat -> Omega -> Real}
    {strategy : Kappa -> Nat -> Omega -> Real}
    {B : Set Kappa} (hB : MeasurableSet B) {c : Real}
    {n : Nat} {omega : Omega}
    (hwealth_nonneg : forall j,
      0 <= algebraicBettingWealth residual (strategy j) n omega)
    (hwealth_int : Integrable
      (fun j => algebraicBettingWealth residual (strategy j) n omega)
      strategyPrior)
    (hlower : forall j, j ∈ B ->
      c <= algebraicBettingWealth residual (strategy j) n omega) :
    strategyPrior.real B * c <=
      continuumExpertMixtureWealth strategyPrior residual strategy n omega := by
  have hpoint : forall j,
      B.indicator (fun _ => c) j <=
        algebraicBettingWealth residual (strategy j) n omega := by
    intro j
    by_cases hj : j ∈ B
    · rw [Set.indicator_of_mem hj]
      exact hlower j hj
    · rw [Set.indicator_of_notMem hj]
      exact hwealth_nonneg j
  have hind_int : Integrable (B.indicator (fun _ : Kappa => c)) strategyPrior :=
    (integrable_const c).indicator hB
  have hmono := integral_mono hind_int hwealth_int hpoint
  rwa [integral_indicator_const c hB, smul_eq_mul] at hmono

/-- A set of strategies with positive prior mass and a positive uniform wealth
floor makes the mixture denominator strictly positive, so the master bet is
well defined at that time.
@isnad1 id=lt.6h9v.s7.4124a65edf06 from=translated src=- shape=1152d11e vocab=df4b1fe3
-/
theorem continuumExpertMixtureWealth_pos_of_priorMass
    (strategyPrior : Measure Kappa) [IsFiniteMeasure strategyPrior]
    {residual : Nat -> Omega -> Real}
    {strategy : Kappa -> Nat -> Omega -> Real}
    {B : Set Kappa} (hB : MeasurableSet B) {c : Real}
    {n : Nat} {omega : Omega}
    (hmass_pos : 0 < strategyPrior.real B) (hc_pos : 0 < c)
    (hwealth_nonneg : forall j,
      0 <= algebraicBettingWealth residual (strategy j) n omega)
    (hwealth_int : Integrable
      (fun j => algebraicBettingWealth residual (strategy j) n omega)
      strategyPrior)
    (hlower : forall j, j ∈ B ->
      c <= algebraicBettingWealth residual (strategy j) n omega) :
    0 < continuumExpertMixtureWealth strategyPrior residual strategy n omega :=
  lt_of_lt_of_le (mul_pos hmass_pos hc_pos)
    (continuumExpertMixtureWealth_competes_of_priorMass strategyPrior hB
      hwealth_nonneg hwealth_int hlower)

/-- Log-wealth regret of the prior mixture against a positive-prior-mass set
of strategies is at most the negative log prior mass of that set.  The
competing object is a set, not an atom; `c` is the worst component wealth on
the set at the reported time, so this charges the set's prior log mass and
nothing for the choice of member.
@isnad1 id=le.6h9v.s7.41ae96ad4b99 from=translated src=- shape=0b912571 vocab=3dbd815e
-/
theorem continuumExpertMixtureWealth_logWealth_regret_le_neg_log_priorMass
    (strategyPrior : Measure Kappa) [IsFiniteMeasure strategyPrior]
    {residual : Nat -> Omega -> Real}
    {strategy : Kappa -> Nat -> Omega -> Real}
    {B : Set Kappa} (hB : MeasurableSet B) {c : Real}
    {n : Nat} {omega : Omega}
    (hmass_pos : 0 < strategyPrior.real B) (hc_pos : 0 < c)
    (hwealth_nonneg : forall j,
      0 <= algebraicBettingWealth residual (strategy j) n omega)
    (hwealth_int : Integrable
      (fun j => algebraicBettingWealth residual (strategy j) n omega)
      strategyPrior)
    (hlower : forall j, j ∈ B ->
      c <= algebraicBettingWealth residual (strategy j) n omega) :
    Real.log c -
        Real.log (continuumExpertMixtureWealth
          strategyPrior residual strategy n omega) <=
      -Real.log (strategyPrior.real B) := by
  have hcomp := continuumExpertMixtureWealth_competes_of_priorMass
    strategyPrior hB hwealth_nonneg hwealth_int hlower
  have hlog := Real.log_le_log (mul_pos hmass_pos hc_pos) hcomp
  rw [Real.log_mul hmass_pos.ne' hc_pos.ne'] at hlog
  linarith

/-- The headline statement on the master's own realized wealth: one
predictable bet, run against the observed residuals, loses at most the
negative log prior mass of any positive-mass set of competing strategies
relative to the worst member of that set.
@isnad1 id=le.8h9v.s8.24c1a3c9ce10 from=translated src=- shape=1b8a474e vocab=8dd14545
-/
theorem continuumMaster_logWealth_regret_le_neg_log_priorMass
    (strategyPrior : Measure Kappa) [IsProbabilityMeasure strategyPrior]
    (residual : Nat -> Omega -> Real)
    (strategy : Kappa -> Nat -> Omega -> Real)
    (hwealth_int : forall n omega, Integrable
      (fun j => algebraicBettingWealth residual (strategy j) n omega)
      strategyPrior)
    (hnumerator_int : forall n omega, Integrable
      (fun j => algebraicBettingWealth residual (strategy j) n omega *
        strategy j n omega) strategyPrior)
    (hmix_ne : forall n omega,
      continuumExpertMixtureWealth strategyPrior residual strategy n omega ≠ 0)
    (hwealth_nonneg : forall j n omega,
      0 <= algebraicBettingWealth residual (strategy j) n omega)
    {B : Set Kappa} (hB : MeasurableSet B) {c : Real}
    {n : Nat} {omega : Omega}
    (hmass_pos : 0 < strategyPrior.real B) (hc_pos : 0 < c)
    (hlower : forall j, j ∈ B ->
      c <= algebraicBettingWealth residual (strategy j) n omega) :
    Real.log c -
        Real.log (algebraicBettingWealth residual
          (continuumWealthWeightedBet strategyPrior residual strategy)
          n omega) <=
      -Real.log (strategyPrior.real B) := by
  rw [continuumAggregateWealth_eq_continuumExpertMixtureWealth
    strategyPrior residual strategy hwealth_int hnumerator_int hmix_ne n omega]
  exact continuumExpertMixtureWealth_logWealth_regret_le_neg_log_priorMass
    strategyPrior hB hmass_pos hc_pos (fun j => hwealth_nonneg j n omega)
    (hwealth_int n omega) hlower

/-- The master bet inherits the interval the whole class bets in, so it is a
legal bet of the same family.  This is the uncountable analogue of
`wealthWeightedBet_mem_Icc`.
@isnad1 id=mem.5h8v.s7.791c78611571 from=translated src=- shape=0a1ca2a3 vocab=e2c3dae3
-/
theorem continuumWealthWeightedBet_mem_Icc
    (strategyPrior : Measure Kappa)
    {residual : Nat -> Omega -> Real}
    {strategy : Kappa -> Nat -> Omega -> Real} {limit : Real}
    {n : Nat} {omega : Omega}
    (hwealth_nonneg : forall j,
      0 <= algebraicBettingWealth residual (strategy j) n omega)
    (hwealth_int : Integrable
      (fun j => algebraicBettingWealth residual (strategy j) n omega)
      strategyPrior)
    (hnumerator_int : Integrable
      (fun j => algebraicBettingWealth residual (strategy j) n omega *
        strategy j n omega) strategyPrior)
    (hmix_pos : 0 <
      continuumExpertMixtureWealth strategyPrior residual strategy n omega)
    (hstrategy : forall j, strategy j n omega ∈ Set.Icc (0 : Real) limit) :
    continuumWealthWeightedBet strategyPrior residual strategy n omega ∈
      Set.Icc (0 : Real) limit := by
  have hnum_nonneg :
      0 <= continuumWealthWeightedBetNumerator
        strategyPrior residual strategy n omega :=
    integral_nonneg fun j =>
      mul_nonneg (hwealth_nonneg j) (hstrategy j).1
  have hnum_le :
      continuumWealthWeightedBetNumerator
          strategyPrior residual strategy n omega <=
        limit * continuumExpertMixtureWealth
          strategyPrior residual strategy n omega := by
    unfold continuumWealthWeightedBetNumerator continuumExpertMixtureWealth
    have hpoint : forall j,
        algebraicBettingWealth residual (strategy j) n omega *
            strategy j n omega <=
          limit * algebraicBettingWealth residual (strategy j) n omega := by
      intro j
      have := mul_le_mul_of_nonneg_left (hstrategy j).2 (hwealth_nonneg j)
      linarith [this]
    have hmono := integral_mono hnumerator_int
      (hwealth_int.const_mul limit) hpoint
    rwa [integral_const_mul] at hmono
  exact ⟨div_nonneg hnum_nonneg hmix_pos.le,
    (div_le_iff₀ hmix_pos).2 hnum_le⟩

section RealBridge

variable {mOmega : MeasurableSpace Omega}

/-- The master's betting wealth for the residual `X - m` is exactly the prior
mixture process.  Any e-process argument supplied for the prior mixture
therefore transfers to the single realized master bet; this module does not
prove the mixture supermartingale property itself.
@isnad1 id=eq.3h6v.s7.4f8b0ec76bd6 from=translated src=- shape=2b1223ce vocab=5cfa9ab4
-/
theorem continuumMasterWealth_eq_bettingWealthProcess
    (strategyPrior : Measure Kappa) [IsProbabilityMeasure strategyPrior]
    (X : Nat -> Omega -> Real) (m : Real)
    (strategy : Kappa -> Nat -> Omega -> Real)
    (hwealth_int : forall n omega, Integrable
      (fun j => algebraicBettingWealth (fun k omega => X k omega - m)
        (strategy j) n omega) strategyPrior)
    (hnumerator_int : forall n omega, Integrable
      (fun j => algebraicBettingWealth (fun k omega => X k omega - m)
        (strategy j) n omega * strategy j n omega) strategyPrior)
    (hmix_ne : forall n omega,
      continuumExpertMixtureWealth strategyPrior
        (fun k omega => X k omega - m) strategy n omega ≠ 0) :
    bettingWealthProcess X
        (continuumWealthWeightedBet strategyPrior
          (fun k omega => X k omega - m) strategy) m =
      continuumExpertMixtureWealth strategyPrior
        (fun k omega => X k omega - m) strategy := by
  funext n omega
  rw [← algebraicBettingWealth_eq_bettingWealthProcess]
  exact continuumAggregateWealth_eq_continuumExpertMixtureWealth
    strategyPrior (fun k omega => X k omega - m) strategy
    hwealth_int hnumerator_int hmix_ne n omega

/-- Joint strong measurability of the component wealths in the `F n`-product
sigma-algebra, from a one-step-late increment process and a jointly
predictable strategy family.  This is the input to predictability of the
master bet.
@isnad1 id=strongly.2h8v.s7.8f41b6b3bb18 from=translated src=- shape=45873dc6 vocab=b37af6cd
-/
theorem stronglyMeasurable_filtration_prod_algebraicBettingWealth
    {F : Filtration Nat mOmega}
    (X : Nat -> Omega -> Real) (m : Real)
    (strategy : Kappa -> Nat -> Omega -> Real) (n : Nat)
    (hX_adapted : IncrementAdapted F X)
    (hstrategy : forall k, k < n ->
      StronglyMeasurable[(F n).prod (inferInstance : MeasurableSpace Kappa)]
        (Function.uncurry fun omega j => strategy j k omega)) :
    StronglyMeasurable[(F n).prod (inferInstance : MeasurableSpace Kappa)]
      (Function.uncurry fun omega j =>
        algebraicBettingWealth (fun k omega => X k omega - m)
          (strategy j) n omega) := by
  have hgoal : StronglyMeasurable[(F n).prod
      (inferInstance : MeasurableSpace Kappa)]
      (fun p : Omega × Kappa => ∏ k ∈ Finset.range n,
        (1 + strategy p.2 k p.1 * (X k p.1 - m))) := by
    apply Finset.stronglyMeasurable_fun_prod
    intro k hk
    rw [Finset.mem_range] at hk
    have hX : StronglyMeasurable[F n] (X k) :=
      (hX_adapted k).mono (F.mono (Nat.succ_le_of_lt hk))
    have hXprod : StronglyMeasurable[(F n).prod
        (inferInstance : MeasurableSpace Kappa)]
        (fun p : Omega × Kappa => X k p.1) :=
      hX.comp_measurable measurable_fst
    have hs : StronglyMeasurable[(F n).prod
        (inferInstance : MeasurableSpace Kappa)]
        (fun p : Omega × Kappa => strategy p.2 k p.1) := hstrategy k hk
    exact stronglyMeasurable_const.add
      (hs.mul (hXprod.sub stronglyMeasurable_const))
  exact hgoal

/-- The master bet is predictable: its time-`n` value is `F n`-measurable, so
it is fixed before the time-`n` residual `X n - m` (which is only
`F (n + 1)`-measurable) is revealed.  The prior integral is pushed through the
sigma-algebra by Fubini measurability.
@isnad1 id=strongly.2h7v.s7.d431b8ca6c86 from=translated src=- shape=51093cf6 vocab=03276d7b
-/
theorem continuumWealthWeightedBet_stronglyAdapted
    {F : Filtration Nat mOmega}
    (strategyPrior : Measure Kappa) [SFinite strategyPrior]
    (residual : Nat -> Omega -> Real)
    (strategy : Kappa -> Nat -> Omega -> Real)
    (hwealth_joint : forall n,
      StronglyMeasurable[(F n).prod (inferInstance : MeasurableSpace Kappa)]
        (Function.uncurry fun omega j =>
          algebraicBettingWealth residual (strategy j) n omega))
    (hnumerator_joint : forall n,
      StronglyMeasurable[(F n).prod (inferInstance : MeasurableSpace Kappa)]
        (Function.uncurry fun omega j =>
          algebraicBettingWealth residual (strategy j) n omega *
            strategy j n omega)) :
    StronglyAdapted F
      (continuumWealthWeightedBet strategyPrior residual strategy) := by
  intro n
  have hden : StronglyMeasurable[F n]
      (fun omega => continuumExpertMixtureWealth
        strategyPrior residual strategy n omega) := by
    letI : MeasurableSpace Omega := F n
    exact MeasureTheory.StronglyMeasurable.integral_prod_right
      (ν := strategyPrior) (hwealth_joint n)
  have hnum : StronglyMeasurable[F n]
      (fun omega => continuumWealthWeightedBetNumerator
        strategyPrior residual strategy n omega) := by
    letI : MeasurableSpace Omega := F n
    exact MeasureTheory.StronglyMeasurable.integral_prod_right
      (ν := strategyPrior) (hnumerator_joint n)
  exact hnum.div hden

/-- Predictability of the master bet with both Fubini-measurability
obligations discharged from the increment model.  The time-`k` bet of every
member of the class is jointly measurable in path and index at level `F k`,
and increments arrive one step late, so the master bet at time `n` is
`F n`-measurable and is fixed before `X n - m` is revealed.
@isnad1 id=strongly.2h8v.s7.574f2d93e7f0 from=translated src=- shape=82b4724c vocab=ef5292c8
-/
theorem continuumWealthWeightedBet_stronglyAdapted_of_incrementAdapted
    {F : Filtration Nat mOmega}
    (strategyPrior : Measure Kappa) [SFinite strategyPrior]
    (X : Nat -> Omega -> Real) (m : Real)
    (strategy : Kappa -> Nat -> Omega -> Real)
    (hX_adapted : IncrementAdapted F X)
    (hstrategy : forall n k, k <= n ->
      StronglyMeasurable[(F n).prod (inferInstance : MeasurableSpace Kappa)]
        (Function.uncurry fun omega j => strategy j k omega)) :
    StronglyAdapted F
      (continuumWealthWeightedBet strategyPrior
        (fun k omega => X k omega - m) strategy) := by
  have hwealth : forall n,
      StronglyMeasurable[(F n).prod (inferInstance : MeasurableSpace Kappa)]
        (Function.uncurry fun omega j =>
          algebraicBettingWealth (fun k omega => X k omega - m)
            (strategy j) n omega) := fun n =>
    stronglyMeasurable_filtration_prod_algebraicBettingWealth
      X m strategy n hX_adapted (fun k hk => hstrategy n k hk.le)
  refine continuumWealthWeightedBet_stronglyAdapted strategyPrior _ strategy
    hwealth ?_
  intro n
  show StronglyMeasurable[(F n).prod (inferInstance : MeasurableSpace Kappa)]
    (fun p : Omega × Kappa =>
      algebraicBettingWealth (fun k omega => X k omega - m)
        (strategy p.2) n p.1 * strategy p.2 n p.1)
  exact (hwealth n).mul (hstrategy n n le_rfl)

end RealBridge

end

end FormalSLT.AnytimeValid
