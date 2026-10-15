/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/
module

public import Tengoku.LeanPool.LeanPool.PebblingLean.Hypercube
public import Tengoku

/-!
# Upper-bound scaffolding

This file records the definitions and elementary lemmas used by the
probabilistic high-demand part of the upper bound.  The probabilistic estimates
themselves are not asserted here; they will be formalized as separate lemmas.
-/

@[expose] public section

namespace PebblingLean

namespace Hypercube

open Pebbling

/-- Centers whose distance from `target` lies between the inner and outer
radii. -/
def annulus (n rIn rOut : ℕ) (target : HypercubeVertex n) : Finset (HypercubeVertex n) :=
  Finset.univ.filter fun center => rIn ≤ dist center target ∧ dist center target ≤ rOut

/--
@isnad1 id=iff.0h5v.s5.5d8686439e26 from=translated src=- shape=166f7b4d vocab=5ff3a4d4
-/
@[simp]
theorem mem_annulus {n rIn rOut : ℕ} {target center : HypercubeVertex n} :
    center ∈ annulus n rIn rOut target ↔
      rIn ≤ dist center target ∧ dist center target ≤ rOut := by
  simp [annulus]

/-- Contribution of one stack of size `2^rOut` at `center` toward `target`,
counting only centers in the annulus. -/
def annulusContribution {n : ℕ} (rIn rOut : ℕ) (target center : HypercubeVertex n) : ℕ :=
  if rIn ≤ dist center target ∧ dist center target ≤ rOut then
    2 ^ (rOut - dist center target)
  else
    0

/--
@isnad1 id=eq.1h5v.s6.2ad11a9dede8 from=translated src=- shape=55c971b7 vocab=0f97faf8
-/
theorem annulusContribution_eq_of_mem {n rIn rOut : ℕ}
    {target center : HypercubeVertex n}
    (hmem : center ∈ annulus n rIn rOut target) :
    annulusContribution rIn rOut target center = 2 ^ (rOut - dist center target) := by
  simp [annulusContribution, mem_annulus.mp hmem]

/--
@isnad1 id=eq.1h5v.s5.10e326980c7b from=translated src=- shape=e09bbaa7 vocab=ebfc34b0
-/
theorem annulusContribution_eq_zero_of_notMem {n rIn rOut : ℕ}
    {target center : HypercubeVertex n}
    (hmem : center ∉ annulus n rIn rOut target) :
    annulusContribution rIn rOut target center = 0 := by
  have hnot : ¬ (rIn ≤ dist center target ∧ dist center target ≤ rOut) := by
    simp_all
  simp [annulusContribution, hnot]

/-- One annulus contribution is bounded by the stack size `2^rOut`.
@isnad1 id=le.0h5v.s5.6d36f2938dcc from=translated src=- shape=d628ada8 vocab=407dbec7
-/
theorem annulusContribution_le_stackSize {n rIn rOut : ℕ}
    (target center : HypercubeVertex n) :
    annulusContribution rIn rOut target center ≤ 2 ^ rOut := by
  unfold annulusContribution
  by_cases h : rIn ≤ dist center target ∧ dist center target ≤ rOut
  · simpa [h] using
      Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.sub_le rOut (dist center target))
  · simp [h]

/-- If the center is counted, the annulus contribution is bounded by the width
of the annulus rather than by the full stack size.
@isnad1 id=le.0h5v.s5.3c18d461a58e from=translated src=- shape=f6d348a1 vocab=54ddea74
-/
theorem annulusContribution_le_width {n rIn rOut : ℕ}
    (target center : HypercubeVertex n) :
    annulusContribution rIn rOut target center ≤ 2 ^ (rOut - rIn) := by
  unfold annulusContribution
  by_cases h : rIn ≤ dist center target ∧ dist center target ≤ rOut
  · have hsub : rOut - dist center target ≤ rOut - rIn :=
      tsub_le_tsub_left h.1 rOut
    simpa [h] using Nat.pow_le_pow_right (by decide : 0 < 2) hsub
  · simp [h]

/-- The square bound used in the Bernstein step: `Z^2 ≤ B_0 Z`, where
`B_0 = 2^(rOut-rIn)` is the annulus-width contribution bound.
@isnad1 id=le.0h5v.s6.824a8bee4b3c from=translated src=- shape=e3913e5c vocab=61b5a066
-/
theorem annulusContribution_sq_le_width_mul {n rIn rOut : ℕ}
    (target center : HypercubeVertex n) :
    annulusContribution rIn rOut target center ^ 2 ≤
      2 ^ (rOut - rIn) * annulusContribution rIn rOut target center := by
  have hle := annulusContribution_le_width (rIn := rIn) (rOut := rOut) target center
  calc
    annulusContribution rIn rOut target center ^ 2
        = annulusContribution rIn rOut target center *
          annulusContribution rIn rOut target center := by
          rw [pow_two]
    _ ≤ annulusContribution rIn rOut target center * 2 ^ (rOut - rIn) := by
          exact Nat.mul_le_mul_left _ hle
    _ = 2 ^ (rOut - rIn) * annulusContribution rIn rOut target center := by
          rw [Nat.mul_comm]

/-- The total annulus contribution of a finite list of centers to a fixed
target. This is the Lean version of `X_t` in the proof. -/
def annulusTotalContribution {n : ℕ} (rIn rOut : ℕ) (target : HypercubeVertex n)
    (centers : List (HypercubeVertex n)) : ℕ :=
  (centers.map (annulusContribution rIn rOut target)).sum

/-- The high-demand conclusion used as a target for the probabilistic lemma:
a `T`-solvable distribution whose size is bounded and whose occupied piles are
large. -/
def HasHighDemandDistribution (n T : ℕ) (costBound minPile : ℕ) : Prop :=
  ∃ D : Pebbling (HypercubeVertex n),
    size D ≤ costBound ∧
      SolvableAtLeast (graph n) D T ∧
        MinOccupiedPileSize D minPile

/--
@isnad1 id=hassolva.1h4v.s5.c9070c40c480 from=translated src=- shape=1768161e vocab=230fcd0b
-/
theorem HasHighDemandDistribution.to_hasSolvableAtMostSize
    {n T costBound minPile : ℕ}
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasSolvableAtMostSize (graph n) T costBound := by
  rcases h with ⟨D, hsize, hsolv, _hmin⟩
  exact ⟨D, hsize, hsolv⟩

/--
@isnad1 id=hassolva.2h4v.s6.285c3f1a9b12 from=translated src=- shape=f5919a31 vocab=5009da82
-/
theorem HasHighDemandDistribution.to_ordinary_hasSolvableAtMostSize
    {n T costBound minPile : ℕ} (hT : 1 ≤ T)
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasSolvableAtMostSize (graph n) 1 costBound :=
  Pebbling.hasSolvableAtMostSize_mono_demand hT h.to_hasSolvableAtMostSize

/--
@isnad1 id=hashighd.2h5v.s4.3a42034867a9 from=translated src=- shape=3f98495e vocab=4cce877f
-/
theorem HasHighDemandDistribution.mono_cost {n T costBound costBound' minPile : ℕ}
    (hcost : costBound ≤ costBound')
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasHighDemandDistribution n T costBound' minPile := by
  rcases h with ⟨D, hsize, hsolv, hmin⟩
  exact ⟨D, hsize.trans hcost, hsolv, hmin⟩

/--
@isnad1 id=hashighd.2h5v.s4.24ab6ebe6e5f from=translated src=- shape=5104b76e vocab=4cce877f
-/
theorem HasHighDemandDistribution.mono_minPile {n T costBound minPile minPile' : ℕ}
    (hminPile : minPile' ≤ minPile)
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasHighDemandDistribution n T costBound minPile' := by
  rcases h with ⟨D, hsize, hsolv, hmin⟩
  exact ⟨D, hsize, hsolv, fun v hv => hminPile.trans (hmin v hv)⟩

/--
@isnad1 id=hashighd.3h6v.s5.bed7b26bd87a from=translated src=- shape=2b20410b vocab=4cce877f
-/
theorem HasHighDemandDistribution.mono
    {n T costBound costBound' minPile minPile' : ℕ}
    (hcost : costBound ≤ costBound') (hminPile : minPile' ≤ minPile)
    (h : HasHighDemandDistribution n T costBound minPile) :
    HasHighDemandDistribution n T costBound' minPile' :=
  (h.mono_cost hcost).mono_minPile hminPile

/-- The constant distribution with `S` pebbles on every vertex. -/
def constantDistribution (n S : ℕ) : Pebbling (HypercubeVertex n) :=
  fun _ => S

/--
@isnad1 id=eq.0h2v.s5.6407119b2c53 from=translated src=- shape=21dd6ffe vocab=3b12e7d9
-/
theorem size_constantDistribution (n S : ℕ) :
    size (constantDistribution n S) = 2 ^ n * S := by
  simp [constantDistribution, size, Finset.sum_const]

/--
@isnad1 id=solvable.0h2v.s5.bf66a060c2ff from=translated src=- shape=a13f997b vocab=1e33c654
-/
theorem solvableAtLeast_constantDistribution (n S : ℕ) :
    SolvableAtLeast (graph n) (constantDistribution n S) S := by
  intro target
  exact ⟨constantDistribution n S, Relation.ReflTransGen.refl, by simp [constantDistribution]⟩

/--
@isnad1 id=minoccup.0h2v.s3.a992ad0bdbd9 from=translated src=- shape=d5e1edf9 vocab=ed1972db
-/
theorem minOccupiedPileSize_constantDistribution (n S : ℕ) :
    MinOccupiedPileSize (constantDistribution n S) S := by
  intro v _hv
  simp [constantDistribution]

/--
@isnad1 id=hashighd.0h2v.s5.1efc161c62c6 from=translated src=- shape=934a69c5 vocab=d17bfbd3
-/
theorem hasHighDemandDistribution_constant (n S : ℕ) :
    HasHighDemandDistribution n S (2 ^ n * S) S := by
  exact ⟨constantDistribution n S, by rw [size_constantDistribution],
    solvableAtLeast_constantDistribution n S,
    minOccupiedPileSize_constantDistribution n S⟩

end Hypercube

end PebblingLean
