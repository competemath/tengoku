/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Randomsettheory.RandomSetTheory.Geometry
import Tengoku.Randomsettheory.RandomSetTheory.FiniteNetConcentration

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-net concentration for convex compact sets

This module turns finitely many directional tail bounds for support functions
into a Hausdorff-distance tail bound. Geometry transfers estimates from a
finite net to the whole unit ball, while a union bound controls the resulting
bad event.
-/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace RandomSetTheory

/-- If the Hausdorff distance exceeds the net precision, some direction in the
net has a large support-function error.-/
theorem supportFunction_bad_event_subset_finset
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Ω → Set E) (L : Set E)
    (hK : ∀ ω, IsCompact (K ω)) (hL : IsCompact L)
    (hKne : ∀ ω, (K ω).Nonempty) (hLne : L.Nonempty)
    (hKconv : ∀ ω, Convex ℝ (K ω)) (hLconv : Convex ℝ L)
    {RK RL eps s : ℝ}
    (hRK : ∀ ω, ∀ x ∈ K ω, ‖x‖ ≤ RK)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 ≤ eps) (hs : 0 ≤ s)
    (N : Finset E)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps) :
    {ω | s + (RK + RL) * eps < hausdorffDist (K ω) L} ⊆
      {ω | ∃ v ∈ N,
        s ≤ |supportFunction (K ω) v - supportFunction L v|} := by
  intro ω hbad
  by_contra hlarge
  have hsmall : ∀ v ∈ N,
      |supportFunction (K ω) v - supportFunction L v| < s := by
    intro v hv
    exact lt_of_not_ge fun hvlarge => hlarge ⟨v, hv, hvlarge⟩
  have hdist := hausdorffDist_le_of_finset_net_supportFunction
    (hK ω) hL (hKne ω) hLne (hKconv ω) hLconv
    (hRK ω) hRL heps hs N hnet
    (fun v hv => (hsmall v hv).le)
  exact (not_lt_of_ge hdist) hbad

/-- Directional tail bounds on a finite net imply a Hausdorff-distance tail
bound for convex compact sets.-/
theorem hausdorffDist_risk_bound_of_finset_supportFunction
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Ω → Set E) (L : Set E)
    (hK : ∀ ω, IsCompact (K ω)) (hL : IsCompact L)
    (hKne : ∀ ω, (K ω).Nonempty) (hLne : L.Nonempty)
    (hKconv : ∀ ω, Convex ℝ (K ω)) (hLconv : Convex ℝ L)
    {RK RL eps s q : ℝ}
    (hRK : ∀ ω, ∀ x ∈ K ω, ‖x‖ ≤ RK)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 ≤ eps) (hs : 0 ≤ s)
    (N : Finset E)
    (hnet : ∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ N, dist u v ≤ eps)
    (htail : ∀ v ∈ N, μ.real {ω |
      s ≤ |supportFunction (K ω) v - supportFunction L v|} ≤ q) :
    μ.real {ω | s + (RK + RL) * eps < hausdorffDist (K ω) L} ≤
      N.card * q := by
  calc
    μ.real {ω | s + (RK + RL) * eps < hausdorffDist (K ω) L} ≤
        μ.real {ω | ∃ v ∈ N,
          s ≤ |supportFunction (K ω) v - supportFunction L v|} :=
      measureReal_mono
        (supportFunction_bad_event_subset_finset K L hK hL hKne hLne
          hKconv hLconv hRK hRL heps hs N hnet)
        (by finiteness)
    _ ≤ N.card * q :=
      ProbabilityTheory.finite_family_deviation_bound N
        (fun v ω => supportFunction (K ω) v - supportFunction L v) htail

/-- Finite-dimensional version using a volumetric unit-ball net.-/
theorem exists_hausdorffDist_risk_bound_supportFunction_net
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : Ω → Set E) (L : Set E)
    (hK : ∀ ω, IsCompact (K ω)) (hL : IsCompact L)
    (hKne : ∀ ω, (K ω).Nonempty) (hLne : L.Nonempty)
    (hKconv : ∀ ω, Convex ℝ (K ω)) (hLconv : Convex ℝ L)
    {RK RL eps s q : ℝ}
    (hRK : ∀ ω, ∀ x ∈ K ω, ‖x‖ ≤ RK)
    (hRL : ∀ x ∈ L, ‖x‖ ≤ RL)
    (heps : 0 < eps) (heps_one : eps ≤ 1)
    (hs : 0 ≤ s) (hq : 0 ≤ q)
    (htail : ∀ v : E, ‖v‖ ≤ 1 → μ.real {ω |
      s ≤ |supportFunction (K ω) v - supportFunction L v|} ≤ q) :
    ∃ N : Finset E,
      (∀ v ∈ N, ‖v‖ ≤ 1) ∧
      (N.card : ℝ) ≤ (3 / eps) ^ Module.finrank ℝ E ∧
      μ.real {ω | s + (RK + RL) * eps < hausdorffDist (K ω) L} ≤
        (3 / eps) ^ Module.finrank ℝ E * q := by
  obtain ⟨N, hNmem, hnet, hcard⟩ :=
    ProbabilityTheory.exists_unitBall_finset_net_card_le_three_div
      (E := E) heps heps_one
  refine ⟨N, hNmem, hcard, ?_⟩
  have hprob := hausdorffDist_risk_bound_of_finset_supportFunction
    (μ := μ) K L hK hL hKne hLne hKconv hLconv hRK hRL
    heps.le hs N hnet (fun v hv => htail v (hNmem v hv))
  exact hprob.trans (mul_le_mul_of_nonneg_right hcard hq)

end RandomSetTheory
