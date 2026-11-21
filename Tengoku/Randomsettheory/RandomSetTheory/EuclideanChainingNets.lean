/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.EuclideanNetCardinality
import Tengoku.Randomsettheory.RandomSetTheory.EuclideanUnitBall
import Tengoku.Randomsettheory.RandomSetTheory.MixedTailChaining

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite Euclidean nets for chaining

This file packages the volumetric unit-ball net from
`EuclideanNetCardinality` in the form required by `FiniteChaining` and
`MixedTailChaining`.  It supplies simultaneously chosen finite nets at every
positive prescribed radius, finite-horizon projections, and the cardinality
bound

`card (N k) ≤ (1 + 2 / eps k) ^ finrank ℝ E`.

A second construction chooses a parent in level `k` for every point of the
unit ball, starts from a finest-level projection, and descends through those
parents.  The resulting projections are coherent.  Their local edges have
length at most `eps k`, and the parent-edge graph at level `k` has cardinality
at most `card (N (k+1))`.  Only the finest coherent projection is asserted to
approximate the original point directly; coarser coherent projections are
obtained by parent descent rather than independent nearest-point choices.

Everything is finite-horizon.  There is no infinite nested-net construction
or limiting chaining argument in this module.
-/

open Real Set Metric Finset Module
open scoped BigOperators NNReal ENNReal

noncomputable section

namespace RandomSetTheory

/-- One volumetrically controlled net, lifted to the subtype of the closed
unit ball.-/
theorem exists_euclideanUnitBall_finset_net_card_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {eps : ℝ} (heps : 0 < eps) :
    ∃ N : Finset (EuclideanUnitBall E),
      (∀ u : EuclideanUnitBall E, ∃ v ∈ N, dist u v ≤ eps) ∧
      (N.card : ℝ) ≤ (1 + 2 / eps) ^ finrank ℝ E := by
  classical
  obtain ⟨N, hNmem, hNcover, hNcard⟩ :=
    exists_unitBall_finset_net_card_le (E := E) heps
  let liftFun : {v // v ∈ N} → EuclideanUnitBall E := fun v ↦
    ⟨v.1, hNmem v.1 v.2⟩
  have hliftFun : Function.Injective liftFun := by
    intro v w hvw
    exact Subtype.ext
      (congrArg (fun z : EuclideanUnitBall E ↦ z.1) hvw)
  let lift : {v // v ∈ N} ↪ EuclideanUnitBall E :=
    ⟨liftFun, hliftFun⟩
  let M : Finset (EuclideanUnitBall E) := N.attach.map lift
  refine ⟨M, ?_, ?_⟩
  · intro u
    obtain ⟨v, hvN, huv⟩ := hNcover u.1 u.2
    let vN : {v // v ∈ N} := ⟨v, hvN⟩
    refine ⟨lift vN, ?_, ?_⟩
    · exact Finset.mem_map.2 ⟨vN, by simp [vN], rfl⟩
    · exact huv
  · calc
      (M.card : ℝ) = (N.attach.card : ℝ) := by simp [M]
      _ = (N.card : ℝ) := by simp
      _ ≤ (1 + 2 / eps) ^ finrank ℝ E := hNcard

/-- Simultaneous volumetric nets at an arbitrary positive sequence of
scales.  Choice is made independently at each level; no nesting is asserted
by this theorem.-/
theorem exists_euclideanUnitBall_multiscaleNets
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (eps : ℕ → ℝ) (heps : ∀ k, 0 < eps k) :
    ∃ N : ℕ → Finset (EuclideanUnitBall E),
      (∀ k, ∀ u : EuclideanUnitBall E,
        ∃ v ∈ N k, dist u v ≤ eps k) ∧
      ∀ k, ((N k).card : ℝ) ≤
        (1 + 2 / eps k) ^ finrank ℝ E := by
  choose N hnet hcard using fun k ↦
    exists_euclideanUnitBall_finset_net_card_le (E := E) (heps k)
  exact ⟨N, hnet, hcard⟩

/-- Simultaneous volumetric nets together with the finite-horizon projections
used by `FiniteChaining`.  Every projection through level `m` lies in its net
and is within that level's prescribed radius.-/
theorem exists_euclideanUnitBall_multiscaleNets_projections
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (eps : ℕ → ℝ) (heps : ∀ k, 0 < eps k) (m : ℕ) :
    ∃ N : ℕ → Finset (EuclideanUnitBall E),
      ∃ proj : ℕ → EuclideanUnitBall E → EuclideanUnitBall E,
        (∀ k, ∀ u : EuclideanUnitBall E,
          ∃ v ∈ N k, dist u v ≤ eps k) ∧
        (∀ k, ((N k).card : ℝ) ≤
          (1 + 2 / eps k) ^ finrank ℝ E) ∧
        (∀ k, k ≤ m → ∀ u, proj k u ∈ N k) ∧
        ∀ k, k ≤ m → ∀ u, dist u (proj k u) ≤ eps k := by
  obtain ⟨N, hnet, hcard⟩ :=
    exists_euclideanUnitBall_multiscaleNets (E := E) eps heps
  obtain ⟨proj, hproj, hnear⟩ :=
    ProbabilityTheory.exists_finiteNetProjections N eps m
      (fun k _ ↦ hnet k)
  exact ⟨N, proj, hnet, hcard, hproj, hnear⟩

/-- Simultaneous choice of a nearest-enough parent in every level.-/
theorem exists_euclideanUnitBall_netParents
    {E : Type*} [NormedAddCommGroup E]
    (N : ℕ → Finset (EuclideanUnitBall E)) (eps : ℕ → ℝ)
    (hnet : ∀ k, ∀ u : EuclideanUnitBall E,
      ∃ v ∈ N k, dist u v ≤ eps k) :
    ∃ parent : ℕ → EuclideanUnitBall E → EuclideanUnitBall E,
      ∀ k u, parent k u ∈ N k ∧ dist u (parent k u) ≤ eps k := by
  choose parent hparent using fun k u ↦ hnet k u
  exact ⟨parent, hparent⟩

/-- Descend `steps` times from a finest point, applying the parents whose
indices decrease from `m-1`.-/
def finiteParentDescent {T : Type*} (parent : ℕ → T → T)
    (m : ℕ) (top : T) : ℕ → T
  | 0 => top
  | steps + 1 => parent (m - (steps + 1))
      (finiteParentDescent parent m top steps)

@[simp] theorem finiteParentDescent_zero
    {T : Type*} (parent : ℕ → T → T) (m : ℕ) (top : T) :
    finiteParentDescent parent m top 0 = top := rfl

@[simp] theorem finiteParentDescent_succ
    {T : Type*} (parent : ℕ → T → T) (m : ℕ) (top : T) (steps : ℕ) :
    finiteParentDescent parent m top (steps + 1) =
      parent (m - (steps + 1))
        (finiteParentDescent parent m top steps) := rfl

/-- The algebraic identity behind coherence of reverse parent descent.-/
theorem parent_finiteParentDescent_sub_succ
    {T : Type*} (parent : ℕ → T → T) (m : ℕ) (top : T)
    {k : ℕ} (hk : k < m) :
    parent k (finiteParentDescent parent m top (m - (k + 1))) =
      finiteParentDescent parent m top (m - k) := by
  have hsteps : m - k = (m - (k + 1)) + 1 := by omega
  rw [hsteps, finiteParentDescent_succ]
  congr 1
  omega

/-- Projection obtained by descending from one chosen finest-level point.
Outside the finite horizon it is set equal to that finest point.-/
def coherentParentProjection {T : Type*} (parent : ℕ → T → T)
    (top : T → T) (m k : ℕ) (t : T) : T :=
  if k ≤ m then finiteParentDescent parent m (top t) (m - k) else top t

@[simp] theorem coherentParentProjection_top
    {T : Type*} (parent : ℕ → T → T) (top : T → T)
    (m : ℕ) (t : T) :
    coherentParentProjection parent top m m t = top t := by
  simp [coherentParentProjection]

/-- Successive coherent projections are related by the prescribed parent.-/
theorem coherentParentProjection_parent
    {T : Type*} (parent : ℕ → T → T) (top : T → T)
    (m : ℕ) {k : ℕ} (hk : k < m) (t : T) :
    parent k (coherentParentProjection parent top m (k + 1) t) =
      coherentParentProjection parent top m k t := by
  rw [coherentParentProjection, coherentParentProjection,
    ite_eq_left (Nat.succ_le_iff.2 hk), ite_eq_left hk.le]
  exact parent_finiteParentDescent_sub_succ parent m (top t) hk

/-- Full finite Euclidean chaining package with coherent parent projections.
The finest projection is within `eps m`; every local parent edge at level `k`
has length at most `eps k`.-/
theorem exists_euclideanUnitBall_coherentParentChaining
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (eps : ℕ → ℝ) (heps : ∀ k, 0 < eps k) (m : ℕ) :
    ∃ N : ℕ → Finset (EuclideanUnitBall E),
      ∃ parent proj : ℕ → EuclideanUnitBall E → EuclideanUnitBall E,
        (∀ k, ∀ u : EuclideanUnitBall E,
          ∃ v ∈ N k, dist u v ≤ eps k) ∧
        (∀ k, ((N k).card : ℝ) ≤
          (1 + 2 / eps k) ^ finrank ℝ E) ∧
        (∀ k u, parent k u ∈ N k ∧
          dist u (parent k u) ≤ eps k) ∧
        (∀ k, k ≤ m → ∀ u, proj k u ∈ N k) ∧
        (∀ u, dist u (proj m u) ≤ eps m) ∧
        (∀ k ∈ Finset.range m, ∀ u,
          parent k (proj (k + 1) u) = proj k u) ∧
        (∀ k ∈ Finset.range m, ∀ u,
          (proj (k + 1) u, proj k u) ∈
            ProbabilityTheory.finiteChainingParentEdges N parent k) ∧
        ∀ k, (ProbabilityTheory.finiteChainingParentEdges N parent k).card ≤
          (N (k + 1)).card := by
  classical
  obtain ⟨N, hnet, hcard⟩ :=
    exists_euclideanUnitBall_multiscaleNets (E := E) eps heps
  obtain ⟨parent, hparent⟩ :=
    exists_euclideanUnitBall_netParents N eps hnet
  choose top htop using fun u : EuclideanUnitBall E ↦ hnet m u
  let proj : ℕ → EuclideanUnitBall E → EuclideanUnitBall E :=
    fun k u ↦ coherentParentProjection parent top m k u
  have hcoherent : ∀ k ∈ Finset.range m, ∀ u,
      parent k (proj (k + 1) u) = proj k u := by
    intro k hk u
    exact coherentParentProjection_parent parent top m
      (Finset.mem_range.1 hk) u
  have hproj : ∀ k, k ≤ m → ∀ u, proj k u ∈ N k := by
    intro k hk u
    by_cases hkm : k = m
    · subst k
      simpa [proj] using (htop u).1
    · have hlt : k < m := lt_of_le_of_ne hk hkm
      rw [← hcoherent k (Finset.mem_range.2 hlt) u]
      exact (hparent k (proj (k + 1) u)).1
  have hfinal : ∀ u, dist u (proj m u) ≤ eps m := by
    intro u
    simpa [proj] using (htop u).2
  have hedge : ∀ k ∈ Finset.range m, ∀ u,
      (proj (k + 1) u, proj k u) ∈
        ProbabilityTheory.finiteChainingParentEdges N parent k :=
    ProbabilityTheory.finiteChainingParentEdges_contains_projection
      N parent proj m
      (fun k hk u ↦ hproj (k + 1) (Nat.succ_le_iff.2 (Finset.mem_range.1 hk)) u)
      hcoherent
  refine ⟨N, parent, proj, hnet, hcard, hparent, hproj, hfinal,
    hcoherent, hedge, ?_⟩
  intro k
  exact ProbabilityTheory.card_finiteChainingParentEdges_le N parent k

end RandomSetTheory
