/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.EffrosOperations
import Tengoku.Randomsettheory.RandomSetTheory.SupportFunction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Effros measurability of finite Minkowski averages

Finite Minkowski sums of compact-valued Effros correspondences are Effros
measurable.  Deterministic scaling then gives the empirical Minkowski average
used throughout random-set laws of large numbers and concentration bounds.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set MeasureTheory TopologicalSpace
open scoped Pointwise BigOperators

noncomputable section

namespace Tengoku.Randomsettheory.RandomSet

open RandomSetTheory

/-- A finite pointwise Minkowski sum of compact, nonempty Effros
correspondences is Effros measurable.
@isnad1 id=iseffros.3h5v.s7.3dcfefb896bd from=translated src=- shape=106395a7 vocab=97669d62
-/
theorem IsEffrosMeasurable.finset_sum
    {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    (s : Finset ι) (S : ι → Ω → Set E)
    (hS : ∀ i ∈ s, IsEffrosMeasurable (S i))
    (hcompact : ∀ i ∈ s, ∀ ω, IsCompact (S i ω))
    (hne : ∀ i ∈ s, ∀ ω, (S i ω).Nonempty) :
    IsEffrosMeasurable (fun ω => ∑ i ∈ s, S i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (isEffrosMeasurable_const (Ω := Ω) (0 : Set E))
  | @insert a s ha ih =>
      simp_rw [Finset.sum_insert ha]
      apply (hS a (Finset.mem_insert_self a s)).add
        (ih
          (fun i hi => hS i (Finset.mem_insert_of_mem hi))
          (fun i hi ω => hcompact i (Finset.mem_insert_of_mem hi) ω)
          (fun i hi ω => hne i (Finset.mem_insert_of_mem hi) ω))
      · exact fun ω => (hcompact a (Finset.mem_insert_self a s) ω).isClosed
      · intro ω
        exact (isCompact_finset_sum s (fun i => S i ω)
          (fun i hi => hcompact i (Finset.mem_insert_of_mem hi) ω)).isClosed
      · exact fun ω => hne a (Finset.mem_insert_self a s) ω
      · intro ω
        exact nonempty_finset_sum s (fun i => S i ω)
          (fun i hi => hne i (Finset.mem_insert_of_mem hi) ω)

/-- The empirical Minkowski average of finitely many compact, nonempty
Effros correspondences is Effros measurable.
@isnad1 id=iseffros.3h5v.s7.2dbacb55ed42 from=translated src=- shape=a45f7afb vocab=4426d463
-/
theorem IsEffrosMeasurable.minkowskiAverage
    {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [Nonempty E]
    (s : Finset ι) (S : ι → Ω → Set E)
    (hS : ∀ i ∈ s, IsEffrosMeasurable (S i))
    (hcompact : ∀ i ∈ s, ∀ ω, IsCompact (S i ω))
    (hne : ∀ i ∈ s, ∀ ω, (S i ω).Nonempty) :
    IsEffrosMeasurable
      (fun ω => minkowskiAverage s (fun i => S i ω)) := by
  have hsum := IsEffrosMeasurable.finset_sum s S hS hcompact hne
  simpa only [RandomSetTheory.minkowskiAverage] using
    hsum.const_smul (s.card : ℝ)⁻¹

end Tengoku.Randomsettheory.RandomSet
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
