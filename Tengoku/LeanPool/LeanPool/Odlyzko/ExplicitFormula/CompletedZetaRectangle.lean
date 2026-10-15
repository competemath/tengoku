/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.FunctionalEquation
public import Tengoku.LeanPool.LeanPool.Odlyzko.FromPrimeNumberTheoremAnd.RectangleIntegral
import Tengoku.LeanPool.LeanPool.Odlyzko.CompletedZeta.FunctionalEquationLogDeriv
import Tengoku.LeanPool.LeanPool.Odlyzko.ExplicitFormula.WeightedRectangleArgumentPrinciple
public import Tengoku

/-!
# Completed Zeta Rectangle

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

section

open Complex Filter NumberField
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

open Classical in
/-- A completed dedekind zeta zero divisor used in the Odlyzko-bound argument. -/
noncomputable def completedDedekindZetaZeroDivisor :
    Function.locallyFinsuppWithin (Set.univ : Set ℂ) ℤ :=
  MeromorphicOn.divisor
    (poleClearedCompletedDedekindZetaContinuation K) Set.univ

omit [IsTotallyComplex K] in
open Classical in
/--
@isnad1 id=finite.1h2v.s6.ace9eaccff62 from=translated src=- shape=0b4b4295 vocab=ab8afd7a
-/
theorem completedDedekindZetaZeroDivisor_support_inter_compact_finite
    {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ (completedDedekindZetaZeroDivisor K).support).Finite := by
  classical
  let D := completedDedekindZetaZeroDivisor K
  have hloc :
      ∀ x ∈ S, ∃ V : Set ℂ, V ∈ 𝓝 x ∧
        Set.Finite (V ∩ D.support) := by
    intro x _
    rcases D.supportLocallyFiniteWithinDomain x (Set.mem_univ x) with
      ⟨V, hV, hfin⟩
    grind
  choose V hVnhds hVfin using hloc
  rcases hS.elim_nhds_subcover'
      (U := fun x hx ↦ V x hx)
      (hU := fun x hx ↦ hVnhds x hx) with
    ⟨t, ht⟩
  have hsub :
      S ∩ D.support ⊆
        ⋃ x ∈ t, (V (x : ℂ) x.2 ∩ D.support) := by
    intro y hy
    rcases hy with ⟨hyS, hyD⟩
    have hycov : y ∈ ⋃ x ∈ t, V (x : ℂ) x.2 := ht hyS
    simp_all
  have hfinite :
      Set.Finite (⋃ x ∈ t,
        (V (x : ℂ) x.2 ∩ D.support)) := by
    refine (t.finite_toSet).biUnion ?_
    simp_all
  exact hfinite.subset hsub

end NumberField.Odlyzko

end

section

open Complex Filter Metric NumberField Set
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

end NumberField.Odlyzko

end

section

open Complex NumberField Set
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- A completed dedekind zeta zeros in closed rectangle used in the Odlyzko-bound argument. -/
noncomputable def completedDedekindZetaZerosInClosedRectangle
    (a b u v : ℝ) : Finset ℂ := by
  classical
  exact (completedDedekindZetaZeroDivisor_support_inter_compact_finite K
      (S := Icc a b ×ℂ Icc u v)
      (isCompact_Icc.reProdIm isCompact_Icc)).toFinset

omit [IsTotallyComplex K] in
/--
@isnad1 id=iff.0h6v.s6.c3c06b2e4441 from=translated src=- shape=ffd33db8 vocab=70e3f26b
-/
theorem mem_completedDedekindZetaZerosInClosedRectangle_iff
    {a b u v : ℝ} {z : ℂ} :
    z ∈ completedDedekindZetaZerosInClosedRectangle K a b u v ↔
      z ∈ Icc a b ×ℂ Icc u v ∧
        z ∈ (completedDedekindZetaZeroDivisor K).support := by
  classical
  simp [completedDedekindZetaZerosInClosedRectangle]

end NumberField.Odlyzko

end
