/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Regularity.Baire.Suslin
import Tengoku.Seed.MeasureTheory.Constructions.Polish.Basic
import Tengoku.Seed.Topology.MetricSpace.PiNat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analytic sets have the Baire property

An analytic set is empty or the range of a continuous map from Baire space. For a continuous
`f : (ℕ → ℕ) → X`, this file represents `Set.range f` as the Suslin operation of the closed
scheme

`s ↦ closure (f '' {p | p extends s})`.

The reverse inclusion in that representation is the substantive step: if a point belongs to the
closures along one branch, continuity and Hausdorff separation force it to equal the image of that
branch. The v1.26 Suslin-closure theorem then gives the Baire property. The proof needs only a
Hausdorff, second-countable target, so the public theorem is slightly more general than the usual
Polish-space statement. No measurable-space instance or selected compatible metric appears in its
signature.
-/

open Set

universe u

namespace DescriptiveSetTheory

open Tree

variable {X : Type u}

/-- The Baire-space cylinder consisting of sequences with finite prefix `s`.-/
def bairePrefixCylinder (s : List ℕ) : Set (ℕ → ℕ) :=
  {p | initialSegment p s.length = s}

/-- The prefix cylinder selected by a sequence agrees with mathlib's coordinate cylinder.-/
theorem bairePrefixCylinder_initialSegment (p : ℕ → ℕ) (n : ℕ) :
    bairePrefixCylinder (initialSegment p n) = PiNat.cylinder p n := by
  ext q
  change initialSegment q (initialSegment p n).length = initialSegment p n ↔
    ∀ i, i < n → q i = p i
  rw [length_initialSegment]
  constructor
  · intro h i hi
    have hfun : (fun j : Fin n => q j) = fun j : Fin n => p j :=
      List.ofFn_injective (by simpa [initialSegment] using h)
    exact congrFun hfun ⟨i, hi⟩
  · intro h
    change List.ofFn (fun j : Fin n => q j) = List.ofFn fun j : Fin n => p j
    exact congrArg List.ofFn (funext fun i => h i i.2)

/-- The closed Suslin scheme obtained from the finite-prefix images of a map on Baire space.-/
def closedRangeScheme [TopologicalSpace X] (f : (ℕ → ℕ) → X) (s : List ℕ) : Set X :=
  closure (f '' bairePrefixCylinder s)

/-- Every component of `closedRangeScheme` is closed.-/
theorem isClosed_closedRangeScheme [TopologicalSpace X] (f : (ℕ → ℕ) → X) (s : List ℕ) :
    IsClosed (closedRangeScheme f s) :=
  isClosed_closure

/-- In a Hausdorff target, the closed-range scheme recovers exactly the range of a continuous map.

The forward direction uses Hausdorff separation and a finite-prefix neighborhood supplied by the
standard cylinder basis of Baire space.-/
theorem suslinOperation_closedRangeScheme [TopologicalSpace X] [T2Space X]
    (f : (ℕ → ℕ) → X) (hf : Continuous f) :
    suslinOperation (closedRangeScheme f) = range f := by
  ext x
  constructor
  · rintro ⟨p, hp⟩
    have hxp : x = f p := by
      by_contra hne
      rcases t2_separation hne with ⟨U, V, hUopen, hVopen, hxU, hfpV, hUV⟩
      have hpreopen : IsOpen (f ⁻¹' V) := hVopen.preimage hf
      have hppre : p ∈ f ⁻¹' V := hfpV
      rcases (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => ℕ)).exists_subset_of_mem_open
          hppre hpreopen with ⟨C, ⟨q, n, rfl⟩, hpC, hCsub⟩
      have hcylinder : PiNat.cylinder p n ⊆ f ⁻¹' V := by
        rw [PiNat.mem_cylinder_iff_eq.1 hpC]
        exact hCsub
      have hxclosure : x ∈ closure (f '' PiNat.cylinder p n) := by
        simpa [closedRangeScheme, bairePrefixCylinder_initialSegment] using hp n
      rcases (mem_closure_iff.1 hxclosure U hUopen hxU) with ⟨z, hzU, y, hy, rfl⟩
      exact Set.disjoint_left.1 hUV hzU (hcylinder hy)
    exact ⟨p, hxp.symm⟩
  · rintro ⟨p, rfl⟩
    refine ⟨p, fun n => ?_⟩
    change f p ∈ closure (f '' bairePrefixCylinder (initialSegment p n))
    apply subset_closure
    refine ⟨p, ?_, rfl⟩
    rw [bairePrefixCylinder_initialSegment]
    exact PiNat.self_mem_cylinder p n

/-- Every analytic subset of a second-countable Hausdorff space has the property of Baire.

In particular this applies to every Polish space.-/
theorem _root_.MeasureTheory.AnalyticSet.baireMeasurableSet [TopologicalSpace X] [T2Space X]
    [SecondCountableTopology X] {s : Set X} (hs : MeasureTheory.AnalyticSet s) :
    BaireMeasurableSet s := by
  rw [MeasureTheory.AnalyticSet] at hs
  rcases hs with rfl | ⟨f, hf, rfl⟩
  · exact IsMeagre.empty.baireMeasurableSet
  · rw [← suslinOperation_closedRangeScheme f hf]
    exact BaireMeasurableSet.suslinOperation _ fun t =>
      (isClosed_closedRangeScheme f t).isOpen_compl.baireMeasurableSet.of_compl

/-- Baire-space specialization of `MeasureTheory.AnalyticSet.baireMeasurableSet`.-/
theorem analyticSet_baireMeasurableSet_baire {s : Set (ℕ → ℕ)}
    (hs : MeasureTheory.AnalyticSet s) : BaireMeasurableSet s :=
  hs.baireMeasurableSet

/-- Cantor-space specialization of `MeasureTheory.AnalyticSet.baireMeasurableSet`.-/
theorem analyticSet_baireMeasurableSet_cantor {s : Set (ℕ → Bool)}
    (hs : MeasureTheory.AnalyticSet s) : BaireMeasurableSet s :=
  hs.baireMeasurableSet

end DescriptiveSetTheory
