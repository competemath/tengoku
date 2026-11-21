/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/

import Tengoku.Seed.Analysis.Normed.Group.Real
import Tengoku.Seed.MeasureTheory.Order.Lattice
import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Metric
import Tengoku.Seed.MeasureTheory.Constructions.BorelSpace.Order
import Tengoku.Seed.Order.PartialSups
import Tengoku.Seed.Topology.Bases
import Tengoku.Seed.Topology.Order.IsLUB
import Tengoku.Seed.Topology.Order.MonotoneConvergence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Suprema of continuous functions along a dense sequence

This file records the elementary passage from finite prefix suprema along
`denseSeq` to the supremum of a continuous real-valued function on the whole
space.  The domain need not be compact; boundedness is required only for the
convergence statement, not for the equality of the two suprema.
-/

open Filter Set TopologicalSpace
open scoped Topology

noncomputable section

namespace RandomSetTheory

variable {T Omega : Type*}

section DenseSupremum

variable [TopologicalSpace T] [SeparableSpace T] [Nonempty T]

/-- A continuous real-valued function has the same supremum on `denseSeq` as
on the whole space.-/
theorem iSup_denseSeq_eq_iSup (f : T → ℝ) (hf : Continuous f) :
    (⨆ k : ℕ, f (denseSeq T k)) = ⨆ t : T, f t := by
  let S : Set T := Set.range (denseSeq T)
  have hS : Dense S := by
    change Dense (Set.range (denseSeq T))
    exact denseRange_denseSeq T
  have hsub : (⨆ s : S, f s) = ⨆ t : T, f t := hS.ciSup' hf
  have hrange :
      Set.range (fun k : ℕ ↦ f (denseSeq T k)) =
        Set.range (fun s : S ↦ f s) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨denseSeq T k, ⟨k, rfl⟩⟩, rfl⟩
    · rintro ⟨⟨t, k, hk⟩, rfl⟩
      exact ⟨k, by simpa using congrArg f hk⟩
  rw [← sSup_range, ← sSup_range, hrange]
  exact hsub

/-- Absolute-value version of `iSup_denseSeq_eq_iSup`.-/
theorem iSup_abs_denseSeq_eq_iSup_abs (f : T → ℝ) (hf : Continuous f) :
    (⨆ k : ℕ, |f (denseSeq T k)|) = ⨆ t : T, |f t| := by
  exact iSup_denseSeq_eq_iSup (fun t ↦ |f t|) hf.abs

/-- The maximum of the first `n + 1` values of `f` along `denseSeq`.

Unlike a `Finset.sup`, this definition does not introduce an artificial
bottom element in `ℝ`; the prefix always contains its zeroth term.-/
def densePrefixSupremum (f : T → ℝ) (n : ℕ) : ℝ :=
  partialSups (fun k : ℕ ↦ f (denseSeq T k)) n

/-- A dense prefix supremum is the finite maximum over `Finset.range (n + 1)`.-/
theorem densePrefixSupremum_eq_sup'_range (f : T → ℝ) (n : ℕ) :
    densePrefixSupremum f n =
      (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ f (denseSeq T k)) :=
  partialSups_eq_sup'_range _ n

/-- Dense prefix suprema form a monotone sequence.-/
theorem densePrefixSupremum_monotone (f : T → ℝ) :
    Monotone (densePrefixSupremum f) := by
  exact partialSups_monotone _

/-- The supremum of all dense prefix suprema is the supremum on the whole
space.-/
theorem iSup_densePrefixSupremum_eq_iSup (f : T → ℝ)
    (hf : Continuous f) :
    (⨆ n : ℕ, densePrefixSupremum f n) = ⨆ t : T, f t := by
  change (⨆ n : ℕ, partialSups (fun k : ℕ ↦ f (denseSeq T k)) n) = _
  rw [ciSup_partialSups_eq']
  exact iSup_denseSeq_eq_iSup f hf

/-- If the range of `f` is bounded above, its dense prefix suprema converge
monotonically to its supremum on the whole space.-/
theorem tendsto_densePrefixSupremum (f : T → ℝ) (hf : Continuous f)
    (hbdd : BddAbove (Set.range f)) :
    Tendsto (densePrefixSupremum f) atTop (nhds (⨆ t : T, f t)) := by
  have hbddDense : BddAbove (Set.range (fun k : ℕ ↦ f (denseSeq T k))) :=
    hbdd.mono (by
      rintro _ ⟨k, rfl⟩
      exact ⟨denseSeq T k, rfl⟩)
  have hbddPrefix :
      BddAbove (Set.range (partialSups (fun k : ℕ ↦ f (denseSeq T k)))) :=
    bddAbove_range_partialSups.mpr hbddDense
  have hlim := tendsto_atTop_ciSup
    (partialSups_monotone (fun k : ℕ ↦ f (denseSeq T k))) hbddPrefix
  rw [ciSup_partialSups_eq', iSup_denseSeq_eq_iSup f hf] at hlim
  exact hlim

/-- The maximum of the absolute values of the first `n + 1` dense
evaluations.-/
def densePrefixAbsSupremum (f : T → ℝ) (n : ℕ) : ℝ :=
  densePrefixSupremum (fun t ↦ |f t|) n

/-- Absolute dense prefix suprema form a monotone sequence.-/
theorem densePrefixAbsSupremum_monotone (f : T → ℝ) :
    Monotone (densePrefixAbsSupremum f) :=
  densePrefixSupremum_monotone _

/-- The supremum of the absolute dense prefix suprema is the full absolute
supremum.-/
theorem iSup_densePrefixAbsSupremum_eq_iSup_abs (f : T → ℝ)
    (hf : Continuous f) :
    (⨆ n : ℕ, densePrefixAbsSupremum f n) = ⨆ t : T, |f t| := by
  exact iSup_densePrefixSupremum_eq_iSup (fun t ↦ |f t|) hf.abs

/-- Under boundedness of the absolute range, the absolute dense prefix
suprema converge to the full absolute supremum.-/
theorem tendsto_densePrefixAbsSupremum (f : T → ℝ) (hf : Continuous f)
    (hbdd : BddAbove (Set.range fun t ↦ |f t|)) :
    Tendsto (densePrefixAbsSupremum f) atTop (nhds (⨆ t : T, |f t|)) := by
  exact tendsto_densePrefixSupremum (fun t ↦ |f t|) hf.abs hbdd

end DenseSupremum

section Measurability

variable [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
  [MeasurableSpace Omega]

/-- A dense prefix supremum is measurable whenever all the corresponding
dense evaluations are measurable.-/
theorem measurable_densePrefixSupremum (F : Omega → T → ℝ)
    (hF : ∀ k : ℕ, Measurable (fun omega ↦ F omega (denseSeq T k))) (n : ℕ) :
    Measurable (fun omega ↦ densePrefixSupremum (F omega) n) := by
  rw [show (fun omega ↦ densePrefixSupremum (F omega) n) =
      (fun omega ↦
        (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
          (fun k ↦ F omega (denseSeq T k))) by
    funext omega
    exact densePrefixSupremum_eq_sup'_range _ n]
  exact Finset.measurable_range_sup'' fun k _hk ↦ hF k

/-- An absolute dense prefix supremum is measurable whenever all dense
evaluations are measurable.-/
theorem measurable_densePrefixAbsSupremum (F : Omega → T → ℝ)
    (hF : ∀ k : ℕ, Measurable (fun omega ↦ F omega (denseSeq T k))) (n : ℕ) :
    Measurable (fun omega ↦ densePrefixAbsSupremum (F omega) n) := by
  apply measurable_densePrefixSupremum (fun omega t ↦ |F omega t|) _ n
  intro k
  simpa only [Real.norm_eq_abs] using (hF k).norm

end Measurability

end RandomSetTheory
