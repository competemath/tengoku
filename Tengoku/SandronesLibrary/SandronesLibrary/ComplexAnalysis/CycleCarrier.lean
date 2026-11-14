/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.BanachPathIntegral
import Tengoku.SandronesLibrary.SandronesLibrary.ComplexAnalysis.DyadicPathIntegralAssembly
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.PiecewiseC1Path
import Tengoku.Seed.Data.Finsupp.Basic
import Tengoku.Seed.Algebra.BigOperators.Finsupp.Basic
import Tengoku.Seed.LinearAlgebra.Finsupp.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The cycle carrier and the ℤ-linear cycle integral

A *closed path* is a path whose endpoints coincide, the common base point being part of
the data.  A *cycle* is a finitely supported `ℤ`-valued formal sum of closed paths, i.e. an
element of `ClosedPath →₀ ℤ`: the textbook finite formal sum of closed curves, carried by
the free abelian group on closed paths.

This file provides the elementary predicates on cycles — their trace, the property that
every piece is piecewise C¹, the property that every piece stays inside a set, and per-piece
integrability of an integrand — together with the cycle integral `∮_γ f(z) dz`.  The latter
is defined through `Finsupp.linearCombination ℤ` of the Banach-valued path integral over the
pieces, so it is `ℤ`-linear in the cycle *by construction*; `cycleIntegral_add`,
`cycleIntegral_smul`, `cycleIntegral_neg` and `cycleIntegral_sub` are then immediate from the
linear-map API rather than reproved.  Linearity in the integrand
(`cycleIntegral_add_integrand`) is checked piece by piece, under per-piece integrability.

The closing section records the first genuine consumers of the carrier: a cycle integral
vanishes when every piece does, and consequently the cycle integral of a derivative over a
cycle supported in its holomorphy domain vanishes.  These make the carrier a real
upper-level interface rather than a decorative alias.

Current entries:

* `complex-analysis.integral.finite-cycle-foundation`: the cycle carrier, its predicates, and
  the `ℤ`-linear cycle integral with its linearity, single-piece, closure, vanishing and
  primitive-consumer lemmas.
-/

noncomputable section

namespace SandronesLibrary.ComplexAnalysis

/-- A closed path is a path whose endpoints coincide; the base point is part of the data.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
abbrev ClosedPath : Type := Σ a : ℂ, Path a a

/-- A cycle is a finitely supported ℤ-valued formal sum of closed paths.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
abbrev Cycle : Type := ClosedPath →₀ ℤ

namespace Cycle

/-- The trace of a cycle: the union of the ranges of its closed pieces.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
def trace (γ : Cycle) : Set ℂ := {w | ∃ c ∈ γ.support, w ∈ Set.range c.2}

/-- Every piece is piecewise C¹.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
def PiecewiseC1 (γ : Cycle) : Prop :=
  ∀ c ∈ γ.support, SandronesLibrary.Topology.Path.PiecewiseC1 c.2

/-- Every piece stays in `U`.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
def SupportedIn (γ : Cycle) (U : Set ℂ) : Prop := ∀ c ∈ γ.support, Set.range c.2 ⊆ U

/-- The integrand is path-integrable on every piece.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
def Integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → F) (γ : Cycle) : Prop := ∀ c ∈ γ.support, BanachPathIntegrable f c.2

end Cycle

/-- The integral of a Banach-valued integrand over a cycle, ℤ-linear in the cycle by
construction.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
noncomputable def cycleIntegral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → F) : Cycle →ₗ[ℤ] F :=
  Finsupp.linearCombination ℤ (fun c : ClosedPath => banachPathIntegral f c.2)

/-- A piece of a sum of cycles is a piece of one of the summands.  This is the support
membership form of `Finsupp.support_add`; it avoids `DecidableEq ClosedPath`, which does
not exist.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
theorem mem_support_or {γ δ : Cycle} {c : ClosedPath} (hc : c ∈ (γ + δ).support) :
    c ∈ γ.support ∨ c ∈ δ.support := by
  have hne : γ c + δ c ≠ 0 := Finsupp.mem_support_iff.mp hc
  rcases eq_or_ne (γ c) 0 with h | h
  · right
    refine Finsupp.mem_support_iff.mpr fun h2 => hne ?_
    rw [h, h2, zero_add]
  · exact Or.inl (Finsupp.mem_support_iff.mpr h)

/-- Evaluation of the cycle integral as the ℤ-weighted sum of the piece integrals.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
theorem cycleIntegral_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → F) (γ : Cycle) :
    cycleIntegral f γ = γ.sum (fun c n => n • banachPathIntegral f c.2) :=
  rfl

/-- The cycle integral of the zero cycle vanishes.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
@[simp]
theorem cycleIntegral_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → F) : cycleIntegral f (0 : Cycle) = 0 :=
  map_zero (cycleIntegral f)

/-- The cycle integral of a single closed path is the integer multiple of its path integral.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
@[simp]
theorem cycleIntegral_single {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → F) (c : ClosedPath) (n : ℤ) :
    cycleIntegral f (Finsupp.single c n) = n • banachPathIntegral f c.2 := by
  show Finsupp.linearCombination ℤ (fun c : ClosedPath => banachPathIntegral f c.2)
      (Finsupp.single c n) = n • banachPathIntegral f c.2
  exact Finsupp.linearCombination_single (v := fun c : ClosedPath => banachPathIntegral f c.2) ℤ n c

/-- The cycle integral is additive in the cycle.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
theorem cycleIntegral_add {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → F) (γ δ : Cycle) :
    cycleIntegral f (γ + δ) = cycleIntegral f γ + cycleIntegral f δ :=
  map_add (cycleIntegral f) γ δ

/-- The cycle integral is ℤ-homogeneous in the cycle.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
theorem cycleIntegral_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → F) (n : ℤ) (γ : Cycle) :
    cycleIntegral f (n • γ) = n • cycleIntegral f γ :=
  map_smul (cycleIntegral f) n γ

/-- Negating the cycle negates its integral.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
theorem cycleIntegral_neg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → F) (γ : Cycle) :
    cycleIntegral f (-γ) = -cycleIntegral f γ :=
  map_neg (cycleIntegral f) γ

/-- Subtracting cycles subtracts their integrals.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
theorem cycleIntegral_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → F) (γ δ : Cycle) :
    cycleIntegral f (γ - δ) = cycleIntegral f γ - cycleIntegral f δ :=
  map_sub (cycleIntegral f) γ δ

/-- Linearity in the integrand, under per-piece integrability.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
theorem cycleIntegral_add_integrand (f g : ℂ → ℂ) (γ : Cycle)
    (hf : γ.Integrable f) (hg : γ.Integrable g) :
    cycleIntegral (fun z => f z + g z) γ = cycleIntegral f γ + cycleIntegral g γ := by
  rw [cycleIntegral_apply, cycleIntegral_apply, cycleIntegral_apply,
    Finsupp.sum_of_support_subset γ (Finset.Subset.refl _)
      (fun c n => n • banachPathIntegral (fun z => f z + g z) c.2) (fun i _ => by simp),
    Finsupp.sum_of_support_subset γ (Finset.Subset.refl _)
      (fun c n => n • banachPathIntegral f c.2) (fun i _ => by simp),
    Finsupp.sum_of_support_subset γ (Finset.Subset.refl _)
      (fun c n => n • banachPathIntegral g c.2) (fun i _ => by simp),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [banachPathIntegral_add (hf c (by simpa using hc)) (hg c (by simpa using hc)), smul_add]

/-- The sum of two piecewise-C¹ cycles is piecewise C¹.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
theorem Cycle.PiecewiseC1.add {γ δ : Cycle} (hγ : γ.PiecewiseC1) (hδ : δ.PiecewiseC1) :
    (γ + δ).PiecewiseC1 := by
  intro c hc
  rcases mem_support_or hc with h | h
  · exact hγ c h
  · exact hδ c h

/-- The sum of two cycles supported in `U` is supported in `U`.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
theorem Cycle.SupportedIn.add {γ δ : Cycle} {U : Set ℂ}
    (hγ : γ.SupportedIn U) (hδ : δ.SupportedIn U) : (γ + δ).SupportedIn U := by
  intro c hc
  rcases mem_support_or hc with h | h
  · exact hγ c h
  · exact hδ c h

/-- The sum of two cycles integrable for `f` is integrable for `f`.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
theorem Cycle.Integrable.add {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : ℂ → F} {γ δ : Cycle}
    (hγ : γ.Integrable f) (hδ : δ.Integrable f) : (γ + δ).Integrable f := by
  intro c hc
  rcases mem_support_or hc with h | h
  · exact hγ c h
  · exact hδ c h

/-- Unfolding the trace of a cycle.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
theorem Cycle.mem_trace {γ : Cycle} {w : ℂ} :
    w ∈ γ.trace ↔ ∃ c ∈ γ.support, w ∈ Set.range c.2 :=
  Iff.rfl

/-- The trace of a sum is contained in the union of the traces.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
theorem Cycle.trace_add_subset {γ δ : Cycle} : (γ + δ).trace ⊆ γ.trace ∪ δ.trace := by
  intro w hw
  rcases (Cycle.mem_trace.mp hw) with ⟨c, hc, hrange⟩
  rcases mem_support_or hc with h | h
  · exact Or.inl (Cycle.mem_trace.mpr ⟨c, h, hrange⟩)
  · exact Or.inr (Cycle.mem_trace.mpr ⟨c, h, hrange⟩)

/-- A cycle integral over a finite ℤ-combination vanishes as soon as every piece does.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
theorem cycleIntegral_eq_zero_of_forall_piece_eq_zero
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : ℂ → F) (γ : Cycle)
    (h : ∀ c ∈ γ.support, banachPathIntegral f c.2 = 0) :
    cycleIntegral f γ = 0 := by
  rw [cycleIntegral_apply,
    Finsupp.sum_of_support_subset γ (Finset.Subset.refl _)
      (fun c n => n • banachPathIntegral f c.2) (fun i _ => by simp)]
  exact Finset.sum_eq_zero fun c hc => by rw [h c (by simpa using hc), smul_zero]

/-- A cycle integral of a derivative (`f = g'` on `U`) over a cycle supported in `U` vanishes.
This is the textbook "integral of a derivative around a closed cycle" statement.

> **Entry**: complex-analysis.integral.finite-cycle-foundation-/
theorem cycleIntegral_eq_zero_of_primitive
    {U : Set ℂ} {f g : ℂ → ℂ} (γ : Cycle)
    (hC1 : γ.PiecewiseC1) (hUγ : γ.SupportedIn U)
    (hg : ∀ z ∈ U, HasDerivAt g (f z) z) (hf : ContinuousOn f U) :
    cycleIntegral f γ = 0 := by
  apply cycleIntegral_eq_zero_of_forall_piece_eq_zero
  intro c hc
  have hadm : AdmissiblePath f U c.2 :=
    admissiblePath_of_piecewiseC1 (hC1 c hc) (hUγ c hc) hf
  rw [banachPathIntegral_complex_eq_pathIntegral,
    pathIntegral_eq_sub_of_primitive_of_admissiblePath hadm hg, sub_self]

end SandronesLibrary.ComplexAnalysis
