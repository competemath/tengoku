/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Seed.Analysis.SpecialFunctions.Integrals.Basic
import Tengoku.Seed.Topology.Order.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Abstract Interval Interface

This file defines the abstract notion of intervals as subsets of ℝ,
with semantic properties. This provides the mathematical foundation
that `IntervalReal` will implement computationally.

## Main definitions

* Lemmas about `Set.Icc` (closed intervals) relevant to interval arithmetic
* Convexity and integrability properties

## Design notes

We primarily use `Set.Icc a b` from Mathlib as our semantic interval type.
This file collects lemmas and abstractions useful for verified numerics.
-/

namespace LeanCert.Core

/-! ### Interval membership and operations -/

/-- A real number is in the interval [a, b] -/
abbrev mem_Icc (x a b : ℝ) : Prop := a ≤ x ∧ x ≤ b

/--
@isnad1 id=iff.0h3v.s4.ccbcb6835cc0 from=translated src=- shape=6dee174a vocab=b4ba2dc9
-/
theorem mem_Icc_iff (x a b : ℝ) : mem_Icc x a b ↔ x ∈ Set.Icc a b := Iff.rfl

/-! ### Interval arithmetic semantics

These lemmas establish the semantic foundation for interval arithmetic:
if x ∈ [a, b] and y ∈ [c, d], then x ⊕ y ∈ [a ⊕ c, b ⊕ d] (for appropriate ⊕).
-/

/-- Addition preserves interval membership
@isnad1 id=mem.2h6v.s6.5d01b0f17faf from=translated src=- shape=7b711573 vocab=921bf9c6
-/
theorem add_mem_Icc {x y a b c d : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d) :
    x + y ∈ Set.Icc (a + c) (b + d) := by
  simp only [Set.mem_Icc] at *
  constructor <;> linarith

/-- Negation reverses interval bounds
@isnad1 id=mem.1h3v.s5.ac1889c01427 from=translated src=- shape=1c904a9e vocab=666617d0
-/
theorem neg_mem_Icc {x a b : ℝ} (hx : x ∈ Set.Icc a b) :
    -x ∈ Set.Icc (-b) (-a) := by
  simp only [Set.mem_Icc] at *
  constructor <;> linarith

/-- Subtraction on intervals
@isnad1 id=mem.2h6v.s6.09137f6eba6c from=translated src=- shape=9ea5668e vocab=e30d45a3
-/
theorem sub_mem_Icc {x y a b c d : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d) :
    x - y ∈ Set.Icc (a - d) (b - c) := by
  simp only [Set.mem_Icc] at *
  constructor <;> linarith

/-! ### Convexity -/

/-- Closed intervals are convex
@isnad1 id=convex.0h2v.s4.3b3afd3a3b0b from=translated src=- shape=59a17b85 vocab=f0c8472e
-/
theorem Icc_convex (a b : ℝ) : Convex ℝ (Set.Icc a b) := convex_Icc a b

/-! ### Compactness -/

/-- Nonempty closed bounded intervals are compact
@isnad1 id=iscompac.0h2v.s4.167d279ebe72 from=translated src=- shape=dc04ab9d vocab=80a90528
-/
theorem Icc_compact (a b : ℝ) : IsCompact (Set.Icc a b) := isCompact_Icc

/-! ### Continuous functions on intervals -/

/-- A continuous function on a compact interval attains its bounds
@isnad1 id=ex.2h3v.s6.7114346c84a0 from=translated src=- shape=00c4e443 vocab=6a24432a
-/
theorem continuous_Icc_bounds {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous f) :
    ∃ (lo hi : ℝ), (∀ x ∈ Set.Icc a b, lo ≤ f x ∧ f x ≤ hi) ∧
      (∃ x ∈ Set.Icc a b, f x = lo) ∧ (∃ x ∈ Set.Icc a b, f x = hi) := by
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab
  have hcpt : IsCompact (Set.Icc a b) := isCompact_Icc
  obtain ⟨xmin, hxmin_mem, hxmin⟩ := hcpt.exists_isMinOn hne hf.continuousOn
  obtain ⟨xmax, hxmax_mem, hxmax⟩ := hcpt.exists_isMaxOn hne hf.continuousOn
  exact ⟨f xmin, f xmax,
    fun x hx => ⟨hxmin hx, hxmax hx⟩,
    ⟨xmin, hxmin_mem, rfl⟩,
    ⟨xmax, hxmax_mem, rfl⟩⟩

end LeanCert.Core
