/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.Analysis.Normed.Operator.Compact.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite products of compact operators

A finite family of compact operators `f i : M₁ i → M₂ i` gives a compact operator
`(x i)ᵢ ↦ (f i (x i))ᵢ` on the products (`IsCompactOperator.piMap`).
-/

open Filter Set Topology

/-- The product of finitely many compact operators is a compact operator. -/
theorem IsCompactOperator.piMap {ι : Type*} [Finite ι] {M₁ M₂ : ι → Type*}
    [∀ i, Zero (M₁ i)] [∀ i, TopologicalSpace (M₁ i)] [∀ i, TopologicalSpace (M₂ i)]
    {f : ∀ i, M₁ i → M₂ i} (hf : ∀ i, IsCompactOperator (f i)) :
    IsCompactOperator (fun (x : ∀ i, M₁ i) i ↦ f i (x i)) := by
  choose K hK hKn using hf
  refine ⟨univ.pi K, isCompact_univ_pi hK, ?_⟩
  have : (fun (x : ∀ i, M₁ i) i ↦ f i (x i)) ⁻¹' univ.pi K = univ.pi fun i ↦ f i ⁻¹' K i := by
    ext x
    simp
  rw [this]
  exact set_pi_mem_nhds finite_univ fun i _ ↦ hKn i
