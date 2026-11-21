/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Tengoku
import Tengoku.LeanTnorms.Tnorms.Util.Mathlib
import Tengoku.LeanTnorms.Tnorms.Basic.Defs
import Tengoku.LeanTnorms.Tnorms.Util.Seq

/-!
TODOs:
  * General proof cleanup
  * File docstring
  * Can we resolve the universe issues surrounding TietzeExtension
-/
namespace Tengoku.LeanTnorms end Tengoku.LeanTnorms open Tengoku.LeanTnorms
local infixl:60 " ⇒ " => LImp

universe u v

variable {M : Type v} [UniformSpace M]
variable {X : Type u} [MetricSpace X] [WeaklyLocallyCompactSpace X]

/--
@isnad1 id=isclosed.1h3v.s5.f532a286370b from=translated src=- shape=ad7539b5 vocab=504a7f64
-/
lemma _root_.Tengoku.LeanTnorms.isClosed_seq_of_tendsto {X : Type*} [TopologicalSpace X] [T2Space X] {x : ℕ → X} {y : X}
    (h : Filter.Tendsto x Filter.atTop (nhds y)) : IsClosed (insert y (Set.range x)) := by
  refine IsCompact.isClosed ?_
  exact Filter.Tendsto.isCompact_insert_range h

/--
@isnad1 id=ex.1h3v.s5.d2ab6f802551 from=translated src=- shape=9af8910b vocab=9c152521
-/
lemma _root_.Tengoku.LeanTnorms.exists_subseq_of_infinite_indices {X : Type*} (x : ℕ → X) {A : Set ℕ}
    (h : A.Infinite) : ∃ φ : ℕ → ℕ, StrictMono φ ∧ x '' A = Set.range (x ∘ φ) := by
  have hA : Infinite A := Set.infinite_coe_iff.mpr h
  use Subtype.val ∘ (Nat.Subtype.orderIsoOfNat A)
  constructor
  · refine StrictMono.comp ?_ ?_
    · exact Subtype.strictMono_coe _
    · refine Monotone.strictMono_of_injective ?_ ?_
      · exact OrderIso.monotone _
      · exact Equiv.injective (Nat.Subtype.orderIsoOfNat A).toEquiv
  · ext y
    simp
    constructor
    · intro  ⟨a, ha, haxy⟩
      obtain ⟨n, hn⟩ := (OrderIso.surjective (Nat.Subtype.orderIsoOfNat A)) ⟨a, ha⟩
      use n
      simp [hn, haxy]
    · grind

/--
@isnad1 id=continuo.5h8v.s7.660210cd26f8 from=translated src=- shape=08c4e5a7 vocab=5859d59d
-/
lemma _root_.Tengoku.LeanTnorms.continuousOn_seq_of_tendsto {X M : Type*} [TopologicalSpace X] [TopologicalSpace M]
    [T2Space X] {s : Set X} {g : s → M} {x : ℕ → s} {y : s} {p : ℕ → M} {q : M}
    (hxt : Filter.Tendsto x Filter.atTop (nhds y)) (hx : ∀ n, x n ≠ y)
    (hpt : Filter.Tendsto p Filter.atTop (nhds q))
    (hgx : ∀ n, g (x n)  = p n) (hgy : g y = q) :
    ContinuousOn g ({y} ∪ Set.range x) := by
  rw [continuousOn_iff_isClosed]
  intro t ht
  by_cases! hqt : q ∈ t
  · let A := {i : ℕ | p i ∈ t}
    use {y} ∪ (x '' A)
    constructor
    · by_cases! hA : A.Finite
      · refine Set.Finite.isClosed ?_
        exact Set.Finite.union (Set.finite_singleton y) <| Set.Finite.image x hA
      · obtain ⟨φ, hφ, hxA⟩ := exists_subseq_of_infinite_indices x hA
        rw [hxA]
        have hxt' := Filter.Tendsto.comp hxt <| StrictMono.tendsto_atTop hφ
        exact isClosed_seq_of_tendsto hxt'
    · grind
  · have hyt : y ∉ g⁻¹' t := by grind
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, p n ∉ t := by
      rw [tendsto_atTop_nhds] at hpt
      exact hpt tᶜ hqt IsClosed.isOpen_compl
    use x '' {i : ℕ | x i ∈ g⁻¹' t}
    constructor
    · refine Set.Finite.isClosed ?_
      refine Set.Finite.subset (Set.toFinite (x '' {i | i < N})) ?_
      grind
    · ext z
      simp
      intro hz
      rcases hz with hz | hz
      · simp at hyt
        subst hz
        simp [hyt, hx]
      · grind

/--
@isnad1 id=ex.1h3v.s6.5ba90e7ec1c1 from=translated src=- shape=2b7c8e9c vocab=baa22ee2
-/
lemma _root_.Tengoku.LeanTnorms.exists_open_containing_seq_with_compact_closure {x : ℕ → X} {y : X}
    (h : Filter.Tendsto x Filter.atTop (nhds y)) :
    ∃ U, y ∈ U ∧ Set.range x ⊆ U ∧ IsOpen U ∧ IsCompact (closure U) := by
  suffices ∃ K, IsCompact K ∧ ({y} ∪ Set.range x) ⊆ K by
    obtain ⟨K, hK, hxyK⟩ := this
    obtain ⟨U, hU, hKU, _, hcU⟩ := exists_open_between_and_isCompact_closure hK
        isOpen_univ (Set.subset_univ K)
    use U
    grind
  obtain ⟨K', hK', hKy'⟩ := exists_compact_mem_nhds y
  rw [Filter.tendsto_def] at h
  specialize h K' hKy'
  simp at h
  obtain ⟨N, hN⟩ := h
  let f : Fin N → Set X := fun ⟨n, hn⟩ ↦ Classical.choose (exists_compact_mem_nhds (x n))
  use K' ∪ (⋃ n : Fin N, f n)
  constructor
  · refine IsCompact.union hK' ?_
    refine isCompact_iUnion ?_
    intro n
    exact (Classical.choose_spec (exists_compact_mem_nhds (x n.1))).1
  · rw [Set.union_subset_iff]
    constructor
    · simp [mem_of_mem_nhds hKy']
    intro z
    simp
    intro n hn
    subst hn
    by_cases! hn : n < N
    · right
      use ⟨n, hn⟩
      have hf := Classical.choose_spec (exists_compact_mem_nhds (x n))
      simp [f, mem_of_mem_nhds hf.2]
    · left
      exact hN n hn
-- Tengoku: root names of this library moved to Tengoku.LeanTnorms so they do not collide with other libraries (generated)
