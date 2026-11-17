/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Suslin.Regular
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Suslin.Tree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Viable prefixes and normalized Suslin schemes

A finite witness prefix is viable when it extends to one complete Baire witness together with one
object satisfying every component of the scheme along that witness. Viable prefixes form a pruned
tree: the next value of a supplied witness gives an extension. This is an existential theorem, not
a globally selected extension function.

`normalizeScheme A s` keeps the regularized component at viable prefixes and is empty at impossible
prefixes. It is regular and pruned at the component-support level, is closed when all components of
`A` are closed, and has exactly the same Suslin operation as `A`.
-/

open Set

universe u

namespace DescriptiveSetTheory

open Tree

variable {X : Type u}

/-- A prefix is viable when it occurs on a complete scheme witness.-/
def IsViablePrefix (A : List ℕ → Set X) (s : List ℕ) : Prop :=
  ∃ x : X, ∃ f : ℕ → ℕ,
    initialSegment f s.length = s ∧ ∀ n, x ∈ A (initialSegment f n)

private theorem take_initialSegment (f : ℕ → ℕ) {m n : ℕ} (hmn : m ≤ n) :
    (initialSegment f n).take m = initialSegment f m := by
  apply List.ext_getElem
  · simp [length_initialSegment, hmn]
  · intro i hi₁ hi₂
    simp [initialSegment]

/-- Every prefix of a viable prefix is viable.-/
theorem IsViablePrefix.of_prefix {A : List ℕ → Set X} {s t : List ℕ}
    (ht : IsViablePrefix A t) (hst : s <+: t) : IsViablePrefix A s := by
  rcases ht with ⟨x, f, hft, hf⟩
  rcases hst with ⟨u, rfl⟩
  refine ⟨x, f, ?_, hf⟩
  have hlen : s.length ≤ (s ++ u).length := by simp
  calc
    initialSegment f s.length = (initialSegment f (s ++ u).length).take s.length :=
      (take_initialSegment f hlen).symm
    _ = (s ++ u).take s.length := congrArg (List.take s.length) hft
    _ = s := by simp

/-- A supplied viability witness gives at least one viable immediate extension.-/
theorem IsViablePrefix.exists_extension {A : List ℕ → Set X} {s : List ℕ}
    (hs : IsViablePrefix A s) : ∃ a, IsViablePrefix A (s ++ [a]) := by
  rcases hs with ⟨x, f, hfs, hf⟩
  refine ⟨f s.length, x, f, ?_, hf⟩
  rw [List.length_append, List.length_singleton, initialSegment_succ, hfs]

/-- The tree of exactly those finite witness prefixes that extend to a complete scheme witness.-/
def viablePrefixTree (A : List ℕ → Set X) : Descriptive.tree ℕ where
  val := {s | IsViablePrefix A s}
  property := by
    intro s a hs
    exact hs.of_prefix ⟨[a], rfl⟩

@[simp]
theorem mem_viablePrefixTree {A : List ℕ → Set X} {s : List ℕ} :
    s ∈ viablePrefixTree A ↔ IsViablePrefix A s :=
  Iff.rfl

/-- A tree is pruned when every node has an immediate successor in the tree.-/
def IsPrunedTree (T : Descriptive.tree ℕ) : Prop :=
  ∀ ⦃s : List ℕ⦄, s ∈ T → ∃ a, s ++ [a] ∈ T

/-- The viable-prefix tree is pruned, vacuously when it is empty.-/
theorem isPrunedTree_viablePrefixTree (A : List ℕ → Set X) :
    IsPrunedTree (viablePrefixTree A) := by
  intro s hs
  exact hs.exists_extension

/-- A scheme is pruned at the support level when every nonempty component has a nonempty immediate
successor component. This predicate makes no choice of successor.-/
def IsPrunedSuslinScheme (A : List ℕ → Set X) : Prop :=
  ∀ ⦃s : List ℕ⦄, (A s).Nonempty → ∃ a, (A (s ++ [a])).Nonempty

/-- Keep the regularized value at viable prefixes and delete every impossible prefix.-/
def normalizeScheme (A : List ℕ → Set X) (s : List ℕ) : Set X :=
  {x | IsViablePrefix A s ∧ x ∈ regularizeScheme A s}

@[simp]
theorem mem_normalizeScheme {A : List ℕ → Set X} {s : List ℕ} {x : X} :
    x ∈ normalizeScheme A s ↔ IsViablePrefix A s ∧ x ∈ regularizeScheme A s :=
  Iff.rfl

/-- Normalization is pointwise contained in the original scheme.-/
theorem normalizeScheme_subset (A : List ℕ → Set X) (s : List ℕ) :
    normalizeScheme A s ⊆ A s := by
  intro x hx
  exact regularizeScheme_subset A s hx.2

/-- Normalized components decrease along witness-prefix extension.-/
theorem isRegularSuslinScheme_normalizeScheme (A : List ℕ → Set X) :
    IsRegularSuslinScheme (normalizeScheme A) := by
  intro s t hst x hx
  exact ⟨hx.1.of_prefix hst, isRegularSuslinScheme_regularizeScheme A hst hx.2⟩

private theorem eq_initialSegment_length_of_prefix (f : ℕ → ℕ)
    {s : List ℕ} {n : ℕ} (hs : s <+: initialSegment f n) :
    s = initialSegment f s.length := by
  have hlen : s.length ≤ n := by simpa using hs.length_le
  have htake := congrArg (List.take s.length) (List.prefix_iff_eq_append.mp hs)
  rw [List.take_append, List.take_length, Nat.sub_self, List.take_zero, List.append_nil] at htake
  rw [take_initialSegment f hlen] at htake
  exact htake

/-- A normalized component is nonempty exactly at a viable prefix.-/
theorem nonempty_normalizeScheme_iff (A : List ℕ → Set X) (s : List ℕ) :
    (normalizeScheme A s).Nonempty ↔ IsViablePrefix A s := by
  constructor
  · rintro ⟨x, hx⟩
    exact hx.1
  · intro hs
    rcases hs with ⟨x, f, hfs, hf⟩
    let hs : IsViablePrefix A s := ⟨x, f, hfs, hf⟩
    refine ⟨x, hs, ?_⟩
    intro t hts
    rw [← hfs] at hts
    rw [eq_initialSegment_length_of_prefix f hts]
    exact hf t.length

/-- The component support of every normalized scheme is pruned.-/
theorem isPrunedSuslinScheme_normalizeScheme (A : List ℕ → Set X) :
    IsPrunedSuslinScheme (normalizeScheme A) := by
  intro s hs
  rw [nonempty_normalizeScheme_iff] at hs
  rcases hs.exists_extension with ⟨a, ha⟩
  exact ⟨a, (nonempty_normalizeScheme_iff A _).2 ha⟩

/-- Deleting impossible prefixes and regularizing the rest preserves the Suslin operation.-/
@[simp]
theorem suslinOperation_normalizeScheme (A : List ℕ → Set X) :
    suslinOperation (normalizeScheme A) = suslinOperation A := by
  apply Set.Subset.antisymm
  · exact suslinOperation_mono fun s => normalizeScheme_subset A s
  · intro x hx
    rcases suslinOperation_subset_regularizeScheme A hx with ⟨f, hfreg⟩
    have hf : ∀ n, x ∈ A (initialSegment f n) :=
      fun n => regularizeScheme_subset A _ (hfreg n)
    refine ⟨f, fun n => ⟨?_, hfreg n⟩⟩
    exact ⟨x, f, by simp, hf⟩

section Topology

variable [TopologicalSpace X]

/-- Prefix regularization preserves closed-valuedness.-/
theorem isClosed_regularizeScheme (A : List ℕ → Set X)
    (hA : ∀ s, IsClosed (A s)) (s : List ℕ) : IsClosed (regularizeScheme A s) := by
  rw [show regularizeScheme A s = ⋂ t : {t : List ℕ // t <+: s}, A t.1 by
    ext x
    simp [regularizeScheme]]
  exact isClosed_iInter fun t => hA t.1

/-- Normalization preserves closed-valuedness.-/
theorem isClosed_normalizeScheme (A : List ℕ → Set X)
    (hA : ∀ s, IsClosed (A s)) (s : List ℕ) : IsClosed (normalizeScheme A s) := by
  by_cases hs : IsViablePrefix A s
  · have heq : normalizeScheme A s = regularizeScheme A s := by
      ext x
      simp [normalizeScheme, hs]
    rw [heq]
    exact isClosed_regularizeScheme A hA s
  · have heq : normalizeScheme A s = ∅ := by
      ext x
      simp [normalizeScheme, hs]
    rw [heq]
    exact isClosed_empty

end Topology

namespace Tree

/-- A tree projection is also the operation of the normalized form of its associated scheme.-/
theorem projectedBody_eq_suslinOperation_normalizeScheme
    (T : Descriptive.tree (X × ℕ)) :
    projectedBody T = suslinOperation (normalizeScheme (suslinScheme T)) := by
  rw [suslinOperation_normalizeScheme]
  exact projectedBody_eq_suslinOperation T

/-- Baire analytic sets are exactly the operations of closed, regular, support-pruned schemes.-/
theorem analyticSet_iff_exists_normalized_closed_suslinScheme_baire
    (s : Set (ℕ → ℕ)) :
    MeasureTheory.AnalyticSet s ↔
      ∃ A : List ℕ → Set (ℕ → ℕ),
        (∀ t, IsClosed (A t)) ∧ IsRegularSuslinScheme A ∧
          IsPrunedSuslinScheme A ∧ suslinOperation A = s := by
  constructor
  · intro hs
    rcases (analyticSet_iff_exists_closed_suslinScheme_baire s).1 hs with ⟨A, hA, hAs⟩
    refine ⟨normalizeScheme A, isClosed_normalizeScheme A hA,
      isRegularSuslinScheme_normalizeScheme A,
      isPrunedSuslinScheme_normalizeScheme A, ?_⟩
    rw [suslinOperation_normalizeScheme, hAs]
  · rintro ⟨A, hA, -, -, rfl⟩
    exact analyticSet_suslinOperation_of_isClosed A hA

end Tree

end DescriptiveSetTheory
