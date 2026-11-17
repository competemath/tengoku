/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Suslin.Regular
import Tengoku.Seed.Data.Set.SymmDiff
import Tengoku.Seed.Topology.Baire.BaireMeasurable
import Tengoku.Seed.Topology.Bases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Baire property under the Suslin operation

Sets with the property of Baire are closed under the Suslin operation in every second-countable
topological space. The proof is the category form of Nikodým's theorem.

For an arbitrary set `S`, a countable basis produces a Baire-measurable cover `B` such that every
Baire-measurable subset of `B \ S` is meagre. For a regular Suslin scheme, apply this cover to the
Suslin value below every finite node, intersect the cover with the component at that node, and
collect the failures of the immediate-successor equation. Every failure is meagre. Outside their
countable union, dependent choice through the finite nodes reconstructs a complete branch. Thus
the root Suslin value differs from one Baire-measurable set by a meagre set.

Finite-prefix regularization then removes regularity from the public theorem without strengthening
the component hypothesis. No analyticity or Polish-space assumption is used.
-/

open Set
open scoped Topology symmDiff

universe u

namespace DescriptiveSetTheory

open Tree

variable {X : Type u}

private def prependSequence (a : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => a
  | n + 1 => f n

private def tailSequence (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  f (n + 1)

@[simp]
private theorem prependSequence_tailSequence (f : ℕ → ℕ) :
    prependSequence (f 0) (tailSequence f) = f := by
  funext n
  cases n <;> rfl

private theorem initialSegment_prependSequence (a : ℕ) (f : ℕ → ℕ) (n : ℕ) :
    initialSegment (prependSequence a f) (n + 1) = [a] ++ initialSegment f n := by
  induction n with
  | zero =>
      rw [initialSegment_succ, initialSegment_zero]
      rfl
  | succ n ih =>
      rw [initialSegment_succ, ih, initialSegment_succ]
      rfl

/-- The Suslin value of a scheme below a finite node.-/
def subtreeSuslinOperation (A : List ℕ → Set X) (s : List ℕ) : Set X :=
  suslinOperation fun t => A (s ++ t)

/-- Membership in a subtree Suslin value expands along branches extending its root.
@isnad1 id=iff.0h4v.s5.5072343eb445 from=translated src=- shape=6d793fa9 vocab=576a1b28
-/
@[simp]
theorem mem_subtreeSuslinOperation {A : List ℕ → Set X} {s : List ℕ} {x : X} :
    x ∈ subtreeSuslinOperation A s ↔
      ∃ f : ℕ → ℕ, ∀ n, x ∈ A (s ++ initialSegment f n) :=
  Iff.rfl

/-- Every subtree Suslin value lies in its root component.
@isnad1 id=le.0h3v.s4.b43d37eab073 from=translated src=- shape=309d2bd6 vocab=5e46cace
-/
theorem subtreeSuslinOperation_subset (A : List ℕ → Set X) (s : List ℕ) :
    subtreeSuslinOperation A s ⊆ A s := by
  rintro x ⟨f, hf⟩
  simpa using hf 0

/-- For a regular scheme, a subtree value is exactly the union of its immediate child values.
@isnad1 id=eq.1h3v.s5.bae579457ba4 from=translated src=- shape=6b0fe667 vocab=a391f4bb
-/
theorem subtreeSuslinOperation_eq_iUnion_children {A : List ℕ → Set X}
    (hA : IsRegularSuslinScheme A) (s : List ℕ) :
    subtreeSuslinOperation A s = ⋃ a, subtreeSuslinOperation A (s ++ [a]) := by
  apply Set.Subset.antisymm
  · rintro x ⟨f, hf⟩
    refine mem_iUnion.2 ⟨f 0, ?_⟩
    refine ⟨tailSequence f, fun n => ?_⟩
    have h := hf (n + 1)
    have hseg := initialSegment_prependSequence (f 0) (tailSequence f) n
    rw [prependSequence_tailSequence] at hseg
    rw [hseg] at h
    simpa [List.append_assoc] using h
  · rintro x hx
    rcases mem_iUnion.1 hx with ⟨a, f, hf⟩
    refine ⟨prependSequence a f, ?_⟩
    intro n
    cases n with
    | zero =>
        have hchild : x ∈ A (s ++ [a]) := by simpa using hf 0
        have hroot : x ∈ A s :=
          hA (show s <+: s ++ [a] from ⟨[a], rfl⟩) hchild
        simpa using hroot
    | succ n =>
        rw [initialSegment_prependSequence]
        simpa [List.append_assoc] using hf n

private theorem exists_initialSegment_branch {H : List ℕ → Set X} {x : X}
    (hroot : x ∈ H [])
    (hstep : ∀ s : List ℕ, x ∈ H s → ∃ a, x ∈ H (s ++ [a])) :
    ∃ f : ℕ → ℕ, ∀ n, x ∈ H (initialSegment f n) := by
  classical
  let next : List ℕ → ℕ := fun s =>
    if hs : x ∈ H s then Classical.choose (hstep s hs) else 0
  have hnext (s : List ℕ) (hs : x ∈ H s) : x ∈ H (s ++ [next s]) := by
    rw [show next s = Classical.choose (hstep s hs) by simp [next, hs]]
    exact Classical.choose_spec (hstep s hs)
  let path : ℕ → List ℕ := fun n =>
    Nat.rec [] (fun _ s => s ++ [next s]) n
  have path_zero : path 0 = [] := rfl
  have path_succ (n : ℕ) : path (n + 1) = path n ++ [next (path n)] := rfl
  have hpath : ∀ n, x ∈ H (path n) := by
    intro n
    induction n with
    | zero => simpa [path_zero] using hroot
    | succ n ih =>
        rw [path_succ]
        exact hnext (path n) ih
  let f : ℕ → ℕ := fun n => next (path n)
  refine ⟨f, fun n => ?_⟩
  have hsegments : ∀ m, initialSegment f m = path m := by
    intro m
    induction m with
    | zero => simp [path_zero]
    | succ m ih =>
        rw [initialSegment_succ, ih, path_succ]
  rw [hsegments n]
  exact hpath n

section Topology

variable [TopologicalSpace X]

private theorem isMeagre_symmDiff_of_residualEq {s t : Set X} (h : s =ᵇ t) :
    IsMeagre (s ∆ t) := by
  rw [IsMeagre]
  filter_upwards [h] with x hx
  simp only [mem_compl_iff, mem_symmDiff]
  tauto

private theorem residualEq_of_isMeagre_symmDiff {s t : Set X}
    (h : IsMeagre (s ∆ t)) : s =ᵇ t := by
  rw [Filter.eventuallyEq_set]
  rw [IsMeagre] at h
  filter_upwards [h] with x hx
  simp only [mem_compl_iff, mem_symmDiff] at hx
  tauto

private def smallBasisUnion (b : ℕ → Set X) (A : Set X) : Set X :=
  ⋃ n, ⋃ (_ : IsMeagre (b n ∩ A)), b n

private def baireCoverWithBasis (b : ℕ → Set X) (A : Set X) : Set X :=
  A ∪ (smallBasisUnion b A)ᶜ

private theorem isOpen_smallBasisUnion (b : ℕ → Set X)
    (hb : TopologicalSpace.IsTopologicalBasis (range b)) (A : Set X) :
    IsOpen (smallBasisUnion b A) := by
  apply isOpen_iUnion
  intro n
  apply isOpen_iUnion
  intro _
  exact hb.isOpen (mem_range_self n)

private theorem isMeagre_diff_compl_smallBasisUnion (b : ℕ → Set X) (A : Set X) :
    IsMeagre (A \ (smallBasisUnion b A)ᶜ) := by
  rw [show A \ (smallBasisUnion b A)ᶜ =
      ⋃ n, ⋃ (_ : IsMeagre (b n ∩ A)), A ∩ b n by
    ext x
    simp only [smallBasisUnion, mem_sdiff, mem_compl_iff, mem_iUnion, mem_inter_iff]
    aesop]
  apply isMeagre_iUnion
  intro n
  apply isMeagre_iUnion
  intro hn
  simpa [inter_comm] using hn

private theorem baireMeasurableSet_baireCoverWithBasis (b : ℕ → Set X)
    (hb : TopologicalSpace.IsTopologicalBasis (range b)) (A : Set X) :
    BaireMeasurableSet (baireCoverWithBasis b A) := by
  rw [show baireCoverWithBasis b A =
      (smallBasisUnion b A)ᶜ ∪ (A \ (smallBasisUnion b A)ᶜ) by
    ext x
    simp [baireCoverWithBasis]
    tauto]
  exact (isOpen_smallBasisUnion b hb A).baireMeasurableSet.compl.union
    (isMeagre_diff_compl_smallBasisUnion b A).baireMeasurableSet

private theorem isMeagre_of_baireMeasurableSet_subset_cover_diff
    (b : ℕ → Set X) (hb : TopologicalSpace.IsTopologicalBasis (range b))
    (A C : Set X) (hC : BaireMeasurableSet C)
    (hsub : C ⊆ baireCoverWithBasis b A \ A) : IsMeagre C := by
  rcases hC.residualEq_isOpen with ⟨U, hUopen, hCU⟩
  have herror : IsMeagre (C ∆ U) := isMeagre_symmDiff_of_residualEq hCU
  have hUA : IsMeagre (U ∩ A) := by
    apply herror.mono
    intro x hx
    have hnotC : x ∉ C := fun hxC => (hsub hxC).2 hx.2
    exact mem_symmDiff.2 (Or.inr ⟨hx.1, hnotC⟩)
  have hUsub : U ⊆ smallBasisUnion b A := by
    intro x hxU
    rcases hb.exists_subset_of_mem_open hxU hUopen with ⟨V, hVb, hxV, hVU⟩
    rcases hVb with ⟨n, rfl⟩
    have hn : IsMeagre (b n ∩ A) := by
      apply hUA.mono
      intro y hy
      exact ⟨hVU hy.1, hy.2⟩
    exact mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨hn, hxV⟩⟩
  apply herror.mono
  intro x hxC
  have hxcover := (hsub hxC).1
  have hxnotA := (hsub hxC).2
  have hxsmall : x ∉ smallBasisUnion b A := by
    rcases hxcover with hxA | hxcompl
    · exact (hxnotA hxA).elim
    · exact hxcompl
  exact mem_symmDiff.2 (Or.inl ⟨hxC, fun hxU => hxsmall (hUsub hxU)⟩)

/-- Every set in a second-countable space has a Baire-measurable outer approximation whose
Baire-measurable subsets outside the original set are meagre.
@isnad1 id=ex.0h2v.s5.d9fc7ba38244 from=translated src=- shape=b9d89200 vocab=f3726fde
-/
theorem exists_baireMeasurable_cover [SecondCountableTopology X] (A : Set X) :
    ∃ B : Set X, A ⊆ B ∧ BaireMeasurableSet B ∧
      ∀ ⦃C : Set X⦄, BaireMeasurableSet C → C ⊆ B \ A → IsMeagre C := by
  rcases TopologicalSpace.exists_seq_basis X with ⟨b, hb⟩
  exact ⟨baireCoverWithBasis b A, subset_union_left,
    baireMeasurableSet_baireCoverWithBasis b hb A,
    isMeagre_of_baireMeasurableSet_subset_cover_diff b hb A⟩

namespace BaireMeasurableSet

/-- A Baire-measurable-valued regular Suslin scheme has a Baire-measurable operation.
@isnad1 id=bairemea.2h2v.s5.5e27083b58d5 from=translated src=- shape=0755cca7 vocab=9a50b52e
-/
theorem suslinOperation_of_regular [SecondCountableTopology X] {A : List ℕ → Set X}
    (hcomponents : ∀ s, BaireMeasurableSet (A s))
    (hregular : IsRegularSuslinScheme A) :
    BaireMeasurableSet (suslinOperation A) := by
  classical
  choose B hB using fun s : List ℕ =>
    exists_baireMeasurable_cover (subtreeSuslinOperation A s)
  have hsub (s : List ℕ) : subtreeSuslinOperation A s ⊆ B s :=
    (hB s).1
  have hBaire (s : List ℕ) : BaireMeasurableSet (B s) :=
    (hB s).2.1
  have hsmall (s : List ℕ) {C : Set X} (hC : BaireMeasurableSet C)
      (hCsub : C ⊆ B s \ subtreeSuslinOperation A s) : IsMeagre C :=
    (hB s).2.2 hC hCsub
  let H : List ℕ → Set X := fun s => B s ∩ A s
  let E : List ℕ → Set X := fun s => H s \ ⋃ a, H (s ++ [a])
  let M : Set X := ⋃ s, E s
  have hHBaire (s : List ℕ) : BaireMeasurableSet (H s) :=
    (hBaire s).inter (hcomponents s)
  have hvalueH (s : List ℕ) : subtreeSuslinOperation A s ⊆ H s := by
    intro x hx
    exact ⟨hsub s hx, subtreeSuslinOperation_subset A s hx⟩
  have hEBaire (s : List ℕ) : BaireMeasurableSet (E s) := by
    exact (hHBaire s).diff <| BaireMeasurableSet.iUnion fun a => hHBaire (s ++ [a])
  have hEsub (s : List ℕ) : E s ⊆ B s \ subtreeSuslinOperation A s := by
    intro x hx
    refine ⟨hx.1.1, fun hxvalue => ?_⟩
    have hxchildren : x ∈ ⋃ a, subtreeSuslinOperation A (s ++ [a]) := by
      rw [← subtreeSuslinOperation_eq_iUnion_children hregular s]
      exact hxvalue
    rcases mem_iUnion.1 hxchildren with ⟨a, hxa⟩
    exact hx.2 (mem_iUnion.2 ⟨a, hvalueH (s ++ [a]) hxa⟩)
  have hEMeagre (s : List ℕ) : IsMeagre (E s) :=
    hsmall s (hEBaire s) (hEsub s)
  have hMMeagre : IsMeagre M :=
    isMeagre_iUnion hEMeagre
  have hrootDiff : H [] \ M ⊆ suslinOperation A := by
    intro x hx
    have hstep (s : List ℕ) (hxs : x ∈ H s) : ∃ a, x ∈ H (s ++ [a]) := by
      have hxnotE : x ∉ E s := fun hxE => hx.2 (mem_iUnion.2 ⟨s, hxE⟩)
      have hxunion : x ∈ ⋃ a, H (s ++ [a]) := by
        by_contra hnot
        exact hxnotE ⟨hxs, hnot⟩
      exact mem_iUnion.1 hxunion
    rcases exists_initialSegment_branch hx.1 hstep with ⟨f, hf⟩
    exact ⟨f, fun n => (hf n).2⟩
  have hsymmSub : H [] ∆ suslinOperation A ⊆ M := by
    intro x hx
    rcases mem_symmDiff.1 hx with hxleft | hxright
    · by_contra hxM
      exact hxleft.2 (hrootDiff ⟨hxleft.1, hxM⟩)
    · exact (hxright.2 (hvalueH [] hxright.1)).elim
  have hresidual : H [] =ᵇ suslinOperation A :=
    residualEq_of_isMeagre_symmDiff (hMMeagre.mono hsymmSub)
  exact (hHBaire []).congr hresidual

/-- Finite-prefix regularization preserves Baire-measurable-valuedness.
@isnad1 id=bairemea.1h3v.s4.ebf4503f4b16 from=translated src=- shape=33b93510 vocab=7fbf37a0
-/
theorem regularizeScheme (A : List ℕ → Set X)
    (hA : ∀ s, BaireMeasurableSet (A s)) (s : List ℕ) :
    BaireMeasurableSet (DescriptiveSetTheory.regularizeScheme A s) := by
  rw [show DescriptiveSetTheory.regularizeScheme A s =
      ⋂ t : {t : List ℕ // t <+: s}, A t.1 by
    ext x
    simp [DescriptiveSetTheory.regularizeScheme]]
  exact BaireMeasurableSet.iInter fun t => hA t.1

/-- Sets with the property of Baire are closed under the Suslin operation in a
second-countable topological space.
@isnad1 id=bairemea.1h2v.s4.199e23d9cea1 from=translated src=- shape=86014219 vocab=586d2a03
-/
theorem suslinOperation [SecondCountableTopology X] (A : List ℕ → Set X)
    (hA : ∀ s, BaireMeasurableSet (A s)) :
    BaireMeasurableSet (DescriptiveSetTheory.suslinOperation A) := by
  have hregularized : ∀ s,
      BaireMeasurableSet (DescriptiveSetTheory.regularizeScheme A s) :=
    regularizeScheme A hA
  have hresult := suslinOperation_of_regular hregularized
    (isRegularSuslinScheme_regularizeScheme A)
  rw [DescriptiveSetTheory.suslinOperation_regularizeScheme] at hresult
  exact hresult

end BaireMeasurableSet

/-- Borel-valued schemes are a special case of Baire-measurable-valued schemes.
@isnad1 id=bairemea.1h2v.s5.6cf4d0c91b44 from=translated src=- shape=ef4f0267 vocab=4a58c7c6
-/
theorem baireMeasurableSet_suslinOperation_of_measurable [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (A : List ℕ → Set X)
    (hA : ∀ s, MeasurableSet (A s)) :
    BaireMeasurableSet (suslinOperation A) :=
  BaireMeasurableSet.suslinOperation A fun s => (hA s).baireMeasurableSet

/-- Closed-valued schemes are a special case of Baire-measurable-valued schemes.
@isnad1 id=bairemea.1h2v.s4.302c0cca7e6f from=translated src=- shape=68a225f3 vocab=1bb85ee3
-/
theorem baireMeasurableSet_suslinOperation_of_isClosed [SecondCountableTopology X]
    (A : List ℕ → Set X) (hA : ∀ s, IsClosed (A s)) :
    BaireMeasurableSet (suslinOperation A) :=
  BaireMeasurableSet.suslinOperation A fun s =>
    (hA s).isOpen_compl.baireMeasurableSet.of_compl

end Topology

end DescriptiveSetTheory
