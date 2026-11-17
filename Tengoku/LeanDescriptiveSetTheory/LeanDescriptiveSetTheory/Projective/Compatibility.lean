/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Projective.Closure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Low-level compatibility for finite projective classes

This module gathers the inclusions needed to use Borel, analytic, and coanalytic sets at arbitrary
finite projective levels. Same-polarity monotonicity comes from the closure layer. A product with
the universal Baire witness gives the cross-polarity successor inclusions, and hence membership in
the next Delta level. These are inclusions only; no strictness or hierarchy collapse is asserted.

Products are reduced to continuous coordinate preimages and finite intersection. Their vertical
and horizontal sections have exact membership-form, one-way simplification laws.
-/

open Set

universe u v

namespace DescriptiveSetTheory

/-- Products of two Sigma sets at the same finite level remain Sigma at that level.-/
theorem ProjectiveSigma.prod {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {s : Set X} {t : Set Y} (hs : ProjectiveSigma n s)
    (ht : ProjectiveSigma n t) : ProjectiveSigma n (s ×ˢ t) := by
  have hs' := hs.preimage (continuous_fst : Continuous (Prod.fst : X × Y → X))
  have ht' := ht.preimage (continuous_snd : Continuous (Prod.snd : X × Y → Y))
  rw [show s ×ˢ t = Prod.fst ⁻¹' s ∩ Prod.snd ⁻¹' t by ext; rfl]
  exact hs'.inter ht'

/-- Products of two Pi sets at the same finite level remain Pi at that level.-/
theorem ProjectivePi.prod {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {s : Set X} {t : Set Y} (hs : ProjectivePi n s)
    (ht : ProjectivePi n t) : ProjectivePi n (s ×ˢ t) := by
  have hs' := hs.preimage (continuous_fst : Continuous (Prod.fst : X × Y → X))
  have ht' := ht.preimage (continuous_snd : Continuous (Prod.snd : X × Y → Y))
  rw [show s ×ˢ t = Prod.fst ⁻¹' s ∩ Prod.snd ⁻¹' t by ext; rfl]
  exact hs'.inter ht'

/-- Products of two Delta sets at the same finite level remain Delta at that level.-/
theorem ProjectiveDelta.prod {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {s : Set X} {t : Set Y} (hs : ProjectiveDelta n s)
    (ht : ProjectiveDelta n t) : ProjectiveDelta n (s ×ˢ t) :=
  ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩

/-- A vertical section of a product has exactly the conjunction of factor memberships. This is
oriented only from section to membership form, so simplification cannot loop.-/
@[simp]
theorem verticalSection_prod {X : Type u} {Y : Type v}
    (s : Set X) (t : Set Y) (x : X) :
    verticalSection (s ×ˢ t) x = {y | x ∈ s ∧ y ∈ t} :=
  rfl

/-- A horizontal section of a product has exactly the conjunction of factor memberships. This is
oriented only from section to membership form, so simplification cannot loop.-/
@[simp]
theorem horizontalSection_prod {X : Type u} {Y : Type v}
    (s : Set X) (t : Set Y) (y : Y) :
    horizontalSection (s ×ˢ t) y = {x | x ∈ s ∧ y ∈ t} :=
  rfl

/-- Every Sigma set at level `n` belongs to Pi at the next level.-/
theorem ProjectiveSigma.toProjectivePi_succ {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : ProjectiveSigma n s) :
    ProjectivePi (n + 1) s := by
  have hR : ProjectiveSigma n (Set.univ ×ˢ s : Set (ProjectiveWitness × X)) :=
    ProjectiveSigma.univ.prod hs
  have huniv : DescriptiveSetTheory.projectiveUniversal
      (Set.univ ×ˢ s : Set (ProjectiveWitness × X)) = s := by
    ext x
    simp
  simpa only [huniv] using hR.projectiveUniversal

/-- Every Pi set at level `n` belongs to Sigma at the next level.-/
theorem ProjectivePi.toProjectiveSigma_succ {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : ProjectivePi n s) :
    ProjectiveSigma (n + 1) s := by
  have hR : ProjectivePi n (Set.univ ×ˢ s : Set (ProjectiveWitness × X)) :=
    ProjectivePi.univ.prod hs
  have hproj : DescriptiveSetTheory.projectiveProjection
      (Set.univ ×ˢ s : Set (ProjectiveWitness × X)) = s := by
    ext x
    simp
  simpa only [hproj] using hR.projectiveProjection

/-- Every Sigma set belongs to Delta one level higher.-/
theorem ProjectiveSigma.toProjectiveDelta_succ {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : ProjectiveSigma n s) :
    ProjectiveDelta (n + 1) s :=
  ⟨hs.mono_succ, hs.toProjectivePi_succ⟩

/-- Every Pi set belongs to Delta one level higher.-/
theorem ProjectivePi.toProjectiveDelta_succ {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : ProjectivePi n s) :
    ProjectiveDelta (n + 1) s :=
  ⟨hs.toProjectiveSigma_succ, hs.mono_succ⟩

/-- Every Borel set belongs to every finite Sigma level, including the explicit level zero.-/
theorem _root_.MeasurableSet.projectiveSigma {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : MeasurableSet s) : ProjectiveSigma n s :=
  (projectiveSigma_zero.mpr hs).mono (Nat.zero_le n)

/-- Every Borel set belongs to every finite Pi level, including the explicit level zero.-/
theorem _root_.MeasurableSet.projectivePi {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : MeasurableSet s) : ProjectivePi n s :=
  (projectivePi_zero.mpr hs).mono (Nat.zero_le n)

/-- Every Borel set belongs to every finite Delta level, including the explicit level zero.-/
theorem _root_.MeasurableSet.projectiveDelta {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : MeasurableSet s) : ProjectiveDelta n s :=
  ⟨hs.projectiveSigma, hs.projectivePi⟩

/-- Every analytic set belongs to every Sigma level at or above level one.-/
theorem _root_.MeasureTheory.AnalyticSet.projectiveSigma {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : MeasureTheory.AnalyticSet s) (hn : 1 ≤ n) :
    ProjectiveSigma n s :=
  hs.projectiveSigma_one.mono hn

/-- Every coanalytic set belongs to every Pi level at or above level one.-/
theorem IsCoanalytic.projectivePi {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : IsCoanalytic s) (hn : 1 ≤ n) :
    ProjectivePi n s :=
  hs.projectivePi_one.mono hn

/-- Every analytic set belongs to every Delta level at or above level two.-/
theorem _root_.MeasureTheory.AnalyticSet.projectiveDelta {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : MeasureTheory.AnalyticSet s) (hn : 2 ≤ n) :
    ProjectiveDelta n s :=
  hs.projectiveSigma_one.toProjectiveDelta_succ.mono hn

/-- Every coanalytic set belongs to every Delta level at or above level two.-/
theorem IsCoanalytic.projectiveDelta {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : IsCoanalytic s) (hn : 2 ≤ n) :
    ProjectiveDelta n s :=
  hs.projectivePi_one.toProjectiveDelta_succ.mono hn

end DescriptiveSetTheory
