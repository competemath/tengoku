/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.Seed.MeasureTheory.Constructions.Polish.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite boldface projective hierarchy

This file fixes a one-based convention for the finite boldface projective hierarchy on Polish
Borel spaces. Level zero is the Borel compatibility level. At a successor, `ProjectiveSigma`
projects a `ProjectivePi` relation along one Baire-space witness, while `ProjectivePi` is the
complementary polarity. Thus positive levels correspond to the usual `Σ¹_n` and `Π¹_n` classes;
level-one coherence with analytic and coanalytic sets is proved in the next module.

The witness coordinate always comes first in a relation `(ℕ → ℕ) × X`. The recursive definition
is polymorphic in the ambient Polish space, so nesting projections never exposes a code datatype or
casts in the public API. This release covers finite boldface levels only.
-/

open Set

universe u

namespace DescriptiveSetTheory

/-- The fixed witness space used at every projective successor level.-/
abbrev ProjectiveWitness := ℕ → ℕ

variable {X : Type u}

/-- Existential projection of a relation whose first coordinate is Baire space.-/
def projectiveProjection (R : Set (ProjectiveWitness × X)) : Set X :=
  {x | ∃ p, (p, x) ∈ R}

/-- Universal projection of a relation whose first coordinate is Baire space.-/
def projectiveUniversal (R : Set (ProjectiveWitness × X)) : Set X :=
  {x | ∀ p, (p, x) ∈ R}

@[simp]
theorem mem_projectiveProjection {R : Set (ProjectiveWitness × X)} {x : X} :
    x ∈ projectiveProjection R ↔ ∃ p, (p, x) ∈ R :=
  Iff.rfl

@[simp]
theorem mem_projectiveUniversal {R : Set (ProjectiveWitness × X)} {x : X} :
    x ∈ projectiveUniversal R ↔ ∀ p, (p, x) ∈ R :=
  Iff.rfl

/-- The existential projection is the ordinary image under the second coordinate map.-/
theorem projectiveProjection_eq_image_snd (R : Set (ProjectiveWitness × X)) :
    projectiveProjection R = Prod.snd '' R := by
  ext x
  simp [projectiveProjection, eq_comm]

/-- Universal projection is the complement of the existential projection of the complement.-/
theorem projectiveUniversal_eq_compl_projection_compl
    (R : Set (ProjectiveWitness × X)) :
    projectiveUniversal R = (projectiveProjection Rᶜ)ᶜ := by
  ext x
  simp

/-- Existential projection is the complement of the universal projection of the complement.-/
theorem projectiveProjection_eq_compl_universal_compl
    (R : Set (ProjectiveWitness × X)) :
    projectiveProjection R = (projectiveUniversal Rᶜ)ᶜ := by
  rw [projectiveUniversal_eq_compl_projection_compl]
  simp

/-- The one-based finite boldface `Σ¹` hierarchy.

Level zero is Borel. A successor is the Baire-space existential projection of the complementary
polarity at the preceding level. The natural number is placed before the ambient type so the
structural recursion remains polymorphic as the ambient space changes to a product.-/
def ProjectiveSigma : (n : ℕ) → {X : Type u} → [TopologicalSpace X] → [PolishSpace X] →
    [MeasurableSpace X] → [BorelSpace X] → Set X → Prop
  | 0, _, _, _, _, _, s => MeasurableSet s
  | n + 1, X, _, _, _, _, s =>
      ∃ R : Set (ProjectiveWitness × X),
        ProjectiveSigma n Rᶜ ∧ projectiveProjection R = s

/-- The complementary `Π¹` polarity at a finite projective level.-/
def ProjectivePi [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (n : ℕ) (s : Set X) : Prop :=
  ProjectiveSigma n sᶜ

/-- The intersection `Δ¹_n = Σ¹_n ∩ Π¹_n`.-/
def ProjectiveDelta [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (n : ℕ) (s : Set X) : Prop :=
  ProjectiveSigma n s ∧ ProjectivePi n s

theorem projectiveSigma_zero [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {s : Set X} :
    ProjectiveSigma 0 s ↔ MeasurableSet s :=
  Iff.rfl

theorem projectivePi_zero [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {s : Set X} :
    ProjectivePi 0 s ↔ MeasurableSet s := by
  simp [ProjectivePi, ProjectiveSigma]

theorem projectiveDelta_zero [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {s : Set X} :
    ProjectiveDelta 0 s ↔ MeasurableSet s := by
  simp [ProjectiveDelta, projectiveSigma_zero, projectivePi_zero]

/-- The exact existential-projection equation for the `Σ¹` successor.-/
theorem projectiveSigma_succ [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {n : ℕ} {s : Set X} :
    ProjectiveSigma (n + 1) s ↔
      ∃ R : Set (ProjectiveWitness × X),
        ProjectivePi n R ∧ projectiveProjection R = s :=
  Iff.rfl

/-- The exact universal-projection equation for the `Π¹` successor.-/
theorem projectivePi_succ [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {n : ℕ} {s : Set X} :
    ProjectivePi (n + 1) s ↔
      ∃ R : Set (ProjectiveWitness × X),
        ProjectiveSigma n R ∧ projectiveUniversal R = s := by
  constructor
  · rintro ⟨R, hR, hproj⟩
    refine ⟨Rᶜ, ?_, ?_⟩
    · simpa [ProjectivePi] using hR
    · rw [projectiveUniversal_eq_compl_projection_compl]
      simpa using congrArg (fun t : Set X => tᶜ) hproj
  · rintro ⟨R, hR, huniv⟩
    refine ⟨Rᶜ, ?_, ?_⟩
    · simpa [ProjectivePi] using hR
    · rw [← compl_inj_iff, compl_compl]
      rw [← huniv, projectiveUniversal_eq_compl_projection_compl]

/-- Complement duality, in the direction used by the recursive `Σ¹` definition.-/
theorem projectiveSigma_compl_iff_pi [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {n : ℕ} {s : Set X} :
    ProjectiveSigma n sᶜ ↔ ProjectivePi n s :=
  Iff.rfl

/-- Complement duality in the opposite direction.-/
theorem projectivePi_compl_iff_sigma [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] {n : ℕ} {s : Set X} :
    ProjectivePi n sᶜ ↔ ProjectiveSigma n s := by
  simp [ProjectivePi]

theorem projectiveDelta_iff [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {n : ℕ} {s : Set X} :
    ProjectiveDelta n s ↔ ProjectiveSigma n s ∧ ProjectivePi n s :=
  Iff.rfl

/-- Projective membership depends only on the underlying set.-/
theorem projectiveSigma_congr [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {n : ℕ} {s t : Set X} (h : s = t) :
    ProjectiveSigma n s ↔ ProjectiveSigma n t := by
  subst t
  rfl

/-- Extensional congruence for the complementary projective polarity.-/
theorem projectivePi_congr [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {n : ℕ} {s t : Set X} (h : s = t) :
    ProjectivePi n s ↔ ProjectivePi n t := by
  subst t
  rfl

/-- Extensional congruence for `ProjectiveDelta`.-/
theorem projectiveDelta_congr [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] {n : ℕ} {s t : Set X} (h : s = t) :
    ProjectiveDelta n s ↔ ProjectiveDelta n t := by
  subst t
  rfl

end DescriptiveSetTheory
