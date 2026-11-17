/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Projective.LevelOne
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Relations.Sections
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Spaces.BairePacking

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Operations on finite projective levels

Finite boldface projective levels are closed under continuous preimages. Existential projection
sends `ProjectivePi n` to `ProjectiveSigma (n + 1)`, while universal projection gives the dual
rule. At every positive level, the matching projection preserves its polarity and level by packing
two Baire witnesses into one.

Sections, coordinate swaps, and homeomorphism images are exposed as direct consumers of continuous
preimage closure. Complement theorems use the polarity convention frozen in `Projective.Basic`.
-/

open Set

universe u v

namespace DescriptiveSetTheory

private def projectivePreimageMap {X : Type u} {Y : Type v} (f : X → Y) :
    ProjectiveWitness × X → ProjectiveWitness × Y :=
  fun q => (q.1, f q.2)

private theorem continuous_projectivePreimageMap {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous (projectivePreimageMap f) :=
  continuous_fst.prodMk (hf.comp continuous_snd)

/-- Every finite projective Sigma level is closed under continuous preimages.-/
theorem ProjectiveSigma.preimage {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {s : Set Y} (hs : ProjectiveSigma n s) {f : X → Y}
    (hf : Continuous f) : ProjectiveSigma n (f ⁻¹' s) := by
  induction n generalizing X Y with
  | zero =>
      exact MeasurableSet.preimage hs hf.measurable
  | succ n ih =>
      rcases projectiveSigma_succ.mp hs with ⟨R, hR, rfl⟩
      refine projectiveSigma_succ.mpr
        ⟨projectivePreimageMap f ⁻¹' R, ?_, ?_⟩
      · rw [ProjectivePi] at hR ⊢
        simpa only [preimage_compl] using
          ih hR (continuous_projectivePreimageMap hf)
      · ext x
        simp [projectivePreimageMap]

/-- Every finite projective Pi level is closed under continuous preimages.-/
theorem ProjectivePi.preimage {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {s : Set Y} (hs : ProjectivePi n s) {f : X → Y}
    (hf : Continuous f) : ProjectivePi n (f ⁻¹' s) := by
  rw [ProjectivePi] at hs ⊢
  simpa only [preimage_compl] using hs.preimage hf

/-- Every finite projective Delta level is closed under continuous preimages.-/
theorem ProjectiveDelta.preimage {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {s : Set Y} (hs : ProjectiveDelta n s) {f : X → Y}
    (hf : Continuous f) : ProjectiveDelta n (f ⁻¹' s) :=
  ⟨hs.1.preimage hf, hs.2.preimage hf⟩

/-- Complementing a Sigma set changes its polarity to Pi at the same level.-/
theorem ProjectiveSigma.compl {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : ProjectiveSigma n s) :
    ProjectivePi n sᶜ :=
  projectivePi_compl_iff_sigma.mpr hs

/-- Complementing a Pi set changes its polarity to Sigma at the same level.-/
theorem ProjectivePi.compl {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : ProjectivePi n s) :
    ProjectiveSigma n sᶜ :=
  hs

/-- Projective Delta is closed under complements at every finite level.-/
theorem ProjectiveDelta.compl {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : ProjectiveDelta n s) :
    ProjectiveDelta n sᶜ :=
  ⟨hs.2, hs.1.compl⟩

private def unpackProjectiveWitnessMap {X : Type u} :
    ProjectiveWitness × X → ProjectiveWitness × (ProjectiveWitness × X) :=
  fun q => ((unpackBairePair q.1).1, ((unpackBairePair q.1).2, q.2))

private theorem continuous_unpackProjectiveWitnessMap {X : Type u} [TopologicalSpace X] :
    Continuous (unpackProjectiveWitnessMap (X := X)) :=
  ((continuous_unpackBairePair.comp continuous_fst).fst).prodMk
    ((continuous_unpackBairePair.comp continuous_fst).snd.prodMk continuous_snd)

private theorem projectiveProjection_preimage_unpackProjectiveWitnessMap
    {X : Type u} (R : Set (ProjectiveWitness × (ProjectiveWitness × X))) :
    projectiveProjection (unpackProjectiveWitnessMap ⁻¹' R) =
      projectiveProjection (projectiveProjection R) := by
  ext x
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨(unpackBairePair r).2, (unpackBairePair r).1, hr⟩
  · rintro ⟨q, p, hp⟩
    refine ⟨packBairePair (p, q), ?_⟩
    simpa [unpackProjectiveWitnessMap] using hp

/-- Projecting a Pi-level relation existentially raises it to the next Sigma level.-/
theorem ProjectivePi.projectiveProjection {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {R : Set (ProjectiveWitness × X)} (hR : ProjectivePi n R) :
    ProjectiveSigma (n + 1) (projectiveProjection R) :=
  projectiveSigma_succ.mpr ⟨R, hR, rfl⟩

/-- Universally projecting a Sigma-level relation raises it to the next Pi level.-/
theorem ProjectiveSigma.projectiveUniversal {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {R : Set (ProjectiveWitness × X)} (hR : ProjectiveSigma n R) :
    ProjectivePi (n + 1) (projectiveUniversal R) :=
  projectivePi_succ.mpr ⟨R, hR, rfl⟩

/-- At a positive Sigma level, another existential projection stays at the same level.-/
theorem ProjectiveSigma.projectiveProjection {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {R : Set (ProjectiveWitness × X)} (hR : ProjectiveSigma (n + 1) R) :
    ProjectiveSigma (n + 1) (projectiveProjection R) := by
  rcases projectiveSigma_succ.mp hR with ⟨S, hS, hproj⟩
  refine projectiveSigma_succ.mpr
    ⟨unpackProjectiveWitnessMap ⁻¹' S,
      hS.preimage continuous_unpackProjectiveWitnessMap, ?_⟩
  rw [projectiveProjection_preimage_unpackProjectiveWitnessMap, hproj]

/-- At a positive Pi level, another universal projection stays at the same level.-/
theorem ProjectivePi.projectiveUniversal {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {R : Set (ProjectiveWitness × X)} (hR : ProjectivePi (n + 1) R) :
    ProjectivePi (n + 1) (projectiveUniversal R) := by
  rw [ProjectivePi] at hR ⊢
  rw [projectiveUniversal_eq_compl_projection_compl]
  simpa using hR.projectiveProjection

/-- A vertical section of a projective Sigma relation stays at the same level.-/
theorem ProjectiveSigma.verticalSection {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {R : Set (X × Y)} (hR : ProjectiveSigma n R) (x : X) :
    ProjectiveSigma n (verticalSection R x) :=
  hR.preimage (continuous_const.prodMk continuous_id)

/-- A vertical section of a projective Pi relation stays at the same level.-/
theorem ProjectivePi.verticalSection {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {R : Set (X × Y)} (hR : ProjectivePi n R) (x : X) :
    ProjectivePi n (verticalSection R x) :=
  hR.preimage (continuous_const.prodMk continuous_id)

/-- A vertical section of a projective Delta relation stays at the same level.-/
theorem ProjectiveDelta.verticalSection {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {R : Set (X × Y)} (hR : ProjectiveDelta n R) (x : X) :
    ProjectiveDelta n (verticalSection R x) :=
  hR.preimage (continuous_const.prodMk continuous_id)

/-- A horizontal section of a projective Sigma relation stays at the same level.-/
theorem ProjectiveSigma.horizontalSection {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {R : Set (X × Y)} (hR : ProjectiveSigma n R) (y : Y) :
    ProjectiveSigma n (horizontalSection R y) :=
  hR.preimage (continuous_id.prodMk continuous_const)

/-- A horizontal section of a projective Pi relation stays at the same level.-/
theorem ProjectivePi.horizontalSection {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {R : Set (X × Y)} (hR : ProjectivePi n R) (y : Y) :
    ProjectivePi n (horizontalSection R y) :=
  hR.preimage (continuous_id.prodMk continuous_const)

/-- A horizontal section of a projective Delta relation stays at the same level.-/
theorem ProjectiveDelta.horizontalSection {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {R : Set (X × Y)} (hR : ProjectiveDelta n R) (y : Y) :
    ProjectiveDelta n (horizontalSection R y) :=
  hR.preimage (continuous_id.prodMk continuous_const)

/-- Swapping relation coordinates preserves every projective Sigma level.-/
theorem ProjectiveSigma.swapRelation {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {R : Set (X × Y)} (hR : ProjectiveSigma n R) :
    ProjectiveSigma n (swapRelation R) := by
  have heq : DescriptiveSetTheory.swapRelation R = Prod.swap ⁻¹' R := by ext; rfl
  rw [heq]
  exact hR.preimage continuous_swap

/-- Swapping relation coordinates preserves every projective Pi level.-/
theorem ProjectivePi.swapRelation {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {R : Set (X × Y)} (hR : ProjectivePi n R) :
    ProjectivePi n (swapRelation R) := by
  have heq : DescriptiveSetTheory.swapRelation R = Prod.swap ⁻¹' R := by ext; rfl
  rw [heq]
  exact hR.preimage continuous_swap

/-- Swapping relation coordinates preserves every projective Delta level.-/
theorem ProjectiveDelta.swapRelation {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {R : Set (X × Y)} (hR : ProjectiveDelta n R) :
    ProjectiveDelta n (swapRelation R) := by
  have heq : DescriptiveSetTheory.swapRelation R = Prod.swap ⁻¹' R := by ext; rfl
  rw [heq]
  exact hR.preimage continuous_swap

/-- A homeomorphism image preserves projective Sigma membership.-/
theorem ProjectiveSigma.image_homeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {s : Set X} (hs : ProjectiveSigma n s) (e : X ≃ₜ Y) :
    ProjectiveSigma n (e '' s) := by
  rw [e.image_eq_preimage_symm]
  exact hs.preimage e.symm.continuous

/-- A homeomorphism image belongs to Sigma exactly when the original set does.-/
theorem projectiveSigma_image_homeomorph_iff {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {s : Set X} (e : X ≃ₜ Y) :
    ProjectiveSigma n (e '' s) ↔ ProjectiveSigma n s := by
  constructor
  · intro hs
    simpa using hs.preimage e.continuous
  · intro hs
    exact hs.image_homeomorph e

/-- A homeomorphism image preserves projective Pi membership.-/
theorem ProjectivePi.image_homeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {s : Set X} (hs : ProjectivePi n s) (e : X ≃ₜ Y) :
    ProjectivePi n (e '' s) := by
  rw [e.image_eq_preimage_symm]
  exact hs.preimage e.symm.continuous

/-- A homeomorphism image belongs to Pi exactly when the original set does.-/
theorem projectivePi_image_homeomorph_iff {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {s : Set X} (e : X ≃ₜ Y) :
    ProjectivePi n (e '' s) ↔ ProjectivePi n s := by
  constructor
  · intro hs
    simpa using hs.preimage e.continuous
  · intro hs
    exact hs.image_homeomorph e

/-- A homeomorphism image preserves projective Delta membership.-/
theorem ProjectiveDelta.image_homeomorph {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {s : Set X} (hs : ProjectiveDelta n s) (e : X ≃ₜ Y) :
    ProjectiveDelta n (e '' s) := by
  rw [e.image_eq_preimage_symm]
  exact hs.preimage e.symm.continuous

/-- A homeomorphism image belongs to Delta exactly when the original set does.-/
theorem projectiveDelta_image_homeomorph_iff {X : Type u} {Y : Type v}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {n : ℕ} {s : Set X} (e : X ≃ₜ Y) :
    ProjectiveDelta n (e '' s) ↔ ProjectiveDelta n s := by
  constructor
  · intro hs
    simpa using hs.preimage e.continuous
  · intro hs
    exact hs.image_homeomorph e

end DescriptiveSetTheory
