/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Reductions.AnalyticComplete
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.Projective

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strictness and complete sets at every positive finite projective level

Diagonalizing the universal Sigma relation at one fixed positive level produces a Pi set outside
Sigma. Its complement gives the dual Sigma set outside Pi. Packing each universal relation into
one Baire coordinate produces continuously complete witnesses for both polarities.

All results are boldface, finite-level statements. They imply neither projective determinacy nor
regularity beyond the pointclasses already established in this library.
-/

open Set

namespace DescriptiveSetTheory

/-- The Pi-side diagonal witness at projective level `n`.-/
def baireProjectivePiNotSigma (n : ℕ) : Set ProjectiveWitness :=
  baireAnalyticDiagonalMap ⁻¹' baireUniversalProjectivePi n

/-- The complement-dual Sigma-side diagonal witness at projective level `n`.-/
def baireProjectiveSigmaNotPi (n : ℕ) : Set ProjectiveWitness :=
  (baireProjectivePiNotSigma n)ᶜ

/-- Membership in the Pi diagonal means failure of self-membership in the Sigma universal.-/
@[simp]
theorem mem_baireProjectivePiNotSigma {n : ℕ} {p : ProjectiveWitness} :
    p ∈ baireProjectivePiNotSigma n ↔
      (p, p) ∉ baireUniversalProjectiveSigma n :=
  Iff.rfl

/-- Membership in the Sigma diagonal means self-membership in the Sigma universal.-/
@[simp]
theorem mem_baireProjectiveSigmaNotPi {n : ℕ} {p : ProjectiveWitness} :
    p ∈ baireProjectiveSigmaNotPi n ↔
      (p, p) ∈ baireUniversalProjectiveSigma n := by
  simp [baireProjectiveSigmaNotPi]

/-- The Pi diagonal witness has the advertised complexity at every positive finite level.-/
theorem projectivePi_baireProjectivePiNotSigma (n : ℕ) :
    ProjectivePi (n + 1) (baireProjectivePiNotSigma (n + 1)) :=
  (projectivePi_baireUniversalProjectivePi n).preimage
    continuous_baireAnalyticDiagonalMap

/-- Diagonalization keeps the Pi witness outside Sigma at the same positive finite level.-/
theorem not_projectiveSigma_baireProjectivePiNotSigma (n : ℕ) :
    ¬ ProjectiveSigma (n + 1) (baireProjectivePiNotSigma (n + 1)) := by
  intro hdiagonal
  obtain ⟨p, hp⟩ :=
    exists_verticalSection_baireUniversalProjectiveSigma n hdiagonal
  have hself := Set.ext_iff.mp hp p
  simp only [verticalSection, mem_baireProjectivePiNotSigma, mem_ofPred_eq] at hself
  tauto

/-- The dual Sigma witness has the advertised complexity at every positive finite level.-/
theorem projectiveSigma_baireProjectiveSigmaNotPi (n : ℕ) :
    ProjectiveSigma (n + 1) (baireProjectiveSigmaNotPi (n + 1)) :=
  (projectivePi_baireProjectivePiNotSigma n).compl

/-- The dual Sigma witness stays outside Pi at the same positive finite level.-/
theorem not_projectivePi_baireProjectiveSigmaNotPi (n : ℕ) :
    ¬ ProjectivePi (n + 1) (baireProjectiveSigmaNotPi (n + 1)) := by
  intro hPi
  apply not_projectiveSigma_baireProjectivePiNotSigma n
  simpa [ProjectivePi, baireProjectiveSigmaNotPi] using hPi

/-- Every positive finite Pi pointclass has an explicit counterexample to Sigma membership.-/
theorem exists_projectivePi_not_projectiveSigma_baire (n : ℕ) :
    ∃ s : Set ProjectiveWitness,
      ProjectivePi (n + 1) s ∧ ¬ ProjectiveSigma (n + 1) s :=
  ⟨baireProjectivePiNotSigma (n + 1),
    projectivePi_baireProjectivePiNotSigma n,
    not_projectiveSigma_baireProjectivePiNotSigma n⟩

/-- Every positive finite Sigma pointclass has an explicit counterexample to Pi membership.-/
theorem exists_projectiveSigma_not_projectivePi_baire (n : ℕ) :
    ∃ s : Set ProjectiveWitness,
      ProjectiveSigma (n + 1) s ∧ ¬ ProjectivePi (n + 1) s :=
  ⟨baireProjectiveSigmaNotPi (n + 1),
    projectiveSigma_baireProjectiveSigmaNotPi n,
    not_projectivePi_baireProjectiveSigmaNotPi n⟩

/-- A Baire set is Sigma-complete at level `n` when it has that complexity and every Baire set in
the same pointclass continuously reduces to it.-/
def IsProjectiveSigmaComplete (n : ℕ) (t : Set ProjectiveWitness) : Prop :=
  ProjectiveSigma n t ∧
    ∀ s : Set ProjectiveWitness, ProjectiveSigma n s → ContinuouslyReduces s t

/-- The complement-dual notion of Pi completeness on Baire space.-/
def IsProjectivePiComplete (n : ℕ) (t : Set ProjectiveWitness) : Prop :=
  ProjectivePi n t ∧
    ∀ s : Set ProjectiveWitness, ProjectivePi n s → ContinuouslyReduces s t

/-- Apply Sigma completeness without unfolding its conjunction.-/
theorem IsProjectiveSigmaComplete.continuouslyReduces {n : ℕ}
    {s t : Set ProjectiveWitness} (ht : IsProjectiveSigmaComplete n t)
    (hs : ProjectiveSigma n s) : ContinuouslyReduces s t :=
  ht.2 s hs

/-- Apply Pi completeness without unfolding its conjunction.-/
theorem IsProjectivePiComplete.continuouslyReduces {n : ℕ}
    {s t : Set ProjectiveWitness} (ht : IsProjectivePiComplete n t)
    (hs : ProjectivePi n s) : ContinuouslyReduces s t :=
  ht.2 s hs

/-- Pack the level-`n` Sigma universal relation into one Baire coordinate.-/
def projectiveSigmaCompleteSet (n : ℕ) : Set ProjectiveWitness :=
  unpackBairePair ⁻¹' baireUniversalProjectiveSigma n

/-- Pack the level-`n` Pi universal relation into one Baire coordinate.-/
def projectivePiCompleteSet (n : ℕ) : Set ProjectiveWitness :=
  unpackBairePair ⁻¹' baireUniversalProjectivePi n

/-- The two packed candidates are exact complements at every level.-/
theorem projectivePiCompleteSet_eq_compl (n : ℕ) :
    projectivePiCompleteSet n = (projectiveSigmaCompleteSet n)ᶜ := by
  rw [projectivePiCompleteSet, projectiveSigmaCompleteSet,
    baireUniversalProjectivePi, preimage_compl]

/-- The packed Sigma universal has the advertised positive-level complexity.-/
theorem projectiveSigma_projectiveSigmaCompleteSet (n : ℕ) :
    ProjectiveSigma (n + 1) (projectiveSigmaCompleteSet (n + 1)) :=
  (projectiveSigma_baireUniversalProjectiveSigma n).preimage continuous_unpackBairePair

/-- The packed Pi universal has the advertised positive-level complexity.-/
theorem projectivePi_projectivePiCompleteSet (n : ℕ) :
    ProjectivePi (n + 1) (projectivePiCompleteSet (n + 1)) :=
  (projectivePi_baireUniversalProjectivePi n).preimage continuous_unpackBairePair

/-- Pair packing reduces the total Sigma universal relation to its one-coordinate copy.-/
theorem continuouslyReduces_baireUniversalProjectiveSigma_completeSet (n : ℕ) :
    ContinuouslyReduces (baireUniversalProjectiveSigma n)
      (projectiveSigmaCompleteSet n) := by
  refine ⟨packBairePair, continuous_packBairePair, ?_⟩
  ext z
  simp [projectiveSigmaCompleteSet]

/-- Pair packing reduces the total Pi universal relation to its one-coordinate copy.-/
theorem continuouslyReduces_baireUniversalProjectivePi_completeSet (n : ℕ) :
    ContinuouslyReduces (baireUniversalProjectivePi n)
      (projectivePiCompleteSet n) := by
  refine ⟨packBairePair, continuous_packBairePair, ?_⟩
  ext z
  simp [projectivePiCompleteSet]

/-- The packed Sigma universal is complete at every positive finite projective level.-/
theorem isProjectiveSigmaComplete_projectiveSigmaCompleteSet (n : ℕ) :
    IsProjectiveSigmaComplete (n + 1) (projectiveSigmaCompleteSet (n + 1)) := by
  refine ⟨projectiveSigma_projectiveSigmaCompleteSet n, fun s hs => ?_⟩
  exact (isUniversalFor_baireUniversalProjectiveSigma n).continuouslyReduces hs |>.trans
    (continuouslyReduces_baireUniversalProjectiveSigma_completeSet (n + 1))

/-- The packed Pi universal is complete at every positive finite projective level.-/
theorem isProjectivePiComplete_projectivePiCompleteSet (n : ℕ) :
    IsProjectivePiComplete (n + 1) (projectivePiCompleteSet (n + 1)) := by
  refine ⟨projectivePi_projectivePiCompleteSet n, fun s hs => ?_⟩
  exact (isUniversalFor_baireUniversalProjectivePi n).continuouslyReduces hs |>.trans
    (continuouslyReduces_baireUniversalProjectivePi_completeSet (n + 1))

/-- Sigma completeness is proper at every positive finite level.-/
theorem not_projectivePi_projectiveSigmaCompleteSet (n : ℕ) :
    ¬ ProjectivePi (n + 1) (projectiveSigmaCompleteSet (n + 1)) := by
  intro hPi
  obtain ⟨f, hf, hpre⟩ :=
    (isProjectiveSigmaComplete_projectiveSigmaCompleteSet n).continuouslyReduces
      (projectiveSigma_baireProjectiveSigmaNotPi n)
  apply not_projectivePi_baireProjectiveSigmaNotPi n
  have hsource := hPi.preimage hf
  rw [hpre] at hsource
  exact hsource

/-- Pi completeness is proper at every positive finite level.-/
theorem not_projectiveSigma_projectivePiCompleteSet (n : ℕ) :
    ¬ ProjectiveSigma (n + 1) (projectivePiCompleteSet (n + 1)) := by
  intro hSigma
  obtain ⟨f, hf, hpre⟩ :=
    (isProjectivePiComplete_projectivePiCompleteSet n).continuouslyReduces
      (projectivePi_baireProjectivePiNotSigma n)
  apply not_projectiveSigma_baireProjectivePiNotSigma n
  have hsource := hSigma.preimage hf
  rw [hpre] at hsource
  exact hsource

/-- The level-one Pi diagonal is exactly the released coanalytic-not-analytic witness.-/
@[simp]
theorem baireProjectivePiNotSigma_one :
    baireProjectivePiNotSigma 1 = baireCoanalyticNotAnalytic :=
  rfl

/-- The level-one Sigma diagonal is exactly the released analytic-not-coanalytic witness.-/
@[simp]
theorem baireProjectiveSigmaNotPi_one :
    baireProjectiveSigmaNotPi 1 = baireAnalyticNotCoanalytic :=
  rfl

/-- The level-one packed Sigma universal is exactly the released analytic-complete set.-/
@[simp]
theorem projectiveSigmaCompleteSet_one :
    projectiveSigmaCompleteSet 1 = analyticCompleteSet :=
  rfl

/-- The level-one packed Pi universal is exactly the released coanalytic-complete set.-/
@[simp]
theorem projectivePiCompleteSet_one :
    projectivePiCompleteSet 1 = coanalyticCompleteSet :=
  rfl

/-- Projective Sigma completeness at level one is exactly analytic completeness.-/
theorem isProjectiveSigmaComplete_one_iff (t : Set ProjectiveWitness) :
    IsProjectiveSigmaComplete 1 t ↔ IsAnalyticComplete t := by
  simp only [IsProjectiveSigmaComplete, IsAnalyticComplete,
    projectiveSigma_one_iff_analyticSet]

/-- Projective Pi completeness at level one is exactly coanalytic completeness.-/
theorem isProjectivePiComplete_one_iff (t : Set ProjectiveWitness) :
    IsProjectivePiComplete 1 t ↔ IsCoanalyticComplete t := by
  simp only [IsProjectivePiComplete, IsCoanalyticComplete,
    projectivePi_one_iff_isCoanalytic]

end DescriptiveSetTheory
