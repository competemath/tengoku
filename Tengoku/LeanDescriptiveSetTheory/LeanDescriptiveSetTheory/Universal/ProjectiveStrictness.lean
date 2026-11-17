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

/-- Membership in the Pi diagonal means failure of self-membership in the Sigma universal.
@isnad1 id=iff.0h2v.s5.76b2684832c5 from=translated src=- shape=3a948f16 vocab=f6ad25a2
-/
@[simp]
theorem mem_baireProjectivePiNotSigma {n : ℕ} {p : ProjectiveWitness} :
    p ∈ baireProjectivePiNotSigma n ↔
      (p, p) ∉ baireUniversalProjectiveSigma n :=
  Iff.rfl

/-- Membership in the Sigma diagonal means self-membership in the Sigma universal.
@isnad1 id=iff.0h2v.s5.f85423e622fa from=translated src=- shape=92c0ebcc vocab=adad33e6
-/
@[simp]
theorem mem_baireProjectiveSigmaNotPi {n : ℕ} {p : ProjectiveWitness} :
    p ∈ baireProjectiveSigmaNotPi n ↔
      (p, p) ∈ baireUniversalProjectiveSigma n := by
  simp [baireProjectiveSigmaNotPi]

/-- The Pi diagonal witness has the advertised complexity at every positive finite level.
@isnad1 id=projecti.0h1v.s5.2ffb47d666e8 from=translated src=- shape=f8baf4fe vocab=16afc97b
-/
theorem projectivePi_baireProjectivePiNotSigma (n : ℕ) :
    ProjectivePi (n + 1) (baireProjectivePiNotSigma (n + 1)) :=
  (projectivePi_baireUniversalProjectivePi n).preimage
    continuous_baireAnalyticDiagonalMap

/-- Diagonalization keeps the Pi witness outside Sigma at the same positive finite level.
@isnad1 id=not.0h1v.s5.b956d826c9bf from=translated src=- shape=0be1943c vocab=806a1478
-/
theorem not_projectiveSigma_baireProjectivePiNotSigma (n : ℕ) :
    ¬ ProjectiveSigma (n + 1) (baireProjectivePiNotSigma (n + 1)) := by
  intro hdiagonal
  obtain ⟨p, hp⟩ :=
    exists_verticalSection_baireUniversalProjectiveSigma n hdiagonal
  have hself := Set.ext_iff.mp hp p
  simp only [verticalSection, mem_baireProjectivePiNotSigma, mem_ofPred_eq] at hself
  tauto

/-- The dual Sigma witness has the advertised complexity at every positive finite level.
@isnad1 id=projecti.0h1v.s5.dde49f6a8b6a from=translated src=- shape=ea8aae19 vocab=d8fbac55
-/
theorem projectiveSigma_baireProjectiveSigmaNotPi (n : ℕ) :
    ProjectiveSigma (n + 1) (baireProjectiveSigmaNotPi (n + 1)) :=
  (projectivePi_baireProjectivePiNotSigma n).compl

/-- The dual Sigma witness stays outside Pi at the same positive finite level.
@isnad1 id=not.0h1v.s5.4d3138ee3d90 from=translated src=- shape=1d44aada vocab=8b6e706e
-/
theorem not_projectivePi_baireProjectiveSigmaNotPi (n : ℕ) :
    ¬ ProjectivePi (n + 1) (baireProjectiveSigmaNotPi (n + 1)) := by
  intro hPi
  apply not_projectiveSigma_baireProjectivePiNotSigma n
  simpa [ProjectivePi, baireProjectiveSigmaNotPi] using hPi

/-- Every positive finite Pi pointclass has an explicit counterexample to Sigma membership.
@isnad1 id=ex.0h1v.s6.2aa41759a024 from=translated src=- shape=a2c8ddc5 vocab=ed7444c9
-/
theorem exists_projectivePi_not_projectiveSigma_baire (n : ℕ) :
    ∃ s : Set ProjectiveWitness,
      ProjectivePi (n + 1) s ∧ ¬ ProjectiveSigma (n + 1) s :=
  ⟨baireProjectivePiNotSigma (n + 1),
    projectivePi_baireProjectivePiNotSigma n,
    not_projectiveSigma_baireProjectivePiNotSigma n⟩

/-- Every positive finite Sigma pointclass has an explicit counterexample to Pi membership.
@isnad1 id=ex.0h1v.s6.630cb679aa31 from=translated src=- shape=c116ea30 vocab=ed7444c9
-/
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

/-- Apply Sigma completeness without unfolding its conjunction.
@isnad1 id=continuo.2h3v.s5.bfabd54460bc from=translated src=- shape=41441964 vocab=82e202d8
-/
theorem IsProjectiveSigmaComplete.continuouslyReduces {n : ℕ}
    {s t : Set ProjectiveWitness} (ht : IsProjectiveSigmaComplete n t)
    (hs : ProjectiveSigma n s) : ContinuouslyReduces s t :=
  ht.2 s hs

/-- Apply Pi completeness without unfolding its conjunction.
@isnad1 id=continuo.2h3v.s5.359185c546d7 from=translated src=- shape=c8264536 vocab=288d4ffd
-/
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

/-- The two packed candidates are exact complements at every level.
@isnad1 id=eq.0h1v.s3.88565e1308fb from=translated src=- shape=37c1f0ee vocab=aba1b6c0
-/
theorem projectivePiCompleteSet_eq_compl (n : ℕ) :
    projectivePiCompleteSet n = (projectiveSigmaCompleteSet n)ᶜ := by
  rw [projectivePiCompleteSet, projectiveSigmaCompleteSet,
    baireUniversalProjectivePi, preimage_compl]

/-- The packed Sigma universal has the advertised positive-level complexity.
@isnad1 id=projecti.0h1v.s5.1b2c1a6eb19a from=translated src=- shape=ea8aae19 vocab=4ce3e3fe
-/
theorem projectiveSigma_projectiveSigmaCompleteSet (n : ℕ) :
    ProjectiveSigma (n + 1) (projectiveSigmaCompleteSet (n + 1)) :=
  (projectiveSigma_baireUniversalProjectiveSigma n).preimage continuous_unpackBairePair

/-- The packed Pi universal has the advertised positive-level complexity.
@isnad1 id=projecti.0h1v.s5.d67b04f5dea6 from=translated src=- shape=f8baf4fe vocab=3744523a
-/
theorem projectivePi_projectivePiCompleteSet (n : ℕ) :
    ProjectivePi (n + 1) (projectivePiCompleteSet (n + 1)) :=
  (projectivePi_baireUniversalProjectivePi n).preimage continuous_unpackBairePair

/-- Pair packing reduces the total Sigma universal relation to its one-coordinate copy.
@isnad1 id=continuo.0h1v.s5.e6868dc202b3 from=translated src=- shape=a1712f4e vocab=7d521d76
-/
theorem continuouslyReduces_baireUniversalProjectiveSigma_completeSet (n : ℕ) :
    ContinuouslyReduces (baireUniversalProjectiveSigma n)
      (projectiveSigmaCompleteSet n) := by
  refine ⟨packBairePair, continuous_packBairePair, ?_⟩
  ext z
  simp [projectiveSigmaCompleteSet]

/-- Pair packing reduces the total Pi universal relation to its one-coordinate copy.
@isnad1 id=continuo.0h1v.s5.45402dd4ca6d from=translated src=- shape=a1712f4e vocab=6444de18
-/
theorem continuouslyReduces_baireUniversalProjectivePi_completeSet (n : ℕ) :
    ContinuouslyReduces (baireUniversalProjectivePi n)
      (projectivePiCompleteSet n) := by
  refine ⟨packBairePair, continuous_packBairePair, ?_⟩
  ext z
  simp [projectivePiCompleteSet]

/-- The packed Sigma universal is complete at every positive finite projective level.
@isnad1 id=isprojec.0h1v.s4.01c75bfbbe6d from=translated src=- shape=a7dc3ea5 vocab=59f4f5d9
-/
theorem isProjectiveSigmaComplete_projectiveSigmaCompleteSet (n : ℕ) :
    IsProjectiveSigmaComplete (n + 1) (projectiveSigmaCompleteSet (n + 1)) := by
  refine ⟨projectiveSigma_projectiveSigmaCompleteSet n, fun s hs => ?_⟩
  exact (isUniversalFor_baireUniversalProjectiveSigma n).continuouslyReduces hs |>.trans
    (continuouslyReduces_baireUniversalProjectiveSigma_completeSet (n + 1))

/-- The packed Pi universal is complete at every positive finite projective level.
@isnad1 id=isprojec.0h1v.s4.8d4d4a32911a from=translated src=- shape=a7dc3ea5 vocab=73917db7
-/
theorem isProjectivePiComplete_projectivePiCompleteSet (n : ℕ) :
    IsProjectivePiComplete (n + 1) (projectivePiCompleteSet (n + 1)) := by
  refine ⟨projectivePi_projectivePiCompleteSet n, fun s hs => ?_⟩
  exact (isUniversalFor_baireUniversalProjectivePi n).continuouslyReduces hs |>.trans
    (continuouslyReduces_baireUniversalProjectivePi_completeSet (n + 1))

/-- Sigma completeness is proper at every positive finite level.
@isnad1 id=not.0h1v.s5.7cd57771a3c1 from=translated src=- shape=1d44aada vocab=b8cce365
-/
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

/-- Pi completeness is proper at every positive finite level.
@isnad1 id=not.0h1v.s5.6120fffacc51 from=translated src=- shape=0be1943c vocab=56c8f03f
-/
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

/-- The level-one Pi diagonal is exactly the released coanalytic-not-analytic witness.
@isnad1 id=eq.0h0v.s3.e0dfdfd465c1 from=translated src=- shape=52b49c84 vocab=b3e8590f
-/
@[simp]
theorem baireProjectivePiNotSigma_one :
    baireProjectivePiNotSigma 1 = baireCoanalyticNotAnalytic :=
  rfl

/-- The level-one Sigma diagonal is exactly the released analytic-not-coanalytic witness.
@isnad1 id=eq.0h0v.s3.6550bf183e5e from=translated src=- shape=52b49c84 vocab=c2b27896
-/
@[simp]
theorem baireProjectiveSigmaNotPi_one :
    baireProjectiveSigmaNotPi 1 = baireAnalyticNotCoanalytic :=
  rfl

/-- The level-one packed Sigma universal is exactly the released analytic-complete set.
@isnad1 id=eq.0h0v.s3.79f5051c7018 from=translated src=- shape=52b49c84 vocab=9958cf91
-/
@[simp]
theorem projectiveSigmaCompleteSet_one :
    projectiveSigmaCompleteSet 1 = analyticCompleteSet :=
  rfl

/-- The level-one packed Pi universal is exactly the released coanalytic-complete set.
@isnad1 id=eq.0h0v.s3.ed8994e0a8c9 from=translated src=- shape=52b49c84 vocab=42599659
-/
@[simp]
theorem projectivePiCompleteSet_one :
    projectivePiCompleteSet 1 = coanalyticCompleteSet :=
  rfl

/-- Projective Sigma completeness at level one is exactly analytic completeness.
@isnad1 id=iff.0h1v.s3.80f365f9fc6f from=translated src=- shape=2968e08c vocab=767fe8cf
-/
theorem isProjectiveSigmaComplete_one_iff (t : Set ProjectiveWitness) :
    IsProjectiveSigmaComplete 1 t ↔ IsAnalyticComplete t := by
  simp only [IsProjectiveSigmaComplete, IsAnalyticComplete,
    projectiveSigma_one_iff_analyticSet]

/-- Projective Pi completeness at level one is exactly coanalytic completeness.
@isnad1 id=iff.0h1v.s3.9013503ef8a1 from=translated src=- shape=2968e08c vocab=645dc94e
-/
theorem isProjectivePiComplete_one_iff (t : Set ProjectiveWitness) :
    IsProjectivePiComplete 1 t ↔ IsCoanalyticComplete t := by
  simp only [IsProjectivePiComplete, IsCoanalyticComplete,
    projectivePi_one_iff_isCoanalytic]

end DescriptiveSetTheory
