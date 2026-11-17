/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Projective.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closure and monotonicity of finite projective levels

Sigma levels are closed under countable unions and Pi levels under countable intersections. The
proof tags a countable family by the first coordinate of a Baire witness and proves preservation of
that tagged relation by induction on the projective level. Positive-level intersections use the
released Baire-pair packing to combine two witnesses.

All finite levels are monotone. The zero-to-one step uses an explicit measurable dummy-witness
relation; successor steps lift the preceding complementary relation. No strictness claim is made.
The zero level, finite Boolean operations, and finite indexed operations are stated explicitly.
-/

open Set

universe u

namespace DescriptiveSetTheory

private def projectiveTagged {X : Type u} (s : ℕ → Set X) :
    Set (ProjectiveWitness × X) :=
  {q | q.2 ∈ s (q.1 0)}

private theorem measurableSet_projectiveTagged {X : Type u}
    [MeasurableSpace X] {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i)) :
    MeasurableSet (projectiveTagged s) := by
  rw [show projectiveTagged s = ⋃ i, {p : ProjectiveWitness | p 0 = i} ×ˢ s i by
    ext q
    simp [projectiveTagged]]
  apply MeasurableSet.iUnion
  intro i
  have hp : MeasurableSet {p : ProjectiveWitness | p 0 = i} := by
    change MeasurableSet ((fun p : ProjectiveWitness => p 0) ⁻¹' {i})
    exact MeasurableSet.preimage (measurableSet_singleton i) (measurable_pi_apply 0)
  exact hp.prod (hs i)

private def taggedWitnessMap {X : Type u} :
    ProjectiveWitness × (ProjectiveWitness × X) →
      ProjectiveWitness × (ProjectiveWitness × X) :=
  fun q => (q.2.1, (q.1, q.2.2))

private theorem continuous_taggedWitnessMap {X : Type u} [TopologicalSpace X] :
    Continuous (taggedWitnessMap (X := X)) :=
  (continuous_fst.comp continuous_snd).prodMk
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd))

private theorem projectiveSigma_tagged {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : ℕ → Set X} (hs : ∀ i, ProjectiveSigma n (s i)) :
    ProjectiveSigma n (projectiveTagged s) := by
  induction n generalizing X with
  | zero =>
      exact measurableSet_projectiveTagged hs
  | succ n ih =>
      choose R hR hproj using fun i => projectiveSigma_succ.mp (hs i)
      have htaggedPi : ProjectivePi n (projectiveTagged R) := by
        rw [ProjectivePi]
        rw [show (projectiveTagged R)ᶜ = projectiveTagged (fun i => (R i)ᶜ) by
          ext q
          rfl]
        exact ih fun i => hR i
      refine projectiveSigma_succ.mpr
        ⟨taggedWitnessMap ⁻¹' projectiveTagged R,
          htaggedPi.preimage continuous_taggedWitnessMap, ?_⟩
      ext q
      change (∃ p, (p, q.2) ∈ R (q.1 0)) ↔ q.2 ∈ s (q.1 0)
      rw [← hproj (q.1 0)]
      rfl

private theorem projectiveProjection_projectiveTagged {X : Type u} (s : ℕ → Set X) :
    projectiveProjection (projectiveTagged s) = ⋃ i, s i := by
  ext x
  constructor
  · rintro ⟨p, hp⟩
    exact Set.mem_iUnion.mpr ⟨p 0, hp⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    exact ⟨fun _ => i, hi⟩

/-- Every finite projective Sigma level is closed under countable unions.
@isnad1 id=projecti.1h3v.s5.7102d99277a4 from=translated src=- shape=3cddae02 vocab=145e8929
-/
theorem ProjectiveSigma.iUnion {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : ℕ → Set X} (hs : ∀ i, ProjectiveSigma n (s i)) :
    ProjectiveSigma n (⋃ i, s i) := by
  cases n with
  | zero => exact MeasurableSet.iUnion hs
  | succ n =>
      rw [← projectiveProjection_projectiveTagged]
      exact (projectiveSigma_tagged hs).projectiveProjection

/-- Every finite projective Pi level is closed under countable intersections.
@isnad1 id=projecti.1h3v.s5.843552f41e06 from=translated src=- shape=1b2a5bc5 vocab=af73c82c
-/
theorem ProjectivePi.iInter {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : ℕ → Set X} (hs : ∀ i, ProjectivePi n (s i)) :
    ProjectivePi n (⋂ i, s i) := by
  rw [ProjectivePi]
  simpa only [compl_iInter] using
    (ProjectiveSigma.iUnion fun i => (show ProjectiveSigma n (s i)ᶜ from hs i))

/-- Projective Sigma levels are closed under binary unions.
@isnad1 id=projecti.2h4v.s5.b4bbf43cacbf from=translated src=- shape=00e288e1 vocab=fa941ae8
-/
theorem ProjectiveSigma.union {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s t : Set X} (hs : ProjectiveSigma n s) (ht : ProjectiveSigma n t) :
    ProjectiveSigma n (s ∪ t) := by
  let f : ℕ → Set X := fun i => if i = 0 then s else t
  have hf : ∀ i, ProjectiveSigma n (f i) := by
    intro i
    by_cases hi : i = 0
    · simpa [f, hi] using hs
    · simpa [f, hi] using ht
  have heq : (⋃ i, f i) = s ∪ t := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
      by_cases h0 : i = 0
      · exact Or.inl (by simpa [f, h0] using hi)
      · exact Or.inr (by simpa [f, h0] using hi)
    · rintro (hx | hx)
      · exact Set.mem_iUnion.mpr ⟨0, by simpa [f] using hx⟩
      · exact Set.mem_iUnion.mpr ⟨1, by simpa [f] using hx⟩
  rw [← heq]
  exact ProjectiveSigma.iUnion hf

/-- Projective Pi levels are closed under binary intersections.
@isnad1 id=projecti.2h4v.s5.780c67f2ec05 from=translated src=- shape=5d862f59 vocab=2835f834
-/
theorem ProjectivePi.inter {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s t : Set X} (hs : ProjectivePi n s) (ht : ProjectivePi n t) :
    ProjectivePi n (s ∩ t) := by
  rw [ProjectivePi]
  simpa only [compl_inter] using
    (show ProjectiveSigma n sᶜ from hs).union (show ProjectiveSigma n tᶜ from ht)

private def leftPackedWitnessMap {X : Type u} :
    ProjectiveWitness × X → ProjectiveWitness × X :=
  fun q => ((unpackBairePair q.1).1, q.2)

private def rightPackedWitnessMap {X : Type u} :
    ProjectiveWitness × X → ProjectiveWitness × X :=
  fun q => ((unpackBairePair q.1).2, q.2)

private theorem continuous_leftPackedWitnessMap {X : Type u} [TopologicalSpace X] :
    Continuous (leftPackedWitnessMap (X := X)) :=
  (continuous_unpackBairePair.comp continuous_fst).fst.prodMk continuous_snd

private theorem continuous_rightPackedWitnessMap {X : Type u} [TopologicalSpace X] :
    Continuous (rightPackedWitnessMap (X := X)) :=
  (continuous_unpackBairePair.comp continuous_fst).snd.prodMk continuous_snd

private theorem projectiveProjection_packedInter {X : Type u}
    (R S : Set (ProjectiveWitness × X)) :
    projectiveProjection
        (leftPackedWitnessMap ⁻¹' R ∩ rightPackedWitnessMap ⁻¹' S) =
      projectiveProjection R ∩ projectiveProjection S := by
  ext x
  constructor
  · rintro ⟨r, hr, hs⟩
    exact ⟨⟨(unpackBairePair r).1, hr⟩, ⟨(unpackBairePair r).2, hs⟩⟩
  · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    refine ⟨packBairePair (p, q), ?_⟩
    simpa [leftPackedWitnessMap, rightPackedWitnessMap] using And.intro hp hq

/-- Projective Sigma levels are closed under binary intersections.
@isnad1 id=projecti.2h4v.s5.9e31f5c5ecf1 from=translated src=- shape=00e288e1 vocab=5a7fbee2
-/
theorem ProjectiveSigma.inter {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s t : Set X} (hs : ProjectiveSigma n s) (ht : ProjectiveSigma n t) :
    ProjectiveSigma n (s ∩ t) := by
  cases n with
  | zero => exact MeasurableSet.inter hs ht
  | succ n =>
      rcases projectiveSigma_succ.mp hs with ⟨R, hR, hprojR⟩
      rcases projectiveSigma_succ.mp ht with ⟨S, hS, hprojS⟩
      refine projectiveSigma_succ.mpr
        ⟨leftPackedWitnessMap ⁻¹' R ∩ rightPackedWitnessMap ⁻¹' S,
          (hR.preimage continuous_leftPackedWitnessMap).inter
            (hS.preimage continuous_rightPackedWitnessMap), ?_⟩
      rw [projectiveProjection_packedInter, hprojR, hprojS]

/-- Projective Pi levels are closed under binary unions.
@isnad1 id=projecti.2h4v.s5.922b63156db9 from=translated src=- shape=5d862f59 vocab=9d4a6b30
-/
theorem ProjectivePi.union {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s t : Set X} (hs : ProjectivePi n s) (ht : ProjectivePi n t) :
    ProjectivePi n (s ∪ t) := by
  rw [ProjectivePi]
  simpa only [compl_union] using
    (show ProjectiveSigma n sᶜ from hs).inter (show ProjectiveSigma n tᶜ from ht)

/-- Projective Delta levels are closed under binary unions.
@isnad1 id=projecti.2h4v.s5.5394eaf9d18d from=translated src=- shape=5d862f59 vocab=10966795
-/
theorem ProjectiveDelta.union {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s t : Set X} (hs : ProjectiveDelta n s) (ht : ProjectiveDelta n t) :
    ProjectiveDelta n (s ∪ t) :=
  ⟨hs.1.union ht.1, hs.2.union ht.2⟩

/-- Projective Delta levels are closed under binary intersections.
@isnad1 id=projecti.2h4v.s5.f7f9cbfb452d from=translated src=- shape=5d862f59 vocab=aad23e48
-/
theorem ProjectiveDelta.inter {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s t : Set X} (hs : ProjectiveDelta n s) (ht : ProjectiveDelta n t) :
    ProjectiveDelta n (s ∩ t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

private def projectiveDummyRelation {X : Type u} (s : Set X) :
    Set (ProjectiveWitness × X) :=
  univ ×ˢ s

private theorem projectiveProjection_dummyRelation {X : Type u} (s : Set X) :
    projectiveProjection (projectiveDummyRelation s) = s := by
  ext x
  simp [projectiveDummyRelation]

/-- Every projective Sigma level is included in its immediate successor.
@isnad1 id=projecti.1h3v.s5.b757460be426 from=translated src=- shape=cf617dfa vocab=118c22a2
-/
theorem ProjectiveSigma.mono_succ {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : ProjectiveSigma n s) :
    ProjectiveSigma (n + 1) s := by
  induction n generalizing X with
  | zero =>
      refine projectiveSigma_succ.mpr
        ⟨projectiveDummyRelation s, projectivePi_zero.mpr ?_,
          projectiveProjection_dummyRelation s⟩
      exact MeasurableSet.univ.prod hs
  | succ n ih =>
      rcases projectiveSigma_succ.mp hs with ⟨R, hR, hproj⟩
      refine projectiveSigma_succ.mpr ⟨R, ?_, hproj⟩
      rw [ProjectivePi] at hR ⊢
      exact ih hR

/-- Every projective Pi level is included in its immediate successor.
@isnad1 id=projecti.1h3v.s5.d0f4f984e429 from=translated src=- shape=39eda916 vocab=0bb2c5ac
-/
theorem ProjectivePi.mono_succ {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : ProjectivePi n s) :
    ProjectivePi (n + 1) s := by
  rw [ProjectivePi] at hs ⊢
  exact hs.mono_succ

/-- Every projective Delta level is included in its immediate successor.
@isnad1 id=projecti.1h3v.s5.ebdf557378a5 from=translated src=- shape=39eda916 vocab=c37647a3
-/
theorem ProjectiveDelta.mono_succ {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {s : Set X} (hs : ProjectiveDelta n s) :
    ProjectiveDelta (n + 1) s :=
  ⟨hs.1.mono_succ, hs.2.mono_succ⟩

/-- Projective Sigma levels are monotone in their finite index.
@isnad1 id=projecti.2h4v.s5.e1abe7787a04 from=translated src=- shape=0c5df298 vocab=49674f08
-/
theorem ProjectiveSigma.mono {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {m n : ℕ} (hmn : m ≤ n) {s : Set X} (hs : ProjectiveSigma m s) :
    ProjectiveSigma n s := by
  induction n, hmn using Nat.le_induction with
  | base => exact hs
  | succ n _ ih => exact ih.mono_succ

/-- Projective Pi levels are monotone in their finite index.
@isnad1 id=projecti.2h4v.s5.0f7dfa41c475 from=translated src=- shape=44002db6 vocab=c1501ec4
-/
theorem ProjectivePi.mono {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {m n : ℕ} (hmn : m ≤ n) {s : Set X} (hs : ProjectivePi m s) :
    ProjectivePi n s := by
  induction n, hmn using Nat.le_induction with
  | base => exact hs
  | succ n _ ih => exact ih.mono_succ

/-- Projective Delta levels are monotone in their finite index.
@isnad1 id=projecti.2h4v.s5.ef5cb693311f from=translated src=- shape=44002db6 vocab=37b55d75
-/
theorem ProjectiveDelta.mono {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {m n : ℕ} (hmn : m ≤ n) {s : Set X} (hs : ProjectiveDelta m s) :
    ProjectiveDelta n s :=
  ⟨hs.1.mono hmn, hs.2.mono hmn⟩

/-- The empty set belongs to every projective Sigma level.
@isnad1 id=projecti.0h2v.s4.c9280315aa55 from=translated src=- shape=0338338b vocab=b0b0b55f
-/
theorem ProjectiveSigma.empty {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} : ProjectiveSigma n (∅ : Set X) :=
  (projectiveSigma_zero.mpr MeasurableSet.empty).mono (Nat.zero_le n)

/-- The universal set belongs to every projective Sigma level.
@isnad1 id=projecti.0h2v.s4.4798f9977c44 from=translated src=- shape=d12d700d vocab=7dc332ba
-/
theorem ProjectiveSigma.univ {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} : ProjectiveSigma n (Set.univ : Set X) :=
  (projectiveSigma_zero.mpr MeasurableSet.univ).mono (Nat.zero_le n)

/-- The empty set belongs to every projective Pi level.
@isnad1 id=projecti.0h2v.s4.39b459c389a1 from=translated src=- shape=09ab81bb vocab=36eea99c
-/
theorem ProjectivePi.empty {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} : ProjectivePi n (∅ : Set X) :=
  (projectivePi_zero.mpr MeasurableSet.empty).mono (Nat.zero_le n)

/-- The universal set belongs to every projective Pi level.
@isnad1 id=projecti.0h2v.s4.30599ac1e2fd from=translated src=- shape=5e94ae0b vocab=d1e2d340
-/
theorem ProjectivePi.univ {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} : ProjectivePi n (Set.univ : Set X) :=
  (projectivePi_zero.mpr MeasurableSet.univ).mono (Nat.zero_le n)

/-- The empty set belongs to every projective Delta level.
@isnad1 id=projecti.0h2v.s4.3dbdc19601b5 from=translated src=- shape=09ab81bb vocab=37978484
-/
theorem ProjectiveDelta.empty {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} : ProjectiveDelta n (∅ : Set X) :=
  ⟨ProjectiveSigma.empty, ProjectivePi.empty⟩

/-- The universal set belongs to every projective Delta level.
@isnad1 id=projecti.0h2v.s4.e6690fc3590b from=translated src=- shape=5e94ae0b vocab=ffee355a
-/
theorem ProjectiveDelta.univ {X : Type u}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} : ProjectiveDelta n (Set.univ : Set X) :=
  ⟨ProjectiveSigma.univ, ProjectivePi.univ⟩

/-- A finite union of Sigma-level sets stays at the same level.
@isnad1 id=projecti.1h5v.s6.da1aa69cb14c from=translated src=- shape=c684ff2a vocab=e705fb5c
-/
theorem ProjectiveSigma.iUnion_finset {X : Type u} {ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} (I : Finset ι) {s : ι → Set X}
    (hs : ∀ i ∈ I, ProjectiveSigma n (s i)) :
    ProjectiveSigma n (⋃ i ∈ I, s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using (ProjectiveSigma.empty (X := X) (n := n))
  | @insert a I ha ih =>
      have hsa : ProjectiveSigma n (s a) := hs a (by simp)
      have hsI : ProjectiveSigma n (⋃ i ∈ I, s i) :=
        ih fun i hi => hs i (by simp [hi])
      simpa [ha] using hsa.union hsI

/-- A finite intersection of Sigma-level sets stays at the same level.
@isnad1 id=projecti.1h5v.s6.802ef96f3cb9 from=translated src=- shape=c684ff2a vocab=02964461
-/
theorem ProjectiveSigma.iInter_finset {X : Type u} {ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} (I : Finset ι) {s : ι → Set X}
    (hs : ∀ i ∈ I, ProjectiveSigma n (s i)) :
    ProjectiveSigma n (⋂ i ∈ I, s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using (ProjectiveSigma.univ (X := X) (n := n))
  | @insert a I ha ih =>
      have hsa : ProjectiveSigma n (s a) := hs a (by simp)
      have hsI : ProjectiveSigma n (⋂ i ∈ I, s i) :=
        ih fun i hi => hs i (by simp [hi])
      simpa [ha] using hsa.inter hsI

/-- A finite union of Pi-level sets stays at the same level.
@isnad1 id=projecti.1h5v.s6.7af29d778922 from=translated src=- shape=b8229acd vocab=cf5eced1
-/
theorem ProjectivePi.iUnion_finset {X : Type u} {ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} (I : Finset ι) {s : ι → Set X}
    (hs : ∀ i ∈ I, ProjectivePi n (s i)) :
    ProjectivePi n (⋃ i ∈ I, s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using (ProjectivePi.empty (X := X) (n := n))
  | @insert a I ha ih =>
      have hsa : ProjectivePi n (s a) := hs a (by simp)
      have hsI : ProjectivePi n (⋃ i ∈ I, s i) :=
        ih fun i hi => hs i (by simp [hi])
      simpa [ha] using hsa.union hsI

/-- A finite intersection of Pi-level sets stays at the same level.
@isnad1 id=projecti.1h5v.s6.16161d342574 from=translated src=- shape=b8229acd vocab=381cdc39
-/
theorem ProjectivePi.iInter_finset {X : Type u} {ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} (I : Finset ι) {s : ι → Set X}
    (hs : ∀ i ∈ I, ProjectivePi n (s i)) :
    ProjectivePi n (⋂ i ∈ I, s i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using (ProjectivePi.univ (X := X) (n := n))
  | @insert a I ha ih =>
      have hsa : ProjectivePi n (s a) := hs a (by simp)
      have hsI : ProjectivePi n (⋂ i ∈ I, s i) :=
        ih fun i hi => hs i (by simp [hi])
      simpa [ha] using hsa.inter hsI

/-- A finite union of Delta-level sets stays at the same level.
@isnad1 id=projecti.1h5v.s6.a65e22e7079d from=translated src=- shape=b8229acd vocab=7bdbde5d
-/
theorem ProjectiveDelta.iUnion_finset {X : Type u} {ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} (I : Finset ι) {s : ι → Set X}
    (hs : ∀ i ∈ I, ProjectiveDelta n (s i)) :
    ProjectiveDelta n (⋃ i ∈ I, s i) :=
  ⟨ProjectiveSigma.iUnion_finset I fun i hi => (hs i hi).1,
    ProjectivePi.iUnion_finset I fun i hi => (hs i hi).2⟩

/-- A finite intersection of Delta-level sets stays at the same level.
@isnad1 id=projecti.1h5v.s6.988436b918fd from=translated src=- shape=b8229acd vocab=9bb1375e
-/
theorem ProjectiveDelta.iInter_finset {X : Type u} {ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} (I : Finset ι) {s : ι → Set X}
    (hs : ∀ i ∈ I, ProjectiveDelta n (s i)) :
    ProjectiveDelta n (⋂ i ∈ I, s i) :=
  ⟨ProjectiveSigma.iInter_finset I fun i hi => (hs i hi).1,
    ProjectivePi.iInter_finset I fun i hi => (hs i hi).2⟩

end DescriptiveSetTheory
