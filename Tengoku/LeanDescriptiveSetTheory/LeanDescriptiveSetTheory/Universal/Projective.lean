/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Projective.Compatibility
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Universal.Coanalytic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Universal relations for every positive finite projective level

The level-one relations are the existing universal analytic and coanalytic relations. At a
successor level, a parameter for a relation on two Baire coordinates is reused after packing the
witness/object pair into one Baire point. Existentially projecting that packed relation gives the
next Sigma universal; the Pi universal is its exact complement.

The public theorems cover every positive finite level. The encoding used by the recursion is kept
internal, and no relation universal across all levels at once is asserted.
-/

open Set

namespace DescriptiveSetTheory

/-- Existentially lift a parameterized Baire relation after packing a witness/object pair.-/
private def projectiveSuccessorUniversal
    (U : Set (ProjectiveWitness × ProjectiveWitness)) :
    Set (ProjectiveWitness × ProjectiveWitness) :=
  {q | ∃ w, (q.1, packBairePair (w, q.2)) ∈ U}

/-- The continuous map whose preimage is projected in the successor construction.-/
private def projectiveSuccessorWitnessMap
    (q : ProjectiveWitness × (ProjectiveWitness × ProjectiveWitness)) :
    ProjectiveWitness × ProjectiveWitness :=
  (q.2.1, packBairePair (q.1, q.2.2))

private theorem continuous_projectiveSuccessorWitnessMap :
    Continuous projectiveSuccessorWitnessMap :=
  (continuous_fst.comp continuous_snd).prodMk
    (continuous_packBairePair.comp
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

private theorem projectiveSuccessorUniversal_eq_projection
    (U : Set (ProjectiveWitness × ProjectiveWitness)) :
    projectiveSuccessorUniversal U =
      projectiveProjection (projectiveSuccessorWitnessMap ⁻¹' U) := by
  ext q
  simp [projectiveSuccessorUniversal, projectiveSuccessorWitnessMap]

private theorem projectiveSigma_projectiveSuccessorUniversal {n : ℕ}
    {U : Set (ProjectiveWitness × ProjectiveWitness)} (hU : ProjectivePi n U) :
    ProjectiveSigma (n + 1) (projectiveSuccessorUniversal U) := by
  rw [projectiveSuccessorUniversal_eq_projection]
  exact (hU.preimage continuous_projectiveSuccessorWitnessMap).projectiveProjection

private theorem isUniversalFor_projectiveSuccessorUniversal {n : ℕ}
    {U : Set (ProjectiveWitness × ProjectiveWitness)}
    (hTotal : ProjectivePi n U)
    (hU : IsUniversalFor (ProjectivePi n) U) :
    IsUniversalFor (ProjectiveSigma (n + 1)) (projectiveSuccessorUniversal U) := by
  intro s
  constructor
  · intro hs
    rcases projectiveSigma_succ.mp hs with ⟨R, hR, hproj⟩
    have hPacked : ProjectivePi n (unpackBairePair ⁻¹' R) :=
      hR.preimage continuous_unpackBairePair
    obtain ⟨p, hp⟩ := (hU (unpackBairePair ⁻¹' R)).mp hPacked
    refine ⟨p, ?_⟩
    rw [← hproj]
    ext x
    constructor
    · rintro ⟨w, hw⟩
      have hw' : packBairePair (w, x) ∈ verticalSection U p := hw
      rw [hp] at hw'
      exact ⟨w, by simpa using hw'⟩
    · rintro ⟨w, hw⟩
      refine ⟨w, ?_⟩
      have hw' : packBairePair (w, x) ∈ unpackBairePair ⁻¹' R := by
        simpa using hw
      rw [← hp] at hw'
      exact hw'
  · rintro ⟨p, rfl⟩
    exact (projectiveSigma_projectiveSuccessorUniversal hTotal).verticalSection p

private theorem isUniversalFor_projectivePi_compl {n : ℕ}
    {U : Set (ProjectiveWitness × ProjectiveWitness)}
    (hU : IsUniversalFor (ProjectiveSigma n) U) :
    IsUniversalFor (ProjectivePi n) Uᶜ := by
  intro s
  constructor
  · intro hs
    obtain ⟨p, hp⟩ := (hU sᶜ).mp hs
    refine ⟨p, ?_⟩
    ext x
    simp [hp]
  · rintro ⟨p, rfl⟩
    rw [ProjectivePi]
    simpa using (hU (verticalSection U p)).mpr ⟨p, rfl⟩

/-- A recursively universal Sigma relation at every positive projective level. Level zero is an
unused compatibility value; every public theorem is indexed by `n + 1`.-/
def baireUniversalProjectiveSigma : ℕ → Set (ProjectiveWitness × ProjectiveWitness)
  | 0 => ∅
  | 1 => baireUniversalAnalytic
  | n + 2 => projectiveSuccessorUniversal (baireUniversalProjectiveSigma (n + 1))ᶜ

/-- The universal Pi relation is the exact complement of the matching Sigma relation.-/
def baireUniversalProjectivePi (n : ℕ) : Set (ProjectiveWitness × ProjectiveWitness) :=
  (baireUniversalProjectiveSigma n)ᶜ

/-- The projective level-one Sigma universal is the released universal analytic relation.
@isnad1 id=eq.0h0v.s3.f3e2c553165f from=translated src=- shape=404dec73 vocab=3130f3c3
-/
@[simp]
theorem baireUniversalProjectiveSigma_one :
    baireUniversalProjectiveSigma 1 = baireUniversalAnalytic :=
  rfl

/-- The projective level-one Pi universal is the released universal coanalytic relation.
@isnad1 id=eq.0h0v.s3.1b9fd5582051 from=translated src=- shape=404dec73 vocab=00bc5571
-/
@[simp]
theorem baireUniversalProjectivePi_one :
    baireUniversalProjectivePi 1 = baireUniversalCoanalytic :=
  rfl

private theorem baireUniversalProjective_mutual (n : ℕ) :
    (ProjectiveSigma (n + 1) (baireUniversalProjectiveSigma (n + 1)) ∧
      IsUniversalFor (ProjectiveSigma (n + 1))
        (baireUniversalProjectiveSigma (n + 1))) ∧
    (ProjectivePi (n + 1) (baireUniversalProjectivePi (n + 1)) ∧
      IsUniversalFor (ProjectivePi (n + 1))
        (baireUniversalProjectivePi (n + 1))) := by
  induction n with
  | zero =>
      refine ⟨⟨projectiveSigma_one_iff_analyticSet.mpr
          analyticSet_baireUniversalAnalytic, ?_⟩,
        ⟨projectivePi_one_iff_isCoanalytic.mpr
          isCoanalytic_baireUniversalCoanalytic, ?_⟩⟩
      · intro s
        rw [projectiveSigma_one_iff_analyticSet]
        exact isUniversalAnalytic_baireUniversalAnalytic.2 s
      · intro s
        rw [projectivePi_one_iff_isCoanalytic]
        exact isUniversalCoanalytic_baireUniversalCoanalytic.2 s
  | succ n ih =>
      rcases ih with ⟨⟨hSigma, hUniversalSigma⟩, ⟨hPi, hUniversalPi⟩⟩
      have hNextSigma : ProjectiveSigma (n + 2)
          (baireUniversalProjectiveSigma (n + 2)) := by
        simpa [baireUniversalProjectiveSigma, baireUniversalProjectivePi] using
          projectiveSigma_projectiveSuccessorUniversal hPi
      have hNextUniversalSigma : IsUniversalFor (ProjectiveSigma (n + 2))
          (baireUniversalProjectiveSigma (n + 2)) := by
        simpa [baireUniversalProjectiveSigma, baireUniversalProjectivePi] using
          isUniversalFor_projectiveSuccessorUniversal hPi hUniversalPi
      refine ⟨⟨hNextSigma, hNextUniversalSigma⟩, ⟨?_, ?_⟩⟩
      · simpa [baireUniversalProjectivePi] using hNextSigma.compl
      · exact isUniversalFor_projectivePi_compl hNextUniversalSigma

/-- The total universal Sigma relation has the advertised positive finite projective complexity.
@isnad1 id=projecti.0h1v.s6.ed02569b2cdb from=translated src=- shape=2dea0517 vocab=718ecd0c
-/
theorem projectiveSigma_baireUniversalProjectiveSigma (n : ℕ) :
    ProjectiveSigma (n + 1) (baireUniversalProjectiveSigma (n + 1)) :=
  (baireUniversalProjective_mutual n).1.1

/-- The total universal Pi relation has the advertised positive finite projective complexity.
@isnad1 id=projecti.0h1v.s6.cec74b3a05dd from=translated src=- shape=75d2fbe7 vocab=f303e7e8
-/
theorem projectivePi_baireUniversalProjectivePi (n : ℕ) :
    ProjectivePi (n + 1) (baireUniversalProjectivePi (n + 1)) :=
  (baireUniversalProjective_mutual n).2.1

/-- Every positive finite projective Sigma class has an exact Baire-parameter universal relation.
@isnad1 id=isuniver.0h1v.s5.62a12e057895 from=translated src=- shape=7a57e697 vocab=2013b6fb
-/
theorem isUniversalFor_baireUniversalProjectiveSigma (n : ℕ) :
    IsUniversalFor (ProjectiveSigma (n + 1))
      (baireUniversalProjectiveSigma (n + 1)) :=
  (baireUniversalProjective_mutual n).1.2

/-- Every positive finite projective Pi class has an exact Baire-parameter universal relation.
@isnad1 id=isuniver.0h1v.s5.144b3ae68586 from=translated src=- shape=840c9cb0 vocab=f08b1ce8
-/
theorem isUniversalFor_baireUniversalProjectivePi (n : ℕ) :
    IsUniversalFor (ProjectivePi (n + 1))
      (baireUniversalProjectivePi (n + 1)) :=
  (baireUniversalProjective_mutual n).2.2

/-- Every section of the positive-level Sigma universal has the same projective complexity.
@isnad1 id=projecti.0h2v.s5.65997f52f256 from=translated src=- shape=6ad045dd vocab=754aef53
-/
theorem projectiveSigma_verticalSection_baireUniversalProjectiveSigma
    (n : ℕ) (p : ProjectiveWitness) :
    ProjectiveSigma (n + 1)
      (verticalSection (baireUniversalProjectiveSigma (n + 1)) p) :=
  (projectiveSigma_baireUniversalProjectiveSigma n).verticalSection p

/-- Every section of the positive-level Pi universal has the same projective complexity.
@isnad1 id=projecti.0h2v.s5.4984cc1aeb28 from=translated src=- shape=09f2905b vocab=2c960dba
-/
theorem projectivePi_verticalSection_baireUniversalProjectivePi
    (n : ℕ) (p : ProjectiveWitness) :
    ProjectivePi (n + 1)
      (verticalSection (baireUniversalProjectivePi (n + 1)) p) :=
  (projectivePi_baireUniversalProjectivePi n).verticalSection p

/-- Every Sigma set at a positive finite level occurs as an exact universal section.
@isnad1 id=ex.1h2v.s6.55bbf4a16bdf from=translated src=- shape=d4282610 vocab=5c96b74b
-/
theorem exists_verticalSection_baireUniversalProjectiveSigma
    (n : ℕ) {s : Set ProjectiveWitness} (hs : ProjectiveSigma (n + 1) s) :
    ∃ p, verticalSection (baireUniversalProjectiveSigma (n + 1)) p = s :=
  (isUniversalFor_baireUniversalProjectiveSigma n s).mp hs

/-- Every Pi set at a positive finite level occurs as an exact universal section.
@isnad1 id=ex.1h2v.s6.40130fdea0bb from=translated src=- shape=c344a966 vocab=45b32cc4
-/
theorem exists_verticalSection_baireUniversalProjectivePi
    (n : ℕ) {s : Set ProjectiveWitness} (hs : ProjectivePi (n + 1) s) :
    ∃ p, verticalSection (baireUniversalProjectivePi (n + 1)) p = s :=
  (isUniversalFor_baireUniversalProjectivePi n s).mp hs

end DescriptiveSetTheory
