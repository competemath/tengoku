import Tengoku.PaperCLean.PaperC.Combinatorics.CanonicalResidualCellMembership
import Tengoku.PaperCLean.PaperC.Combinatorics.CanonicalResidualCRTCertificate
import Tengoku.PaperCLean.PaperC.Combinatorics.CertificateCellFamilies
import Tengoku.PaperCLean.PaperC.Combinatorics.CertificatePopulationCover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 1800000

/-!
# Canonical residual certificates in a fixed ambient cell family

For one fixed active rational channel, this file builds the common finite
family used by Lemma 7.1.  Its prime labels range over
`residualPrimeRange`, and the fibre above a prime `p` is
`residualVertexPrimeCells ... p ...`.

The pair-dependent canonical certificate of Lemma 6.5 embeds into this
ambient family.  The embedding preserves its modulus and both start
residues, and is injective because different residual components select
different primes.
-/

namespace PaperC
namespace CanonicalResidualComponents

open Affine
open Affine.CanonicalRationalCode
open Affine.RationalChannelCode
open LargePrimeGraph
open ResidualComponentCounts
open ResidualChannelLemmaSevenTwo

noncomputable section

/-- The finite type of prime labels available to one fixed channel.-/
abbrev CanonicalResidualAmbientPrime (L a b : ℕ) :=
  {p : ℕ // p ∈ residualPrimeRange L a b}

/-- The fibre of residual vertex cells above one ambient prime.-/
def canonicalResidualAmbientCells
    (L a b : ℕ) (h : ℤ)
    (p : CanonicalResidualAmbientPrime L a b) :
    Finset (Fin (L + 1) × Fin (L + 1)) :=
  residualVertexPrimeCells L a b p.1 h

/-- The common prime-labelled residual cell family of a fixed channel.-/
abbrev CanonicalResidualAmbientCell
    (L a b : ℕ) (h : ℤ) :=
  CRT.LabeledCell (canonicalResidualAmbientCells L a b h)

/-- The natural modulus map on ambient prime labels.-/
def canonicalResidualAmbientPrimeModulus
    {L a b : ℕ} :
    CanonicalResidualAmbientPrime L a b → ℕ :=
  Subtype.val

/-- Every modulus in the ambient prime range is prime.
@isnad1 id=prime.0h4v.s4.12eea3aef609 from=translated src=- shape=9380dd05 vocab=8dc88bfe
-/
theorem canonicalResidualAmbientPrimeModulus_prime
    {L a b : ℕ}
    (p : CanonicalResidualAmbientPrime L a b) :
    (canonicalResidualAmbientPrimeModulus p).Prime :=
  (mem_residualPrimeRange.mp p.2).1

/-- The modulus carried by an ambient labelled cell.-/
def canonicalResidualAmbientCellModulus
    {L a b : ℕ} {h : ℤ}
    (z : CanonicalResidualAmbientCell L a b h) : ℕ :=
  CRT.labeledCellModulus
    (canonicalResidualAmbientCells L a b h)
    canonicalResidualAmbientPrimeModulus z

/-- The left-start residue encoded by an ambient residual cell.-/
def canonicalResidualAmbientLeftResidue
    {L a b : ℕ} {h : ℤ}
    (z : CanonicalResidualAmbientCell L a b h) : ℕ :=
  CRT.startResidue
    (canonicalResidualAmbientCellModulus z) z.2.1.1

/-- The right-start residue encoded by an ambient residual cell.-/
def canonicalResidualAmbientRightResidue
    {L a b : ℕ} {h : ℤ}
    (z : CanonicalResidualAmbientCell L a b h) : ℕ :=
  CRT.startResidue
    (canonicalResidualAmbientCellModulus z) z.2.1.2

/--
Embed one canonical residual component into the common cell family of its
fixed active channel.-/
noncomputable def canonicalResidualCertificateToAmbientCell
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2))
    (C : CanonicalResidualCertificateIndex A x y L) :
    CanonicalResidualAmbientCell
      L c.1.1 c.1.2 (pairChannelError x y c.1.1 c.1.2) :=
  ⟨⟨(canonicalResidualCertificates hx hy C).prime,
      canonicalResidualCertificates_prime_mem_residualPrimeRange_of_choice
        hx hy c hchoice hm C⟩,
    ⟨((canonicalResidualCertificates hx hy C).left,
        (canonicalResidualCertificates hx hy C).right),
      canonicalResidualCertificates_mem_residualVertexPrimeCells_of_choice
        hx hy c hchoice hm C⟩⟩

/-- The ambient embedding preserves the selected prime modulus.
@isnad1 id=eq.4h6v.s9.bd559c18210e from=translated src=- shape=701f007f vocab=ccdbf1bc
-/
@[simp]
theorem canonicalResidualCertificateToAmbientCell_modulus
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2))
    (C : CanonicalResidualCertificateIndex A x y L) :
    canonicalResidualAmbientCellModulus
        (canonicalResidualCertificateToAmbientCell
          hx hy c hchoice hm C) =
      canonicalResidualCertificateModulus hx hy C := by
  rfl

/-- The ambient embedding preserves the left-start residue.
@isnad1 id=eq.4h6v.s9.447ac6d0cfe3 from=translated src=- shape=701f007f vocab=1ccf367c
-/
@[simp]
theorem canonicalResidualCertificateToAmbientCell_leftResidue
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2))
    (C : CanonicalResidualCertificateIndex A x y L) :
    canonicalResidualAmbientLeftResidue
        (canonicalResidualCertificateToAmbientCell
          hx hy c hchoice hm C) =
      canonicalResidualCertificateLeftResidue hx hy C := by
  rfl

/-- The ambient embedding preserves the right-start residue.
@isnad1 id=eq.4h6v.s9.d82cee06a712 from=translated src=- shape=701f007f vocab=df262def
-/
@[simp]
theorem canonicalResidualCertificateToAmbientCell_rightResidue
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2))
    (C : CanonicalResidualCertificateIndex A x y L) :
    canonicalResidualAmbientRightResidue
        (canonicalResidualCertificateToAmbientCell
          hx hy c hchoice hm C) =
      canonicalResidualCertificateRightResidue hx hy C := by
  rfl

/--
Canonical residual components embed injectively in the common ambient
cell family.
@isnad1 id=injectiv.4h5v.s9.8e2b98d06dfd from=translated src=- shape=cda049ed vocab=cbadaed0
-/
theorem canonicalResidualCertificateToAmbientCell_injective
    {A x y L : ℕ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2)) :
    Function.Injective
      (canonicalResidualCertificateToAmbientCell
        hx hy c hchoice hm) := by
  intro C D hCD
  apply canonicalResidualCertificates_prime_injective hx hy
  have hprime :=
    congrArg
      (fun z :
          CanonicalResidualAmbientCell
            L c.1.1 c.1.2
              (pairChannelError x y c.1.1 c.1.2) ↦
        z.1.1)
      hCD
  exact hprime

/--
The image of all canonical residual components is an unordered certificate
of size `c#` in the common ambient family.-/
noncomputable def canonicalResidualAmbientCertificate
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2)) :
    CRT.UnorderedCertificate
      (Finset.univ :
        Finset
          (CanonicalResidualAmbientCell
            L c.1.1 c.1.2
              (pairChannelError x y c.1.1 c.1.2)))
      (canonicalResidualComponentCount A x y L) := by
  classical
  let f :=
    canonicalResidualCertificateToAmbientCell
      (A := A) (L := L)
      (show 1 ≤ x by omega) (show 1 ≤ y by omega)
      c hchoice hm
  refine
    ⟨Finset.univ.image f,
      Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, ?_⟩⟩
  rw [Finset.card_image_of_injective Finset.univ
      (canonicalResidualCertificateToAmbientCell_injective
        (A := A) (L := L)
        (show 1 ≤ x by omega) (show 1 ≤ y by omega)
        c hchoice hm),
    Finset.card_univ]
  exact card_canonicalResidualCertificateIndex hx hy

/--
@isnad1 id=eq.4h5v.s13.af82a18556dd from=translated src=- shape=16b5c8a3 vocab=046b39dc
-/
@[simp]
theorem canonicalResidualAmbientCertificate_coe
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2)) :
    (canonicalResidualAmbientCertificate hx hy c hchoice hm).1 =
      Finset.univ.image
        (canonicalResidualCertificateToAmbientCell
          (A := A) (L := L)
          (show 1 ≤ x by omega) (show 1 ≤ y by omega)
          c hchoice hm) := by
  rfl

/--
@isnad1 id=mem.4h6v.s12.5d86052dd41c from=translated src=- shape=80ca6f28 vocab=96e44d47
-/
@[simp]
theorem canonicalResidualCertificateToAmbientCell_mem
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2))
    (C : CanonicalResidualCertificateIndex A x y L) :
    canonicalResidualCertificateToAmbientCell
        (show 1 ≤ x by omega) (show 1 ≤ y by omega)
        c hchoice hm C ∈
      (canonicalResidualAmbientCertificate hx hy c hchoice hm).1 := by
  rw [canonicalResidualAmbientCertificate_coe]
  exact Finset.mem_image.mpr ⟨C, Finset.mem_univ C, rfl⟩

/--
The modulus product of the ambient certificate is the original canonical
prime product `P#`.
@isnad1 id=eq.4h5v.s11.e9e4878940c8 from=translated src=- shape=f073006f vocab=26650c53
-/
theorem canonicalResidualAmbientCertificate_modulusProduct
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2)) :
    CRT.certificateModulusProduct
        canonicalResidualAmbientCellModulus
        (canonicalResidualAmbientCertificate hx hy c hchoice hm) =
      canonicalResidualPrimeProduct
        (A := A) (L := L)
        (show 1 ≤ x by omega) (show 1 ≤ y by omega) := by
  classical
  rw [canonicalResidualPrimeProduct_eq_product_certificates]
  unfold CRT.certificateModulusProduct
  rw [canonicalResidualAmbientCertificate_coe]
  rw [Finset.prod_image]
  · simp only [canonicalResidualCertificateToAmbientCell_modulus,
      canonicalResidualCertificateModulus]
  · intro C _hC D _hD hCD
    exact
      canonicalResidualCertificateToAmbientCell_injective
        (A := A) (L := L)
        (show 1 ≤ x by omega) (show 1 ≤ y by omega)
        c hchoice hm hCD

/-- The moduli selected inside the ambient certificate are pairwise distinct.
@isnad1 id=pairwise.4h5v.s12.58efb89464ce from=translated src=- shape=3b4cec6c vocab=0f360379
-/
theorem canonicalResidualAmbientCertificate_moduli_pairwise
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2)) :
    (canonicalResidualAmbientCertificate
        hx hy c hchoice hm).1.toList.Pairwise
      (fun z w ↦
        canonicalResidualAmbientCellModulus z ≠
          canonicalResidualAmbientCellModulus w) := by
  classical
  apply
    (canonicalResidualAmbientCertificate
      hx hy c hchoice hm).1.nodup_toList.pairwise_of_forall_ne
  intro z hz w hw hzw
  rw [canonicalResidualAmbientCertificate_coe] at hz hw
  have hz' :
      z ∈ Finset.univ.image
        (canonicalResidualCertificateToAmbientCell
          (A := A) (L := L)
          (show 1 ≤ x by omega) (show 1 ≤ y by omega)
          c hchoice hm) := by
    simpa using hz
  have hw' :
      w ∈ Finset.univ.image
        (canonicalResidualCertificateToAmbientCell
          (A := A) (L := L)
          (show 1 ≤ x by omega) (show 1 ≤ y by omega)
          c hchoice hm) := by
    simpa using hw
  obtain ⟨C, _hC, rfl⟩ := Finset.mem_image.mp hz'
  obtain ⟨D, _hD, rfl⟩ := Finset.mem_image.mp hw'
  intro hmod
  apply hzw
  apply congrArg
    (canonicalResidualCertificateToAmbientCell
      (A := A) (L := L)
      (show 1 ≤ x by omega) (show 1 ≤ y by omega)
      c hchoice hm)
  apply
    canonicalResidualCertificates_prime_injective
      (show 1 ≤ x by omega) (show 1 ≤ y by omega)
  simpa only [canonicalResidualCertificateToAmbientCell_modulus,
    canonicalResidualCertificateModulus] using hmod

/--
For the ambient incarnation, admissibility is again exactly the branch
`P# ≤ N`.
@isnad1 id=iff.4h6v.s11.e98f59b9ecb3 from=translated src=- shape=86548dba vocab=6188e50f
-/
theorem canonicalResidualAmbientCertificate_admissible_iff
    {A x y L N : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2)) :
    CRT.CertificateAdmissible
        canonicalResidualAmbientCellModulus N
        (canonicalResidualAmbientCertificate hx hy c hchoice hm) ↔
      CanonicalResidualPrimeProductAtMost
        (A := A) (L := L)
        (show 1 ≤ x by omega) (show 1 ≤ y by omega) N := by
  unfold CRT.CertificateAdmissible
  unfold CanonicalResidualPrimeProductAtMost
  rw [canonicalResidualAmbientCertificate_modulusProduct
    (A := A) (L := L) hx hy c hchoice hm]
  constructor
  · exact fun h ↦ h.2
  · exact fun h ↦
      ⟨canonicalResidualAmbientCertificate_moduli_pairwise
          (A := A) (L := L) hx hy c hchoice hm,
        h⟩

/-! ## Satisfaction of the transported congruences -/

/-- The left start satisfies every congruence in the ambient certificate.
@isnad1 id=modeq.5h6v.s12.9269adf7f1e1 from=translated src=- shape=22ce1951 vocab=5aa34244
-/
theorem canonicalResidual_left_satisfies_ambientCertificate
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2)) :
    ∀ z ∈
        (canonicalResidualAmbientCertificate
          hx hy c hchoice hm).1.toList,
      x ≡ canonicalResidualAmbientLeftResidue z
        [MOD canonicalResidualAmbientCellModulus z] := by
  classical
  intro z hz
  have hz' :
      z ∈
        (canonicalResidualAmbientCertificate
          hx hy c hchoice hm).1 := by
    simpa using hz
  rw [canonicalResidualAmbientCertificate_coe] at hz'
  obtain ⟨C, _hC, rfl⟩ := Finset.mem_image.mp hz'
  simpa only [
      canonicalResidualCertificateToAmbientCell_leftResidue,
      canonicalResidualCertificateToAmbientCell_modulus] using
    canonicalResidual_left_modEq
      (A := A) (L := L)
      (show 1 ≤ x by omega) (show 1 ≤ y by omega) C

/-- The right start satisfies every congruence in the ambient certificate.
@isnad1 id=modeq.5h6v.s12.e9727356c431 from=translated src=- shape=19152279 vocab=86262ec2
-/
theorem canonicalResidual_right_satisfies_ambientCertificate
    {A x y L : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2)) :
    ∀ z ∈
        (canonicalResidualAmbientCertificate
          hx hy c hchoice hm).1.toList,
      y ≡ canonicalResidualAmbientRightResidue z
        [MOD canonicalResidualAmbientCellModulus z] := by
  classical
  intro z hz
  have hz' :
      z ∈
        (canonicalResidualAmbientCertificate
          hx hy c hchoice hm).1 := by
    simpa using hz
  rw [canonicalResidualAmbientCertificate_coe] at hz'
  obtain ⟨C, _hC, rfl⟩ := Finset.mem_image.mp hz'
  simpa only [
      canonicalResidualCertificateToAmbientCell_rightResidue,
      canonicalResidualCertificateToAmbientCell_modulus] using
    canonicalResidual_right_modEq
      (A := A) (L := L)
      (show 1 ≤ x by omega) (show 1 ≤ y by omega) C

/--
If the two starts lie in the prescribed intervals, their pair belongs to
the rectangular solution set of the transported ambient certificate.
@isnad1 id=mem.6h9v.s13.69ba4c14d51d from=translated src=- shape=6902ce3f vocab=bc226715
-/
theorem canonicalResidual_pair_mem_ambientCertificatePairSolutions
    {A x y L a₁ b₁ a₂ b₂ : ℕ}
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (c : ReducedCandidate x y (L + 1) ((L + 1) ^ A))
    (hchoice :
      canonicalReducedCandidate?
          x y (L + 1) ((L + 1) ^ A) =
        some c)
    (hm :
      2 ≤ channelUnitCount L c.1.1 c.1.2
        (pairChannelError x y c.1.1 c.1.2))
    (hxI : x ∈ Finset.Ico a₁ b₁)
    (hyI : y ∈ Finset.Ico a₂ b₂) :
    (x, y) ∈
      CRT.certificatePairSolutions
        canonicalResidualAmbientLeftResidue
        canonicalResidualAmbientRightResidue
        canonicalResidualAmbientCellModulus
        a₁ b₁ a₂ b₂
        (canonicalResidualAmbientCertificate
          hx hy c hchoice hm) := by
  unfold CRT.certificatePairSolutions
  rw [Finset.mem_product]
  constructor
  · rw [Finset.mem_filter]
    exact
      ⟨hxI,
        canonicalResidual_left_satisfies_ambientCertificate
          (A := A) (L := L) hx hy c hchoice hm⟩
  · rw [Finset.mem_filter]
    exact
      ⟨hyI,
        canonicalResidual_right_satisfies_ambientCertificate
          (A := A) (L := L) hx hy c hchoice hm⟩

end

end CanonicalResidualComponents
end PaperC
