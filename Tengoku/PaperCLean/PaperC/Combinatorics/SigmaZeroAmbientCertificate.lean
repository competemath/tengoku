import Tengoku.PaperCLean.PaperC.Arithmetic.DyadicPrimeReciprocalSums
import Tengoku.PaperCLean.PaperC.Arithmetic.RationalMassFinite
import Tengoku.PaperCLean.PaperC.Combinatorics.CanonicalResidualCRTCertificate
import Tengoku.PaperCLean.PaperC.Combinatorics.CertificateCellFamilies
import Tengoku.PaperCLean.PaperC.Combinatorics.LargeKernelAssignments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 1800000

/-!
# A pair-independent ambient certificate for the `σ = 0` branch

The canonical residual certificate constructed in
`CanonicalResidualCRTCertificate` has an index type depending on the pair
`(x,y)`.  Lemma 7.1, on the other hand, sums certificates inside one fixed
finite family.  This file supplies the missing transport.

For starts in the dyadic block `[N,2N)`, every selected residual prime lies
in `(L+1, 2N+L]`.  We therefore take this finite prime interval as the
pair-independent prime type, and put above each prime the complete set of
left--right boundary cells `Fin (L+1) × Fin (L+1)`.

Each canonical residual component maps injectively to the labeled cell
formed by its selected prime and its selected pair of offsets.  Its image is
an unordered ambient certificate of size `c#`; its modulus product is still
exactly `P#`, and the two starts satisfy all of its congruences.
-/

namespace PaperC
namespace SigmaZeroAmbientCertificate

open Affine
open CanonicalResidualComponents
open DyadicPrimeReciprocalSums
open LargePrimeGraph
open RationalMassFinite
open ResidualComponentCounts
open scoped BigOperators

noncomputable section

/-- All possible residual primes for pairs in the dyadic block.-/
def ambientPrimes (N L : ℕ) : Finset ℕ :=
  primesBetween (L + 1) (dyadicCutoff N L)

/-- The fixed prime-label type used for all pairs at scales `N,L`.-/
abbrev AmbientPrime (N L : ℕ) :=
  {p : ℕ // p ∈ ambientPrimes N L}

/-- The fixed left--right boundary-cell type.-/
abbrev AmbientCell (L : ℕ) :=
  Fin (L + 1) × Fin (L + 1)

/-- Every ambient prime is allowed to carry every boundary cell.-/
def ambientCells (N L : ℕ) :
    AmbientPrime N L → Finset (AmbientCell L) :=
  fun _p ↦ Finset.univ

/-- Each ambient prime carries exactly the manuscript's `B²` cells.
@isnad1 id=eq.0h3v.s5.5c24ca957764 from=translated src=- shape=206ec68c vocab=fa08a375
-/
@[simp]
theorem card_ambientCells
    {N L : ℕ} (p : AmbientPrime N L) :
    (ambientCells N L p).card = (L + 1) ^ 2 := by
  simp [ambientCells, pow_two]

/-- A prime-tagged boundary cell in the fixed ambient family.-/
abbrev AmbientLabeledCell (N L : ℕ) :=
  CRT.LabeledCell (ambientCells N L)

/-- The natural prime modulus of an ambient prime label.-/
def ambientPrimeModulus {N L : ℕ} (p : AmbientPrime N L) : ℕ :=
  p.1

/-- The prime modulus carried by an ambient labeled cell.-/
def ambientModulus {N L : ℕ} (z : AmbientLabeledCell N L) : ℕ :=
  CRT.labeledCellModulus (ambientCells N L) ambientPrimeModulus z

/-- The residue imposed on the left start by an ambient labeled cell.-/
def ambientLeftResidue {N L : ℕ}
    (z : AmbientLabeledCell N L) : ℕ :=
  CRT.startResidue z.1.1 z.2.1.1

/-- The residue imposed on the right start by an ambient labeled cell.-/
def ambientRightResidue {N L : ℕ}
    (z : AmbientLabeledCell N L) : ℕ :=
  CRT.startResidue z.1.1 z.2.1.2

/--
@isnad1 id=iff.0h3v.s5.5bbc07ebf060 from=translated src=- shape=a60962a8 vocab=6369cc28
-/
@[simp]
theorem mem_ambientPrimes {N L p : ℕ} :
    p ∈ ambientPrimes N L ↔
      p.Prime ∧ L + 1 < p ∧ p ≤ dyadicCutoff N L := by
  simp [ambientPrimes]

/-- Every modulus in the ambient family is prime.
@isnad1 id=prime.0h3v.s3.cd8c954b8ff1 from=translated src=- shape=2ebfc141 vocab=0e6e0e07
-/
theorem ambientModulus_prime
    {N L : ℕ} (z : AmbientLabeledCell N L) :
    (ambientModulus z).Prime := by
  exact (mem_ambientPrimes.mp z.1.2).1

/--
@isnad1 id=le.2h4v.s5.a7aaffe4fa32 from=translated src=- shape=bd45e23b vocab=ccec13c1
-/
theorem pair_left_one_le
    {N x y L : ℕ} (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    1 ≤ x := by
  have hx :=
    two_le_of_mem_dyadicBlock hN
      (mem_separatedDyadicPairs.mp hpair).1
  omega

/--
@isnad1 id=le.2h4v.s5.8b111cba19c3 from=translated src=- shape=818ed2c3 vocab=ccec13c1
-/
theorem pair_right_one_le
    {N x y L : ℕ} (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    1 ≤ y := by
  have hy :=
    two_le_of_mem_dyadicBlock hN
      (mem_separatedDyadicPairs.mp hpair).2.1
  omega

/--
The prime chosen by a canonical residual component belongs to the fixed
dyadic ambient prime family.
@isnad1 id=mem.2h6v.s7.c741d7ef58fd from=translated src=- shape=ef342ec4 vocab=a8fb312f
-/
theorem canonicalResidualCertificatePrime_mem_ambientPrimes
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L)
    (C : CanonicalResidualCertificateIndex A x y L) :
    (canonicalResidualCertificates
        (pair_left_one_le hN hpair)
        (pair_right_one_le hN hpair)
        C).prime ∈ ambientPrimes N L := by
  let cert :=
    canonicalResidualCertificates
      (pair_left_one_le hN hpair)
      (pair_right_one_le hN hpair)
      C
  have hxBlock : x ∈ dyadicBlock N :=
    (mem_separatedDyadicPairs.mp hpair).1
  have hx : 2 ≤ x := two_le_of_mem_dyadicBlock hN hxBlock
  have hlabelPos :
      0 < startCompleteVertexLabel x L cert.left := by
    have hlower :=
      LargePrimeComponents.startCompleteVertexLabel_lower
        (show 1 ≤ x by omega) cert.left
    omega
  have hpLeLabel :
      cert.prime ≤ startCompleteVertexLabel x L cert.left :=
    Nat.le_of_dvd hlabelPos cert.prime_dvd_left_label
  have hlabelLe :
      startCompleteVertexLabel x L cert.left ≤ dyadicCutoff N L :=
    LargeKernelAssignments.startCompleteVertexLabel_le_dyadicCutoff
      hxBlock cert.left
  rw [mem_ambientPrimes]
  exact ⟨cert.prime_large.1, cert.prime_large.2,
    hpLeLabel.trans hlabelLe⟩

/-- The selected prime, packaged as an element of the fixed prime type.-/
noncomputable def componentAmbientPrime
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L)
    (C : CanonicalResidualCertificateIndex A x y L) :
    AmbientPrime N L :=
  ⟨(canonicalResidualCertificates
      (pair_left_one_le hN hpair)
      (pair_right_one_le hN hpair)
      C).prime,
    canonicalResidualCertificatePrime_mem_ambientPrimes hN hpair C⟩

/--
Encoding of a canonical residual component as a cell in the fixed ambient
family.-/
noncomputable def componentAmbientCell
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L)
    (C : CanonicalResidualCertificateIndex A x y L) :
    AmbientLabeledCell N L :=
  ⟨componentAmbientPrime hN hpair C,
    ⟨((canonicalResidualCertificates
        (pair_left_one_le hN hpair)
        (pair_right_one_le hN hpair)
        C).left,
      (canonicalResidualCertificates
        (pair_left_one_le hN hpair)
        (pair_right_one_le hN hpair)
        C).right), by
      simp [ambientCells]⟩⟩

/-- Distinct residual components give distinct ambient labeled cells.
@isnad1 id=injectiv.2h5v.s6.8058404d42df from=translated src=- shape=11c0c8f3 vocab=0dd2b5c4
-/
theorem componentAmbientCell_injective
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    Function.Injective
      (componentAmbientCell
        (A := A) hN hpair :
        CanonicalResidualCertificateIndex A x y L →
          AmbientLabeledCell N L) := by
  intro C D hCD
  have hprime :
      (canonicalResidualCertificates
          (pair_left_one_le hN hpair)
          (pair_right_one_le hN hpair)
          C).prime =
        (canonicalResidualCertificates
          (pair_left_one_le hN hpair)
          (pair_right_one_le hN hpair)
          D).prime := by
    exact congrArg (fun z : AmbientLabeledCell N L ↦ z.1.1) hCD
  exact
    canonicalResidualCertificates_prime_injective
      (A := A) (L := L)
      (pair_left_one_le hN hpair)
      (pair_right_one_le hN hpair)
      hprime

/--
The image of the canonical residual components is an unordered certificate
inside the fixed ambient family, with exact size `c#`.-/
noncomputable def ambientCertificate
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    CRT.UnorderedCertificate
      (Finset.univ : Finset (AmbientLabeledCell N L))
      (canonicalResidualComponentCount A x y L) := by
  classical
  let T : Finset (AmbientLabeledCell N L) :=
    Finset.univ.image
      (componentAmbientCell (A := A) hN hpair)
  refine ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ T, ?_⟩⟩
  dsimp [T]
  rw [Finset.card_image_of_injective _
    (componentAmbientCell_injective (A := A) hN hpair)]
  simpa [ambientModulus, ambientPrimeModulus, ambientLeftResidue,
    componentAmbientCell, componentAmbientPrime,
    CRT.labeledCellModulus,
    canonicalResidualCertificateModulus,
    canonicalResidualCertificateLeftResidue] using
    card_canonicalResidualCertificateIndex
      (two_le_of_mem_dyadicBlock hN
        (mem_separatedDyadicPairs.mp hpair).1)
      (two_le_of_mem_dyadicBlock hN
        (mem_separatedDyadicPairs.mp hpair).2.1)

/--
@isnad1 id=eq.2h5v.s8.e98f9bd236a0 from=translated src=- shape=0a542a3c vocab=690dd8c2
-/
@[simp]
theorem ambientCertificate_coe
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    (ambientCertificate (A := A) hN hpair).1 =
      Finset.univ.image (componentAmbientCell (A := A) hN hpair) := by
  simp [ambientCertificate]

/--
@isnad1 id=eq.2h5v.s7.386f0944073f from=translated src=- shape=42b8824c vocab=06639e3b
-/
@[simp]
theorem ambientCertificate_card
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    (ambientCertificate (A := A) hN hpair).1.card =
      canonicalResidualComponentCount A x y L :=
  CRT.unorderedCertificate_card (ambientCertificate (A := A) hN hpair)

/--
@isnad1 id=eq.2h6v.s7.f143977fd98a from=translated src=- shape=6a958f61 vocab=a06e2821
-/
@[simp]
theorem ambientModulus_componentAmbientCell
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L)
    (C : CanonicalResidualCertificateIndex A x y L) :
    ambientModulus (componentAmbientCell hN hpair C) =
      (canonicalResidualCertificates
        (pair_left_one_le hN hpair)
        (pair_right_one_le hN hpair) C).prime := by
  rfl

/--
@isnad1 id=eq.2h6v.s6.d85fd81cbf77 from=translated src=- shape=4bc7af75 vocab=0a592925
-/
@[simp]
theorem ambientLeftResidue_componentAmbientCell
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L)
    (C : CanonicalResidualCertificateIndex A x y L) :
    ambientLeftResidue (componentAmbientCell hN hpair C) =
      canonicalResidualCertificateLeftResidue
        (pair_left_one_le hN hpair)
        (pair_right_one_le hN hpair) C := by
  rfl

/--
@isnad1 id=eq.2h6v.s6.a47fd47a11ee from=translated src=- shape=4bc7af75 vocab=f2b87dc9
-/
@[simp]
theorem ambientRightResidue_componentAmbientCell
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L)
    (C : CanonicalResidualCertificateIndex A x y L) :
    ambientRightResidue (componentAmbientCell hN hpair C) =
      canonicalResidualCertificateRightResidue
        (pair_left_one_le hN hpair)
        (pair_right_one_le hN hpair) C := by
  rfl

/--
Transport to the fixed ambient family preserves the complete modulus
product exactly.
@isnad1 id=eq.2h5v.s7.1d9cf63474e1 from=translated src=- shape=31f47279 vocab=a0119415
-/
theorem ambientCertificate_modulusProduct
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    CRT.certificateModulusProduct
        ambientModulus
        (ambientCertificate (A := A) hN hpair) =
      canonicalResidualPrimeProduct
        (A := A) (L := L)
        (pair_left_one_le hN hpair)
        (pair_right_one_le hN hpair) := by
  rw [canonicalResidualPrimeProduct_eq_product_certificates]
  simp only [CRT.certificateModulusProduct,
    ambientCertificate_coe]
  rw [Finset.prod_image]
  · simp
  · intro C _hC D _hD hCD
    exact componentAmbientCell_injective (A := A) hN hpair hCD

/-- The ambient modulus is injective on the transported certificate.
@isnad1 id=injon.2h5v.s7.8b610c4a919c from=translated src=- shape=aa5b9bbc vocab=c412091d
-/
theorem ambientModulus_injOn_ambientCertificate
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    Set.InjOn ambientModulus
      (↑(ambientCertificate (A := A) hN hpair).1 :
        Set (AmbientLabeledCell N L)) := by
  intro z hz w hw hmod
  rw [ambientCertificate_coe, Finset.mem_coe,
    Finset.mem_image] at hz hw
  obtain ⟨C, _hC, rfl⟩ := hz
  obtain ⟨D, _hD, rfl⟩ := hw
  have hCD :=
    canonicalResidualCertificates_prime_injective
      (A := A) (L := L)
      (pair_left_one_le hN hpair)
      (pair_right_one_le hN hpair)
      (by simpa using hmod)
  subst D
  rfl

/-- The transported certificate has pairwise distinct prime moduli.
@isnad1 id=pairwise.2h5v.s7.6ad77a85e7c1 from=translated src=- shape=7ad3c32f vocab=c17f453b
-/
theorem ambientCertificate_moduli_pairwise
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    (ambientCertificate (A := A) hN hpair).1.toList.Pairwise
      (fun z w ↦ ambientModulus z ≠ ambientModulus w) := by
  classical
  apply
    (ambientCertificate (A := A) hN hpair).1.nodup_toList
      |>.pairwise_of_forall_ne
  intro z hz w hw hzw hmod
  apply hzw
  exact
    ambientModulus_injOn_ambientCertificate hN hpair
      (by simpa using hz) (by simpa using hw) hmod

/--
Ambient admissibility is exactly the manuscript's small-product branch
`P# ≤ N`.
@isnad1 id=iff.2h5v.s7.847b20be672f from=translated src=- shape=64f2cf7f vocab=89bf3b00
-/
theorem ambientCertificate_admissible_iff
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    CRT.CertificateAdmissible
        ambientModulus N
        (ambientCertificate (A := A) hN hpair) ↔
      CanonicalResidualPrimeProductAtMost
        (A := A) (L := L)
        (pair_left_one_le hN hpair)
        (pair_right_one_le hN hpair) N := by
  unfold CRT.CertificateAdmissible
  unfold CanonicalResidualPrimeProductAtMost
  rw [ambientCertificate_modulusProduct hN hpair]
  constructor
  · exact fun h ↦ h.2
  · exact fun h ↦
      ⟨ambientCertificate_moduli_pairwise hN hpair, h⟩

/-! ## Satisfaction of the transported congruences -/

/-- The left start satisfies the ambient congruence of every component.
@isnad1 id=modeq.2h6v.s6.7a1901fa223d from=translated src=- shape=3f519548 vocab=837df899
-/
theorem left_modEq_componentAmbientCell
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L)
    (C : CanonicalResidualCertificateIndex A x y L) :
    x ≡ ambientLeftResidue (componentAmbientCell hN hpair C)
      [MOD ambientModulus (componentAmbientCell hN hpair C)] := by
  change x ≡ canonicalResidualCertificateLeftResidue
      (pair_left_one_le hN hpair) (pair_right_one_le hN hpair) C
    [MOD canonicalResidualCertificateModulus
      (pair_left_one_le hN hpair) (pair_right_one_le hN hpair) C]
  exact canonicalResidual_left_modEq
    (A := A) (L := L)
    (pair_left_one_le hN hpair)
    (pair_right_one_le hN hpair) C

/-- The right start satisfies the ambient congruence of every component.
@isnad1 id=modeq.2h6v.s6.fb34a2f951ad from=translated src=- shape=9a76e7bf vocab=87d53ab4
-/
theorem right_modEq_componentAmbientCell
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L)
    (C : CanonicalResidualCertificateIndex A x y L) :
    y ≡ ambientRightResidue (componentAmbientCell hN hpair C)
      [MOD ambientModulus (componentAmbientCell hN hpair C)] := by
  change y ≡ canonicalResidualCertificateRightResidue
      (pair_left_one_le hN hpair) (pair_right_one_le hN hpair) C
    [MOD canonicalResidualCertificateModulus
      (pair_left_one_le hN hpair) (pair_right_one_le hN hpair) C]
  exact canonicalResidual_right_modEq
    (A := A) (L := L)
    (pair_left_one_le hN hpair)
    (pair_right_one_le hN hpair) C

/-- The left start satisfies all congruences in the ambient certificate.
@isnad1 id=modeq.3h6v.s7.c04b68c7c930 from=translated src=- shape=778dfd1f vocab=34acc27f
-/
theorem left_satisfies_ambientCertificate
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    ∀ z ∈ (ambientCertificate (A := A) hN hpair).1.toList,
      x ≡ ambientLeftResidue z [MOD ambientModulus z] := by
  intro z hz
  have hzSet :
      z ∈ (ambientCertificate (A := A) hN hpair).1 := by
    simpa using hz
  rw [ambientCertificate_coe, Finset.mem_image] at hzSet
  obtain ⟨C, _hC, rfl⟩ := hzSet
  exact left_modEq_componentAmbientCell hN hpair C

/-- The right start satisfies all congruences in the ambient certificate.
@isnad1 id=modeq.3h6v.s7.5deb8a3f213d from=translated src=- shape=b0513fed vocab=3b0dfb15
-/
theorem right_satisfies_ambientCertificate
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    ∀ z ∈ (ambientCertificate (A := A) hN hpair).1.toList,
      y ≡ ambientRightResidue z [MOD ambientModulus z] := by
  intro z hz
  have hzSet :
      z ∈ (ambientCertificate (A := A) hN hpair).1 := by
    simpa using hz
  rw [ambientCertificate_coe, Finset.mem_image] at hzSet
  obtain ⟨C, _hC, rfl⟩ := hzSet
  exact right_modEq_componentAmbientCell hN hpair C

/--
Every separated dyadic pair belongs to the rectangular CRT solution set of
its transported ambient certificate.
@isnad1 id=mem.4h9v.s11.40e8ba57b7f5 from=translated src=- shape=76cc8fc6 vocab=83fb625a
-/
theorem pair_mem_ambientCertificateSolutions
    {N A x y L a₁ b₁ a₂ b₂ : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L)
    (hxI : x ∈ Finset.Ico a₁ b₁)
    (hyI : y ∈ Finset.Ico a₂ b₂) :
    (x, y) ∈
      (({z ∈ Finset.Ico a₁ b₁ |
          ∀ i ∈ (ambientCertificate
              (A := A) hN hpair).1.toList,
            z ≡ ambientLeftResidue i [MOD ambientModulus i]}) ×ˢ
        {z ∈ Finset.Ico a₂ b₂ |
          ∀ i ∈ (ambientCertificate
              (A := A) hN hpair).1.toList,
            z ≡ ambientRightResidue i [MOD ambientModulus i]}) := by
  rw [Finset.mem_product]
  constructor
  · rw [Finset.mem_filter]
    exact ⟨hxI, left_satisfies_ambientCertificate hN hpair⟩
  · rw [Finset.mem_filter]
    exact ⟨hyI, right_satisfies_ambientCertificate hN hpair⟩

/--
In particular, the dyadic pair is counted by the two-dimensional solution
count attached to its ambient certificate.
@isnad1 id=le.2h5v.s8.f8359f106dd9 from=translated src=- shape=ba893ffc vocab=dc7c99cd
-/
theorem one_le_ambientCertificate_pairSolutionCount
    {N A x y L : ℕ}
    (hN : 2 ≤ N)
    (hpair : (x, y) ∈ separatedDyadicPairs N L) :
    1 ≤
      CRT.certificatePairSolutionCount
        ambientLeftResidue ambientRightResidue ambientModulus
        N (2 * N) N (2 * N)
        (ambientCertificate (A := A) hN hpair) := by
  unfold CRT.certificatePairSolutionCount
  apply Finset.one_le_card.mpr
  exact
    ⟨(x, y),
      pair_mem_ambientCertificateSolutions hN hpair
        (mem_separatedDyadicPairs.mp hpair).1
        (mem_separatedDyadicPairs.mp hpair).2.1⟩

end

end SigmaZeroAmbientCertificate
end PaperC
