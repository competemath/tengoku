import Tengoku.PaperCLean.PaperC.Combinatorics.ResidualMasses

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 1800000

/-!
# The small-height large-product population

This file defines the finite population occurring in Proposition 7.4 of
Paper C.  Its members are separated ordered pairs in the dyadic block such
that

* the canonical residual prime product satisfies `N < P#`;
* a canonical reduced candidate `(a,b)` has been selected; and
* its height `q = max(a,b)` satisfies the manuscript's literal condition
  `q ≤ √(log B)`, where `B = L+1`.

The real inequality is retained verbatim rather than replacing it by a
rounded natural logarithm.  We then delete the pairs with `τ=0`, split the
active population exactly into `σ=0` and `σ>0`, and define its linear and
quadratic residual masses using the generic infrastructure from
`ResidualMasses`.

Finally, every active `σ=0` pair is placed in the relational-host population.
This is the cardinality input used in the Cauchy--Schwarz step of Proposition
7.4.
-/

namespace PaperC
namespace SmallHeightLargeProductPairs

open Affine
open Affine.CanonicalRationalCode
open CanonicalResidualComponents
open RationalMassFinite
open ResidualMasses

noncomputable section

/--
A canonical reduced candidate exists and has manuscript height
`q = max(a,b) ≤ √(log (L+1))`.

The existential witness retains both the selected candidate and the proof
that it is the canonical choice.  This avoids treating the default value
`canonicalPairHeight = 0` as if it represented an actual channel.-/
def HasSmallCanonicalHeight
    (A L x y : ℕ) : Prop :=
  ∃ c : ReducedCandidate x y (L + 1) ((L + 1) ^ A),
    canonicalReducedCandidate?
        x y (L + 1) ((L + 1) ^ A) = some c ∧
      ((Nat.max c.1.1 c.1.2 : ℕ) : ℝ) ≤
        Real.sqrt (Real.log ((L + 1 : ℕ) : ℝ))

/--
All separated pairs in the large-product, small-canonical-height sector of
Proposition 7.4.-/
noncomputable def smallHeightLargeProductPairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact Finset.univ.filter fun pair ↦
    CanonicalResidualPrimeProductExceeds
        (A := A) (L := L)
        (show 1 ≤ pair.1.1 by
          exact le_trans (by omega : 1 ≤ 2)
            (pair_coordinates_two_le hN pair).1)
        (show 1 ≤ pair.1.2 by
          exact le_trans (by omega : 1 ≤ 2)
            (pair_coordinates_two_le hN pair).2)
        N ∧
      HasSmallCanonicalHeight A L pair.1.1 pair.1.2

/--
@isnad1 id=iff.1h4v.s8.ab41cebbd9d5 from=translated src=- shape=3b3a8912 vocab=0083352c
-/
@[simp]
theorem mem_smallHeightLargeProductPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ smallHeightLargeProductPairs N A L hN ↔
      CanonicalResidualPrimeProductExceeds
          (A := A) (L := L)
          (show 1 ≤ pair.1.1 by
            exact le_trans (by omega : 1 ≤ 2)
              (pair_coordinates_two_le hN pair).1)
          (show 1 ≤ pair.1.2 by
            exact le_trans (by omega : 1 ≤ 2)
              (pair_coordinates_two_le hN pair).2)
          N ∧
        HasSmallCanonicalHeight A L pair.1.1 pair.1.2 := by
  simp [smallHeightLargeProductPairs]

/-- Every member exposes its selected small-height canonical candidate.
@isnad1 id=ex.2h4v.s9.75e0e439eb1f from=translated src=- shape=7d2e56d6 vocab=8b826dbf
-/
theorem exists_smallHeight_candidate_of_mem
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ smallHeightLargeProductPairs N A L hN) :
    ∃ c :
        ReducedCandidate pair.1.1 pair.1.2
          (L + 1) ((L + 1) ^ A),
      canonicalReducedCandidate?
          pair.1.1 pair.1.2 (L + 1) ((L + 1) ^ A) =
        some c ∧
      ((Nat.max c.1.1 c.1.2 : ℕ) : ℝ) ≤
        Real.sqrt (Real.log ((L + 1 : ℕ) : ℝ)) :=
  (mem_smallHeightLargeProductPairs.mp hpair).2

/--
The active part of the sector.  Removing `τ=0` does not change either
residual mass.-/
noncomputable def activeSmallHeightLargeProductPairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact (smallHeightLargeProductPairs N A L hN).filter fun pair ↦
    0 < pairTau A hN pair

/--
@isnad1 id=iff.1h4v.s6.82bacc4325e2 from=translated src=- shape=b2b65813 vocab=b84adda8
-/
@[simp]
theorem mem_activeSmallHeightLargeProductPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ activeSmallHeightLargeProductPairs N A L hN ↔
      pair ∈ smallHeightLargeProductPairs N A L hN ∧
        0 < pairTau A hN pair := by
  simp [activeSmallHeightLargeProductPairs]

/--
@isnad1 id=le.1h3v.s5.182e9be2e1d1 from=translated src=- shape=5aca9b93 vocab=65a314ae
-/
theorem activeSmallHeightLargeProductPairs_subset
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeSmallHeightLargeProductPairs N A L hN ⊆
      smallHeightLargeProductPairs N A L hN :=
  Finset.filter_subset _ _

/-! ## The `σ=0` and `σ>0` branches -/

/-- Active pairs in the exceptional branch `σ=0`.-/
noncomputable def sigmaZeroSmallHeightLargeProductPairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact
    (activeSmallHeightLargeProductPairs N A L hN).filter fun pair ↦
      pairSigma A pair = 0

/-- Active pairs carried by a positive systematic rational code.-/
noncomputable def positiveSigmaSmallHeightLargeProductPairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact
    (activeSmallHeightLargeProductPairs N A L hN).filter fun pair ↦
      0 < pairSigma A pair

/--
@isnad1 id=iff.1h4v.s6.1b5989bb09c5 from=translated src=- shape=6bf6bf9b vocab=fdf34969
-/
@[simp]
theorem mem_sigmaZeroSmallHeightLargeProductPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ sigmaZeroSmallHeightLargeProductPairs N A L hN ↔
      pair ∈ activeSmallHeightLargeProductPairs N A L hN ∧
        pairSigma A pair = 0 := by
  simp [sigmaZeroSmallHeightLargeProductPairs]

/--
@isnad1 id=iff.1h4v.s6.b477eb8e3789 from=translated src=- shape=43cd91ac vocab=d53d9d6d
-/
@[simp]
theorem mem_positiveSigmaSmallHeightLargeProductPairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ positiveSigmaSmallHeightLargeProductPairs N A L hN ↔
      pair ∈ activeSmallHeightLargeProductPairs N A L hN ∧
        0 < pairSigma A pair := by
  simp [positiveSigmaSmallHeightLargeProductPairs]

/--
@isnad1 id=disjoint.1h3v.s5.b4e88bedaac1 from=translated src=- shape=57e17e57 vocab=8a74389d
-/
theorem disjoint_sigmaZero_positiveSigmaSmallHeightLargeProductPairs
    {N A L : ℕ} (hN : 2 ≤ N) :
    Disjoint
      (sigmaZeroSmallHeightLargeProductPairs N A L hN)
      (positiveSigmaSmallHeightLargeProductPairs N A L hN) := by
  rw [Finset.disjoint_left]
  intro pair hzero hpositive
  rw [mem_sigmaZeroSmallHeightLargeProductPairs] at hzero
  rw [mem_positiveSigmaSmallHeightLargeProductPairs] at hpositive
  omega

/--
@isnad1 id=eq.1h3v.s6.810519c5a9d3 from=translated src=- shape=5a1e8b88 vocab=0f3740e1
-/
theorem sigmaZero_union_positiveSigma_eq_activeSmallHeightLargeProductPairs
    {N A L : ℕ} (hN : 2 ≤ N) :
    sigmaZeroSmallHeightLargeProductPairs N A L hN ∪
        positiveSigmaSmallHeightLargeProductPairs N A L hN =
      activeSmallHeightLargeProductPairs N A L hN := by
  ext pair
  simp only [Finset.mem_union,
    mem_sigmaZeroSmallHeightLargeProductPairs,
    mem_positiveSigmaSmallHeightLargeProductPairs]
  constructor
  · rintro (hzero | hpositive)
    · exact hzero.1
    · exact hpositive.1
  · intro hactive
    by_cases hzero : pairSigma A pair = 0
    · exact Or.inl ⟨hactive, hzero⟩
    · exact Or.inr ⟨hactive, Nat.pos_of_ne_zero hzero⟩

/-! ## Literal residual masses of the sector -/

/-- Quadratic residual mass on the full Proposition 7.4 population.-/
noncomputable def smallHeightLargeProductQuadraticResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  quadraticResidualMass A hN
    (smallHeightLargeProductPairs N A L hN)

/-- Linear residual mass on the full Proposition 7.4 population.-/
noncomputable def smallHeightLargeProductLinearResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass A hN
    (smallHeightLargeProductPairs N A L hN)

/-- Quadratic residual mass after deleting the zero-weight pairs.-/
noncomputable def activeSmallHeightLargeProductQuadraticResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  quadraticResidualMass A hN
    (activeSmallHeightLargeProductPairs N A L hN)

/-- Linear residual mass after deleting the zero-weight pairs.-/
noncomputable def activeSmallHeightLargeProductLinearResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass A hN
    (activeSmallHeightLargeProductPairs N A L hN)

/-- Quadratic contribution of the `σ=0` branch.-/
noncomputable def sigmaZeroSmallHeightLargeProductQuadraticResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  quadraticResidualMass A hN
    (sigmaZeroSmallHeightLargeProductPairs N A L hN)

/-- Linear contribution of the `σ=0` branch.-/
noncomputable def sigmaZeroSmallHeightLargeProductLinearResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass A hN
    (sigmaZeroSmallHeightLargeProductPairs N A L hN)

/-- Quadratic contribution of the `σ>0` branch.-/
noncomputable def positiveSigmaSmallHeightLargeProductQuadraticResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  quadraticResidualMass A hN
    (positiveSigmaSmallHeightLargeProductPairs N A L hN)

/-- Linear contribution of the `σ>0` branch.-/
noncomputable def positiveSigmaSmallHeightLargeProductLinearResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass A hN
    (positiveSigmaSmallHeightLargeProductPairs N A L hN)

/-- Deleting `τ=0` does not change the quadratic residual mass.
@isnad1 id=eq.1h3v.s4.05ebd0786ac1 from=translated src=- shape=cf7e9bf1 vocab=d1a08edd
-/
theorem smallHeightLargeProductQuadraticResidualMass_eq_active
    {N A L : ℕ} (hN : 2 ≤ N) :
    smallHeightLargeProductQuadraticResidualMass N A L hN =
      activeSmallHeightLargeProductQuadraticResidualMass N A L hN := by
  classical
  unfold smallHeightLargeProductQuadraticResidualMass
  unfold activeSmallHeightLargeProductQuadraticResidualMass
  unfold quadraticResidualMass
  symm
  apply Finset.sum_subset
    (activeSmallHeightLargeProductPairs_subset (A := A) hN)
  intro pair hpair hpairNotActive
  have htau : pairTau A hN pair = 0 := by
    have hnotPos : ¬ 0 < pairTau A hN pair := by
      intro hpos
      exact hpairNotActive
        (mem_activeSmallHeightLargeProductPairs.mpr
          ⟨hpair, hpos⟩)
    omega
  exact quadraticResidualWeight_eq_zero_of_pairTau_eq_zero htau

/-- Deleting `τ=0` does not change the linear residual mass.
@isnad1 id=eq.1h3v.s4.326ed4c26495 from=translated src=- shape=cf7e9bf1 vocab=16ca0ab4
-/
theorem smallHeightLargeProductLinearResidualMass_eq_active
    {N A L : ℕ} (hN : 2 ≤ N) :
    smallHeightLargeProductLinearResidualMass N A L hN =
      activeSmallHeightLargeProductLinearResidualMass N A L hN := by
  classical
  unfold smallHeightLargeProductLinearResidualMass
  unfold activeSmallHeightLargeProductLinearResidualMass
  unfold linearResidualMass
  symm
  apply Finset.sum_subset
    (activeSmallHeightLargeProductPairs_subset (A := A) hN)
  intro pair hpair hpairNotActive
  have htau : pairTau A hN pair = 0 := by
    have hnotPos : ¬ 0 < pairTau A hN pair := by
      intro hpos
      exact hpairNotActive
        (mem_activeSmallHeightLargeProductPairs.mpr
          ⟨hpair, hpos⟩)
    omega
  exact linearResidualWeight_eq_zero_of_pairTau_eq_zero htau

/-- Exact decomposition of the active quadratic mass.
@isnad1 id=eq.1h3v.s5.6b2114e057d0 from=translated src=- shape=588e1398 vocab=f7a8ce35
-/
theorem activeSmallHeightLargeProductQuadraticResidualMass_eq_branches
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeSmallHeightLargeProductQuadraticResidualMass N A L hN =
      sigmaZeroSmallHeightLargeProductQuadraticResidualMass N A L hN +
        positiveSigmaSmallHeightLargeProductQuadraticResidualMass
          N A L hN := by
  rw [activeSmallHeightLargeProductQuadraticResidualMass]
  rw [← sigmaZero_union_positiveSigma_eq_activeSmallHeightLargeProductPairs
    (A := A) hN]
  unfold sigmaZeroSmallHeightLargeProductQuadraticResidualMass
  unfold positiveSigmaSmallHeightLargeProductQuadraticResidualMass
  unfold quadraticResidualMass
  exact Finset.sum_union
    (disjoint_sigmaZero_positiveSigmaSmallHeightLargeProductPairs
      (A := A) hN)

/-- Exact decomposition of the active linear mass.
@isnad1 id=eq.1h3v.s5.22b0cc656854 from=translated src=- shape=588e1398 vocab=6bc43f7f
-/
theorem activeSmallHeightLargeProductLinearResidualMass_eq_branches
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeSmallHeightLargeProductLinearResidualMass N A L hN =
      sigmaZeroSmallHeightLargeProductLinearResidualMass N A L hN +
        positiveSigmaSmallHeightLargeProductLinearResidualMass
          N A L hN := by
  rw [activeSmallHeightLargeProductLinearResidualMass]
  rw [← sigmaZero_union_positiveSigma_eq_activeSmallHeightLargeProductPairs
    (A := A) hN]
  unfold sigmaZeroSmallHeightLargeProductLinearResidualMass
  unfold positiveSigmaSmallHeightLargeProductLinearResidualMass
  unfold linearResidualMass
  exact Finset.sum_union
    (disjoint_sigmaZero_positiveSigmaSmallHeightLargeProductPairs
      (A := A) hN)

/-- Exact decomposition of the full quadratic mass.
@isnad1 id=eq.1h3v.s5.f9b17afb7023 from=translated src=- shape=588e1398 vocab=4b531eb5
-/
theorem smallHeightLargeProductQuadraticResidualMass_eq_branches
    {N A L : ℕ} (hN : 2 ≤ N) :
    smallHeightLargeProductQuadraticResidualMass N A L hN =
      sigmaZeroSmallHeightLargeProductQuadraticResidualMass N A L hN +
        positiveSigmaSmallHeightLargeProductQuadraticResidualMass
          N A L hN := by
  rw [smallHeightLargeProductQuadraticResidualMass_eq_active hN]
  exact
    activeSmallHeightLargeProductQuadraticResidualMass_eq_branches
      (A := A) hN

/-- Exact decomposition of the full linear mass.
@isnad1 id=eq.1h3v.s5.3840ea80715d from=translated src=- shape=588e1398 vocab=bc3c8d13
-/
theorem smallHeightLargeProductLinearResidualMass_eq_branches
    {N A L : ℕ} (hN : 2 ≤ N) :
    smallHeightLargeProductLinearResidualMass N A L hN =
      sigmaZeroSmallHeightLargeProductLinearResidualMass N A L hN +
        positiveSigmaSmallHeightLargeProductLinearResidualMass
          N A L hN := by
  rw [smallHeightLargeProductLinearResidualMass_eq_active hN]
  exact
    activeSmallHeightLargeProductLinearResidualMass_eq_branches
      (A := A) hN

/-! ## Relational-host inclusion of the active `σ=0` branch -/

/-- The `σ=0` branch viewed as ordinary ordered pairs.-/
noncomputable def sigmaZeroSmallHeightLargeProductPairValues
    (N A L : ℕ) (hN : 2 ≤ N) : Finset (ℕ × ℕ) :=
  (sigmaZeroSmallHeightLargeProductPairs N A L hN).image Subtype.val

/--
@isnad1 id=eq.1h3v.s5.8e907636f134 from=translated src=- shape=76232444 vocab=3f66467d
-/
theorem card_sigmaZeroSmallHeightLargeProductPairValues
    (N A L : ℕ) (hN : 2 ≤ N) :
    (sigmaZeroSmallHeightLargeProductPairValues N A L hN).card =
      (sigmaZeroSmallHeightLargeProductPairs N A L hN).card := by
  unfold sigmaZeroSmallHeightLargeProductPairValues
  exact Finset.card_image_of_injective
    (sigmaZeroSmallHeightLargeProductPairs N A L hN)
    Subtype.val_injective

/-- Every active `σ=0` pair has positive relation rank.
@isnad1 id=mem.2h4v.s6.854becec273a from=translated src=- shape=246bcfd2 vocab=ed477cf7
-/
theorem pair_mem_relationalHosts_of_mem_sigmaZero
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair :
      pair ∈ sigmaZeroSmallHeightLargeProductPairs N A L hN) :
    pair.1 ∈ RelationalHosts.relationalHosts N L := by
  have hbranch :=
    mem_sigmaZeroSmallHeightLargeProductPairs.mp hpair
  have hactive :=
    mem_activeSmallHeightLargeProductPairs.mp hbranch.1
  have hsep := mem_separatedDyadicPairs.mp pair.2
  rw [RelationalHosts.mem_relationalHosts]
  refine ⟨hsep.1, hsep.2.1, hsep.2.2, ?_⟩
  have hrho :=
    pairRho_eq_pairSigma_add_pairTau
      (A := A) hN pair
  unfold pairRho at hrho
  calc
    0 < pairSigma A pair + pairTau A hN pair := by
      omega
    _ =
        relationRho
          (twoStartSystem
            (dyadicCutoff N L) pair.1.1 pair.1.2 L) :=
      hrho.symm

/-- Finset-level inclusion in the relational-host population.
@isnad1 id=le.1h3v.s5.11f3e65053ab from=translated src=- shape=b02151f2 vocab=3b4217d3
-/
theorem sigmaZeroSmallHeightLargeProductPairValues_subset_relationalHosts
    {N A L : ℕ} (hN : 2 ≤ N) :
    sigmaZeroSmallHeightLargeProductPairValues N A L hN ⊆
      RelationalHosts.relationalHosts N L := by
  intro pair hpair
  rw [sigmaZeroSmallHeightLargeProductPairValues,
    Finset.mem_image] at hpair
  obtain ⟨z, hz, rfl⟩ := hpair
  exact pair_mem_relationalHosts_of_mem_sigmaZero hz

/-- Cardinality bound inherited from Lemma 4.2.
@isnad1 id=le.1h3v.s5.fa5783b299ff from=translated src=- shape=8e93b465 vocab=985bd5d1
-/
theorem card_sigmaZeroSmallHeightLargeProductPairs_le_relationalHosts
    {N A L : ℕ} (hN : 2 ≤ N) :
    (sigmaZeroSmallHeightLargeProductPairs N A L hN).card ≤
      (RelationalHosts.relationalHosts N L).card := by
  rw [← card_sigmaZeroSmallHeightLargeProductPairValues N A L hN]
  exact Finset.card_le_card
    (sigmaZeroSmallHeightLargeProductPairValues_subset_relationalHosts
      (A := A) hN)

end

end SmallHeightLargeProductPairs
end PaperC
