import Tengoku.PaperCLean.PaperC.Combinatorics.SmallHeightLargeProductPairs
import Tengoku.PaperCLean.PaperC.Combinatorics.TouchingPairs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 1800000

/-!
# The shallow-core population

This file defines the literal finite population occurring in Proposition 7.5
of Paper C.  Its members are separated ordered pairs such that

* the canonical residual prime product satisfies `N < P#`;
* the pair does not belong to the small-canonical-height sector of
  Proposition 7.4; and
* the residual component count satisfies the division-free density condition
  `16 * c# ≤ 3 * (L+1)`.

Thus the natural envelope for `c#` is `3 * (L+1) / 16`.  We remove the
zero-residual pairs, define the literal linear and quadratic masses, and show
that the active population embeds in the relational hosts.  We also expose
the finite maximum of the systematic exponent `σ`; the separate asymptotic
module will prove that its fourth power is subpolynomial.
-/

namespace PaperC
namespace ShallowCorePairs

open Affine
open Affine.CanonicalRationalCode
open CanonicalResidualComponents
open RationalMassFinite
open ResidualComponentCounts
open ResidualMasses
open SmallHeightLargeProductPairs

noncomputable section

/--
The exact integer form of `c# ≤ 3(L+1)/16`.

Using a multiplication inequality avoids rounding ambiguity in the statement
of Proposition 7.5.-/
def HasCoreDensityAtMostThreeSixteenths
    (A L x y : ℕ) : Prop :=
  16 * canonicalResidualComponentCount A x y L ≤
    3 * (L + 1)

/-- The rounded natural envelope forced by the density condition.-/
def shallowCoreComponentEnvelope (L : ℕ) : ℕ :=
  3 * (L + 1) / 16

/--
All separated pairs in the large-product, non-small-height,
low-residual-density sector of Proposition 7.5.-/
noncomputable def shallowCorePairs
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
      ¬ HasSmallCanonicalHeight A L pair.1.1 pair.1.2 ∧
      HasCoreDensityAtMostThreeSixteenths
        A L pair.1.1 pair.1.2

/--
@isnad1 id=iff.1h4v.s8.5be0d6844043 from=translated src=- shape=edb2a313 vocab=abd57e0b
-/
@[simp]
theorem mem_shallowCorePairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ shallowCorePairs N A L hN ↔
      CanonicalResidualPrimeProductExceeds
          (A := A) (L := L)
          (show 1 ≤ pair.1.1 by
            exact le_trans (by omega : 1 ≤ 2)
              (pair_coordinates_two_le hN pair).1)
          (show 1 ≤ pair.1.2 by
            exact le_trans (by omega : 1 ≤ 2)
              (pair_coordinates_two_le hN pair).2)
          N ∧
        ¬ HasSmallCanonicalHeight A L pair.1.1 pair.1.2 ∧
        HasCoreDensityAtMostThreeSixteenths
          A L pair.1.1 pair.1.2 := by
  simp [shallowCorePairs]

/--
The density condition gives the rounded component envelope used in the
finite mass estimate.
@isnad1 id=le.2h4v.s6.5f7570c52b4a from=translated src=- shape=943ae8e9 vocab=3ed5453a
-/
theorem canonicalResidualComponentCount_le_envelope_of_mem
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ shallowCorePairs N A L hN) :
    canonicalResidualComponentCount
        A pair.1.1 pair.1.2 L ≤
      shallowCoreComponentEnvelope L := by
  have hdensity :=
    (mem_shallowCorePairs.mp hpair).2.2
  unfold HasCoreDensityAtMostThreeSixteenths at hdensity
  unfold shallowCoreComponentEnvelope
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 16)).2
  simpa only [Nat.mul_comm] using hdensity

/-- The active part of Proposition 7.5, obtained by deleting `τ=0`.-/
noncomputable def activeShallowCorePairs
    (N A L : ℕ) (hN : 2 ≤ N) :
    Finset (SeparatedDyadicPair N L) := by
  classical
  exact (shallowCorePairs N A L hN).filter fun pair ↦
    0 < pairTau A hN pair

/--
@isnad1 id=iff.1h4v.s6.5696fb03f6af from=translated src=- shape=b2b65813 vocab=a5460a5e
-/
@[simp]
theorem mem_activeShallowCorePairs
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L} :
    pair ∈ activeShallowCorePairs N A L hN ↔
      pair ∈ shallowCorePairs N A L hN ∧
        0 < pairTau A hN pair := by
  simp [activeShallowCorePairs]

/--
@isnad1 id=le.1h3v.s5.50ce04bef922 from=translated src=- shape=5aca9b93 vocab=cb3ebb0a
-/
theorem activeShallowCorePairs_subset
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeShallowCorePairs N A L hN ⊆
      shallowCorePairs N A L hN :=
  Finset.filter_subset _ _

/-! ## Literal residual masses -/

/-- Quadratic residual mass on the full Proposition 7.5 population.-/
noncomputable def shallowCoreQuadraticResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  quadraticResidualMass A hN (shallowCorePairs N A L hN)

/-- Linear residual mass on the full Proposition 7.5 population.-/
noncomputable def shallowCoreLinearResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass A hN (shallowCorePairs N A L hN)

/-- Quadratic residual mass after deleting the zero-weight pairs.-/
noncomputable def activeShallowCoreQuadraticResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  quadraticResidualMass A hN (activeShallowCorePairs N A L hN)

/-- Linear residual mass after deleting the zero-weight pairs.-/
noncomputable def activeShallowCoreLinearResidualMass
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  linearResidualMass A hN (activeShallowCorePairs N A L hN)

/-- Deleting `τ=0` does not change the quadratic residual mass.
@isnad1 id=eq.1h3v.s4.b1f5f15969b9 from=translated src=- shape=cf7e9bf1 vocab=2f3b741b
-/
theorem shallowCoreQuadraticResidualMass_eq_active
    {N A L : ℕ} (hN : 2 ≤ N) :
    shallowCoreQuadraticResidualMass N A L hN =
      activeShallowCoreQuadraticResidualMass N A L hN := by
  classical
  unfold shallowCoreQuadraticResidualMass
  unfold activeShallowCoreQuadraticResidualMass
  unfold quadraticResidualMass
  symm
  apply Finset.sum_subset
    (activeShallowCorePairs_subset (A := A) hN)
  intro pair hpair hpairNotActive
  have htau : pairTau A hN pair = 0 := by
    have hnotPos : ¬ 0 < pairTau A hN pair := by
      intro hpos
      exact hpairNotActive
        (mem_activeShallowCorePairs.mpr ⟨hpair, hpos⟩)
    omega
  exact quadraticResidualWeight_eq_zero_of_pairTau_eq_zero htau

/-- Deleting `τ=0` does not change the linear residual mass.
@isnad1 id=eq.1h3v.s4.8ed1183ad738 from=translated src=- shape=cf7e9bf1 vocab=9a697119
-/
theorem shallowCoreLinearResidualMass_eq_active
    {N A L : ℕ} (hN : 2 ≤ N) :
    shallowCoreLinearResidualMass N A L hN =
      activeShallowCoreLinearResidualMass N A L hN := by
  classical
  unfold shallowCoreLinearResidualMass
  unfold activeShallowCoreLinearResidualMass
  unfold linearResidualMass
  symm
  apply Finset.sum_subset
    (activeShallowCorePairs_subset (A := A) hN)
  intro pair hpair hpairNotActive
  have htau : pairTau A hN pair = 0 := by
    have hnotPos : ¬ 0 < pairTau A hN pair := by
      intro hpos
      exact hpairNotActive
        (mem_activeShallowCorePairs.mpr ⟨hpair, hpos⟩)
    omega
  exact linearResidualWeight_eq_zero_of_pairTau_eq_zero htau

/-! ## Crude `N²` population bound -/

/-- The full shallow-core population viewed as ordinary ordered pairs.-/
noncomputable def shallowCorePairValues
    (N A L : ℕ) (hN : 2 ≤ N) : Finset (ℕ × ℕ) :=
  (shallowCorePairs N A L hN).image Subtype.val

/--
@isnad1 id=eq.1h3v.s5.5ee0d3d46bbf from=translated src=- shape=76232444 vocab=d992120c
-/
theorem card_shallowCorePairValues
    (N A L : ℕ) (hN : 2 ≤ N) :
    (shallowCorePairValues N A L hN).card =
      (shallowCorePairs N A L hN).card := by
  unfold shallowCorePairValues
  exact Finset.card_image_of_injective
    (shallowCorePairs N A L hN) Subtype.val_injective

/--
@isnad1 id=le.1h3v.s5.29609f810159 from=translated src=- shape=a4458e33 vocab=445c5454
-/
theorem shallowCorePairValues_subset_dyadicProduct
    {N A L : ℕ} (hN : 2 ≤ N) :
    shallowCorePairValues N A L hN ⊆
      dyadicBlock N ×ˢ dyadicBlock N := by
  intro pair hpair
  rw [shallowCorePairValues, Finset.mem_image] at hpair
  obtain ⟨z, _hz, rfl⟩ := hpair
  have hsep := mem_separatedDyadicPairs.mp z.2
  exact Finset.mem_product.mpr ⟨hsep.1, hsep.2.1⟩

/-- Proposition 7.5 contains at most `N²` ordered pairs.
@isnad1 id=le.1h3v.s5.e5d157e4f751 from=translated src=- shape=5e08b386 vocab=e08bada9
-/
theorem card_shallowCorePairs_le_sq
    {N A L : ℕ} (hN : 2 ≤ N) :
    (shallowCorePairs N A L hN).card ≤ N ^ 2 := by
  rw [← card_shallowCorePairValues N A L hN]
  calc
    (shallowCorePairValues N A L hN).card ≤
        (dyadicBlock N ×ˢ dyadicBlock N).card :=
      Finset.card_le_card
        (shallowCorePairValues_subset_dyadicProduct
          (A := A) hN)
    _ = N ^ 2 := by
      rw [Finset.card_product, TouchingPairs.card_dyadicBlock]
      ring

/-! ## Relational-host inclusion and finite interpolation -/

/-- The active population viewed as ordinary ordered pairs.-/
noncomputable def activeShallowCorePairValues
    (N A L : ℕ) (hN : 2 ≤ N) : Finset (ℕ × ℕ) :=
  (activeShallowCorePairs N A L hN).image Subtype.val

/--
@isnad1 id=eq.1h3v.s5.e5fe0de837be from=translated src=- shape=76232444 vocab=a9a149e8
-/
theorem card_activeShallowCorePairValues
    (N A L : ℕ) (hN : 2 ≤ N) :
    (activeShallowCorePairValues N A L hN).card =
      (activeShallowCorePairs N A L hN).card := by
  unfold activeShallowCorePairValues
  exact Finset.card_image_of_injective
    (activeShallowCorePairs N A L hN) Subtype.val_injective

/-- Every active shallow-core pair has positive relation rank.
@isnad1 id=mem.2h4v.s6.05197277d192 from=translated src=- shape=246bcfd2 vocab=11edd425
-/
theorem pair_mem_relationalHosts_of_mem_active
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ activeShallowCorePairs N A L hN) :
    pair.1 ∈ RelationalHosts.relationalHosts N L := by
  have hactive := mem_activeShallowCorePairs.mp hpair
  have hsep := mem_separatedDyadicPairs.mp pair.2
  rw [RelationalHosts.mem_relationalHosts]
  refine ⟨hsep.1, hsep.2.1, hsep.2.2, ?_⟩
  have hrho :=
    pairRho_eq_pairSigma_add_pairTau (A := A) hN pair
  unfold pairRho at hrho
  calc
    0 < pairSigma A pair + pairTau A hN pair := by omega
    _ =
        relationRho
          (twoStartSystem
            (dyadicCutoff N L) pair.1.1 pair.1.2 L) :=
      hrho.symm

/--
@isnad1 id=le.1h3v.s5.84a9cce46f80 from=translated src=- shape=b02151f2 vocab=d589a936
-/
theorem activeShallowCorePairValues_subset_relationalHosts
    {N A L : ℕ} (hN : 2 ≤ N) :
    activeShallowCorePairValues N A L hN ⊆
      RelationalHosts.relationalHosts N L := by
  intro pair hpair
  rw [activeShallowCorePairValues, Finset.mem_image] at hpair
  obtain ⟨z, hz, rfl⟩ := hpair
  exact pair_mem_relationalHosts_of_mem_active hz

/--
@isnad1 id=le.1h3v.s5.399d8d197099 from=translated src=- shape=8e93b465 vocab=c9b8dbd7
-/
theorem card_activeShallowCorePairs_le_relationalHosts
    {N A L : ℕ} (hN : 2 ≤ N) :
    (activeShallowCorePairs N A L hN).card ≤
      (RelationalHosts.relationalHosts N L).card := by
  rw [← card_activeShallowCorePairValues N A L hN]
  exact Finset.card_le_card
    (activeShallowCorePairValues_subset_relationalHosts
      (A := A) hN)

/-- Equation (6.6) on the exact Proposition 7.5 population.
@isnad1 id=le.1h3v.s5.f73e953dafa5 from=translated src=- shape=84104160 vocab=0c7e4028
-/
theorem shallowCoreLinearResidualMass_cast_le
    {N A L : ℕ} (hN : 2 ≤ N) :
    (shallowCoreLinearResidualMass N A L hN : ℝ) ≤
      Real.sqrt ((RelationalHosts.relationalHosts N L).card : ℝ) *
        Real.sqrt (shallowCoreQuadraticResidualMass N A L hN : ℝ) := by
  have hinterp :=
    linearResidualMass_cast_le_sqrt_card_mul_sqrt_quadratic
      (A := A) hN (activeShallowCorePairs N A L hN)
  have hcard :
      ((activeShallowCorePairs N A L hN).card : ℝ) ≤
        ((RelationalHosts.relationalHosts N L).card : ℝ) := by
    exact_mod_cast card_activeShallowCorePairs_le_relationalHosts
      (A := A) hN
  rw [shallowCoreLinearResidualMass_eq_active hN]
  rw [shallowCoreQuadraticResidualMass_eq_active hN]
  unfold activeShallowCoreLinearResidualMass
  unfold activeShallowCoreQuadraticResidualMass
  exact hinterp.trans
    (mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt hcard)
      (Real.sqrt_nonneg _))

/-! ## The systematic exponent envelope -/

/-- Largest systematic exponent `σ` on the full Proposition 7.5 sector.-/
noncomputable def maxShallowCoreSigma
    (N A L : ℕ) (hN : 2 ≤ N) : ℕ :=
  (shallowCorePairs N A L hN).sup fun pair ↦ pairSigma A pair

/--
@isnad1 id=le.2h4v.s5.e40ea3a7b040 from=translated src=- shape=9e9913df vocab=cf700a62
-/
theorem pairSigma_le_maxShallowCoreSigma
    {N A L : ℕ} {hN : 2 ≤ N}
    {pair : SeparatedDyadicPair N L}
    (hpair : pair ∈ shallowCorePairs N A L hN) :
    pairSigma A pair ≤ maxShallowCoreSigma N A L hN := by
  unfold maxShallowCoreSigma
  exact Finset.le_sup (f := fun pair ↦ pairSigma A pair) hpair

/--
A pointwise real upper bound passes to the finite `σ` maximum, including the
empty-population case.
@isnad1 id=le.3h4v.s6.c7890639fef7 from=translated src=- shape=b017d46d vocab=38e6d6e9
-/
theorem maxShallowCoreSigma_cast_le
    {N A L : ℕ} {hN : 2 ≤ N} {R : ℝ}
    (hR : 0 ≤ R)
    (hpoint :
      ∀ pair ∈ shallowCorePairs N A L hN,
        (pairSigma A pair : ℝ) ≤ R) :
    (maxShallowCoreSigma N A L hN : ℝ) ≤ R := by
  classical
  have aux :
      ∀ s : Finset (SeparatedDyadicPair N L),
        (∀ pair ∈ s, (pairSigma A pair : ℝ) ≤ R) →
        ((s.sup fun pair ↦ pairSigma A pair : ℕ) : ℝ) ≤ R := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro _h
        simpa using hR
    | @insert pair s hpairNotMem ih =>
        intro hs
        rw [Finset.sup_insert, Nat.cast_max]
        apply max_le
        · exact hs pair (Finset.mem_insert_self pair s)
        · apply ih
          intro other hother
          exact hs other (Finset.mem_insert_of_mem hother)
  exact aux (shallowCorePairs N A L hN) hpoint

end

end ShallowCorePairs
end PaperC
