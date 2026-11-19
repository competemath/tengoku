import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyScalarNearSignedSum
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyNonstandardSourceMaximal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Physical-suffix maximal bounds for the scalar near-energy branch

The actual functions, generation prefixes, active-family restriction,
overlap pruning, and source-oriented physical tails are those already
defined in the project. This module proves their estimates for
`KrauseLaceyScalarNear.intervals`, which is exactly the energy classifier's
near family. The signed-sum input is supplied by the scalar diagonal
estimate proved in `KrauseLaceyScalarNearSignedSum`.

The geometric and measure-theoretic arguments below are the corresponding
proofs from the original near-family modules, now with the scalar-family
hypothesis. In particular, there is no conversion to the old pointwise
predicate and no assumed overlap or Carleson budget in the final theorem.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyScalarNear

open KrauseLaceyBadScale KrauseLaceyStoppingExtraction
  KrauseLaceyGenerationLayers KrauseLaceyRademacherMenshov

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/--
@isnad1 id=hassigne.7h8v.s8.ba1dc9259f16 from=translated src=- shape=bcd835a7 vocab=c2cc7800
-/
theorem hasSignedSumSquareBound_badSubcollectionGenerations
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (M : ℕ) :
    HasSignedSumSquareBound M (badSubcollectionGenerationLp S f hf I₀ k₀ s scale N)
      (nonstandardSignedEnergyBudget f I₀ s) := by
  intro c hc
  change ‖∑ n ∈ Finset.range M, c n • ∑ I ∈ generation N n,
    badPieceLp S f hf I₀ k₀ s scale I‖ ^ 2 ≤ _
  rw [sum_smul_generations_range_eq]
  apply norm_signed_badPieceLp_sq_le hf I₀ k₀ s (by omega) scale hlam hparent hsub N hN _ _ _
  · intro I hI
    have hi := (Finset.mem_filter.mp (hN hI)).2.2.1
    omega
  · intro I hI
    split_ifs with hi
    · rcases hc _ hi with h | h | h <;> rw [h] <;> norm_num
    · norm_num

/--
@isnad1 id=le.7h8v.s8.666b441ae7eb from=translated src=- shape=14be5dd8 vocab=2b8a992a
-/
theorem eLpNorm_badSubcollectionPrefixMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (M : ℕ) :
    eLpNorm (badSubcollectionPrefixMaximal S f I₀ k₀ s scale N M) 2 volume ≤
      ENNReal.ofReal ((Nat.log2 M + 1 : ℝ) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  rw [eLpNorm_congr_ae (badSubcollectionPrefixMaximal_ae_eq S f hf I₀ k₀ s scale N M)]
  apply eLpNorm_finitePrefixMaximal_le_log2 _ _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (nonstandardSignedEnergyBudget_nonneg f I₀ s)]
  exact hasSignedSumSquareBound_badSubcollectionGenerations hf I₀ k₀ s hk₀ hs scale
    hlam hparent hsub N hN M

/--
@isnad1 id=le.8h9v.s8.1e1ebf4b8dd2 from=translated src=- shape=af7c178a vocab=22f0fe26
-/
theorem eLpNorm_badSubcollectionPrefixMaximal_le_of_ae_overlapCount_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (L M : ℕ)
    (hbound : ∀ᵐ x ∂volume, overlapCount N x ≤ M) :
    eLpNorm (badSubcollectionPrefixMaximal S f I₀ k₀ s scale N L) 2 volume ≤
      ENNReal.ofReal ((Nat.log2 M + 1 : ℝ) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  apply le_trans _ (eLpNorm_badSubcollectionPrefixMaximal_le hf I₀ k₀ s hk₀ hs scale
    hlam hparent hsub N hN M)
  apply eLpNorm_mono
  intro x
  rw [Real.norm_of_nonneg (badSubcollectionPrefixMaximal_nonneg S f I₀ k₀ s scale N L x),
    Real.norm_of_nonneg (badSubcollectionPrefixMaximal_nonneg S f I₀ k₀ s scale N M x)]
  exact badSubcollectionPrefixMaximal_le_of_ae_overlapCount_le S f I₀ k₀ s scale N L M hbound x

/--
@isnad1 id=ex.4h7v.s7.75227e059c9a from=translated src=- shape=a922dccf vocab=d605239d
-/
theorem exists_chargedCell_of_active_above_base
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    {I : RealInterval} (hI : I ∈ intervals S f I₀ k₀ s scale)
    (hbase : k₀ < scale I + 2 - s)
    (hactive : ∃ x, intervalBadInput S f I₀ k₀ s scale I x ≠ 0) :
    ∃ J ∈ stoppingChildren S f 0 I₀,
      J.carrier ⊆ I.carrier ∧ I.length = (2 : ℝ) ^ s * J.length := by
  obtain ⟨J, hJ, hJI⟩ := exists_badScaleCell_subset_of_active f I₀ k₀ s scale hlam
    (Finset.mem_filter.mp hI).1 hactive
  have hmax := (Finset.mem_filter.mp hJ).2
  have hlt : (2 : ℝ) ^ k₀ < (2 : ℝ) ^ (scale I + 2 - s) :=
    (zpow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)) hbase
  have hlenJ : J.length = (2 : ℝ) ^ (scale I + 2 - s) := by
    rcases max_cases ((2 : ℝ) ^ k₀) J.length with h | h
    · exact (ne_of_lt hlt (h.1.symm.trans hmax)).elim
    · exact h.1.symm.trans hmax
  refine ⟨J, badScaleCells_subset S f I₀ k₀ _ hJ, hJI, ?_⟩
  rw [(Finset.mem_filter.mp hI).2.1, hlenJ, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  ring

/--
@isnad1 id=le.5h8v.s8.e665a0c78b5c from=translated src=- shape=fa0e4456 vocab=d335e93e
-/
theorem sum_active_aboveBase_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (hactive : ∀ I ∈ N, ∃ x, intervalBadInput S f I₀ k₀ s scale I x ≠ 0)
    (hbase : ∀ I ∈ N, k₀ < scale I + 2 - s)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    (∑ I ∈ N, I.length) ≤ (2 : ℝ) ^ s * K.length := by
  let : Nonempty RealInterval := ⟨I₀⟩
  have hex (I : RealInterval) (hI : I ∈ N) :=
    exists_chargedCell_of_active_above_base f I₀ k₀ s scale hlam (hN hI)
      (hbase I hI) (hactive I hI)
  choose! cell hcell hinside hlength using hex
  let C := (stoppingChildren S f 0 I₀).filter fun J ↦ J.carrier ⊆ K.carrier
  have hCS : Set.Pairwise (↑C) (Disjoint on RealInterval.carrier) := by
    intro I hI J hJ hne
    exact stoppingChildren_pairwiseDisjoint f 0 I₀ hlam
      (Finset.mem_filter.mp hI).1 (Finset.mem_filter.mp hJ).1 hne
  have hinj : Set.InjOn cell (↑N : Set RealInterval) := by
    intro I hI J hJ heq
    have hlen : I.length = J.length := by rw [hlength I hI, hlength J hJ, heq]
    exact eq_of_common_subinterval_of_length_eq hlam
      (intervals_subset S f I₀ k₀ s scale (hN hI))
      (intervals_subset S f I₀ k₀ s scale (hN hJ)) hlen
      (hinside I hI) (heq ▸ hinside J hJ)
  have hmap : N.image cell ⊆ C := by
    intro J hJ
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
    exact Finset.mem_filter.mpr ⟨hcell I hI, (hinside I hI).trans (hsub I hI)⟩
  calc
    _ ≤ ∑ J ∈ C, (2 : ℝ) ^ s * J.length :=
      Finset.sum_le_sum_of_injOn cell hinj hmap
        (fun I hI ↦ (hlength I hI).le) (fun J _ _ ↦ by positivity [J.length_pos])
    _ = (2 : ℝ) ^ s * ∑ J ∈ C, J.length := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_intervalLength_le_of_disjoint C K hCS
        (fun J hJ ↦ (Finset.mem_filter.mp hJ).2)) (by positivity)

/--
@isnad1 id=le.4h8v.s7.36cd7275a983 from=translated src=- shape=a5184bcc vocab=30995818
-/
theorem sum_baseScale_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (hbase : ∀ I ∈ N, scale I + 2 - s ≤ k₀)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    (∑ I ∈ N, I.length) ≤ K.length := by
  apply sum_intervalLength_le_of_disjoint N K _ hsub
  intro I hI J hJ hne
  have hi := (Finset.mem_filter.mp (hN hI)).2
  have hj := (Finset.mem_filter.mp (hN hJ)).2
  have hidx : scale I = scale J := by have := hbase I hI; have := hbase J hJ; omega
  have hlen : I.length = J.length := by rw [hi.1, hj.1, hidx]
  have hNS := intervals_subset S f I₀ k₀ s scale
  rcases hlam (hNS (hN hI)) (hNS (hN hJ)) hne with hsub | hsub | hd
  · exact (hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.ge)).elim
  · exact (hne (interval_eq_of_carrier_subset_of_length_le hsub hlen.le).symm).elim
  · exact hd

/--
@isnad1 id=le.3h8v.s7.512533c255c6 from=translated src=- shape=9bd6220a vocab=176b0dd4
-/
theorem sum_activeBadIntervals_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    (∑ I ∈ activeBadIntervals S f I₀ k₀ s scale N, I.length) ≤
      (1 + (2 : ℝ) ^ s) * K.length := by
  let A := activeBadIntervals S f I₀ k₀ s scale N
  have hAN := activeBadIntervals_subset S f I₀ k₀ s scale N
  have hfar := sum_active_aboveBase_length_le f I₀ k₀ s scale hlam
    (A.filter fun I ↦ k₀ < scale I + 2 - s)
    ((Finset.filter_subset _ A).trans (hAN.trans hN))
    (fun I hI ↦ (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2)
    (fun I hI ↦ (Finset.mem_filter.mp hI).2) K
    (fun I hI ↦ hsub I (hAN (Finset.mem_filter.mp hI).1))
  have hnear := sum_baseScale_length_le f I₀ k₀ s scale hlam
    (A.filter fun I ↦ ¬ k₀ < scale I + 2 - s)
    ((Finset.filter_subset _ A).trans (hAN.trans hN))
    (fun I hI ↦ le_of_not_gt (Finset.mem_filter.mp hI).2) K
    (fun I hI ↦ hsub I (hAN (Finset.mem_filter.mp hI).1))
  have heq := Finset.sum_filter_add_sum_filter_not A
    (fun I ↦ k₀ < scale I + 2 - s) RealInterval.length
  dsimp only [A] at heq
  linarith

/--
@isnad1 id=le.2h8v.s7.2bc65da32886 from=translated src=- shape=e89393c2 vocab=df7825e8
-/
theorem sum_activeBadIntervals_descendants_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (K : RealInterval) :
    (∑ I ∈ (activeBadIntervals S f I₀ k₀ s scale N).filter
      (fun I ↦ I.carrier ⊆ K.carrier), I.length) ≤ (1 + (2 : ℝ) ^ s) * K.length := by
  have heq : (activeBadIntervals S f I₀ k₀ s scale N).filter
      (fun I ↦ I.carrier ⊆ K.carrier) =
      activeBadIntervals S f I₀ k₀ s scale (N.filter fun I ↦ I.carrier ⊆ K.carrier) := by
    ext I
    simp only [activeBadIntervals, Finset.mem_filter, and_assoc, and_left_comm, and_comm]
  rw [heq]
  exact sum_activeBadIntervals_length_le f I₀ k₀ s scale hlam _
    ((Finset.filter_subset _ N).trans hN) K (fun I hI ↦ (Finset.mem_filter.mp hI).2)

/--
@isnad1 id=le.3h9v.s7.736ccbfdd724 from=translated src=- shape=b87730cb vocab=eeeed36f
-/
theorem volume_active_highOverlap_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) (M : ℕ) :
    volume {x | M < overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x} ≤
      ENNReal.ofReal ((1 + (2 : ℝ) ^ s) * K.length) / (M + 1 : ℝ≥0∞) := by
  apply (volume_highOverlap_le _ M).trans
  exact ENNReal.div_le_div_right (ENNReal.ofReal_le_ofReal
    (sum_activeBadIntervals_length_le f I₀ k₀ s scale hlam N hN K hsub)) _

/--
@isnad1 id=eq.2h10v.s7.6ebdb04fe304 from=translated src=- shape=858b9ed1 vocab=4b4a3887
-/
theorem sum_weighted_localizedBadPiece_eq_pruned_of_lowOverlap
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval)
    (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (M : ℕ) (c : RealInterval → ℂ) (x : ℝ)
    (hx : overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x ≤ M) :
    (∑ I ∈ N, c I * krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x) =
    ∑ I ∈ overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M,
      c I * krauseLaceyLocalizedPiece 1 (scale I) I
        (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x := by
  rw [sum_weighted_localizedBadPiece_eq_active]
  symm
  apply Finset.sum_subset (overlapPrunedFamily_subset _ M)
  intro I hI hn
  have hnot : x ∉ I.carrier := fun hxI ↦ hn (Finset.mem_filter.mpr ⟨hI, x, hxI, hx⟩)
  rw [krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 (scale I) I _
    (Finset.mem_filter.mp (hN (Finset.mem_filter.mp hI).1)).2.1 hnot, mul_zero]

/--
@isnad1 id=le.7h9v.s8.b46b01fbd830 from=translated src=- shape=7bf9da9a vocab=7c040fae
-/
theorem eLpNorm_prunedActivePrefixMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (L M : ℕ) :
    eLpNorm (badSubcollectionPrefixMaximal S f I₀ k₀ s scale
      (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) L) 2 volume ≤
      ENNReal.ofReal ((Nat.log2 M + 1 : ℝ) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  have hAS := (activeBadIntervals_subset S f I₀ k₀ s scale N).trans
    (hN.trans (intervals_subset S f I₀ k₀ s scale))
  apply eLpNorm_badSubcollectionPrefixMaximal_le_of_ae_overlapCount_le hf I₀ k₀ s hk₀ hs
    scale hlam hparent hsub _
    ((overlapPrunedFamily_subset _ M).trans
      ((activeBadIntervals_subset S f I₀ k₀ s scale N).trans hN)) L M
  exact Filter.Eventually.of_forall (overlapCount_overlapPrunedFamily_le _ M
    (fun I hI J hJ hne ↦ hlam (hAS hI) (hAS hJ) hne))

/--
@isnad1 id=le.6h8v.s8.60cdf707c92f from=translated src=- shape=f7e50df2 vocab=75141beb
-/
theorem eLpNorm_paperPrunedActivePrefixMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (L : ℕ) :
    eLpNorm (badSubcollectionPrefixMaximal S f I₀ k₀ s scale
      (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) (activeOverlapCutoff s)) L)
      2 volume ≤ ENNReal.ofReal ((2 * (s : ℝ) + 2) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  apply (eLpNorm_prunedActivePrefixMaximal_le hf I₀ k₀ s hk₀ (by omega) scale
    hlam hparent hsub N hN L (activeOverlapCutoff s)).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have h := log2_activeOverlapCutoff_le s
  have hr : (Nat.log2 (activeOverlapCutoff s) : ℝ) ≤ 2 * (s : ℝ) + 1 := by exact_mod_cast h
  linarith

/--
@isnad1 id=le.2h9v.s7.b88f9b0b461e from=translated src=- shape=ba69dc3c vocab=5591b366
-/
theorem norm_badLengthTailAction_le_prefix
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (ell : ℤ) (x : ℝ) :
    ‖badLengthTailAction S f I₀ k₀ s scale N ell x‖ ≤
      2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale N N.card x := by
  have hNS := hN.trans (intervals_subset S f I₀ k₀ s scale)
  apply norm_lengthTail_le_two_generationPrefixNormMax N
    (fun I hI J hJ hne ↦ hlam (hNS hI) (hNS hJ) hne) _ ((2 : ℝ) ^ ell) x
  intro I hI hxI
  exact krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 (scale I) I _
    (Finset.mem_filter.mp (hN hI)).2.1 hxI

/--
@isnad1 id=le.2h8v.s7.7d83a824c2ac from=translated src=- shape=1d7d2abd vocab=97c32096
-/
theorem badLengthTailMaximal_le_prefix
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (x : ℝ) :
    badLengthTailMaximal S f I₀ k₀ s scale N x ≤
      2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale N N.card x :=
  ciSup_le fun ell ↦ norm_badLengthTailAction_le_prefix f I₀ k₀ s scale hlam N hN ell x

/--
@isnad1 id=le.2h8v.s7.d7d7090acd40 from=translated src=- shape=6bd7cc42 vocab=cc24ed08
-/
theorem badLengthTailMaximal_nonneg
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (x : ℝ) :
    0 ≤ badLengthTailMaximal S f I₀ k₀ s scale N x := by
  have hb : BddAbove (Set.range (fun ell : ℤ ↦
      ‖badLengthTailAction S f I₀ k₀ s scale N ell x‖)) :=
    ⟨2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale N N.card x, by
      rintro _ ⟨ell, rfl⟩
      exact norm_badLengthTailAction_le_prefix f I₀ k₀ s scale hlam N hN ell x⟩
  exact (norm_nonneg _).trans (le_ciSup hb (0 : ℤ))

/--
@isnad1 id=eq.2h9v.s6.30acd757d0b1 from=translated src=- shape=4b4606d9 vocab=853e29fc
-/
theorem badLengthTailMaximal_eq_pruned_of_lowOverlap
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval)
    (hN : N ⊆ intervals S f I₀ k₀ s scale) (M : ℕ) (x : ℝ)
    (hx : overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x ≤ M) :
    badLengthTailMaximal S f I₀ k₀ s scale N x =
      badLengthTailMaximal S f I₀ k₀ s scale
        (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) x := by
  apply iSup_congr
  intro ell
  congr 1
  simpa only [badLengthTailAction, ite_mul, one_mul, zero_mul] using
    sum_weighted_localizedBadPiece_eq_pruned_of_lowOverlap S f I₀ k₀ s scale N hN M
      (fun I ↦ if (2 : ℝ) ^ ell ≤ I.length then 1 else 0) x hx

/--
@isnad1 id=le.7h8v.s8.da7e5bee6338 from=translated src=- shape=150d2070 vocab=71c48d44
-/
theorem eLpNorm_pruned_badLengthTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 3 ≤ k₀) (hs : 0 ≤ s)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (M : ℕ) :
    eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale
      (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M)) 2 volume ≤
      ENNReal.ofReal (2 * ((Nat.log2 M + 1 : ℝ) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s))) := by
  let P := overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M
  have hP : P ⊆ intervals S f I₀ k₀ s scale :=
    (overlapPrunedFamily_subset _ M).trans
      ((activeBadIntervals_subset S f I₀ k₀ s scale N).trans hN)
  have hmono : eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale P) 2 volume ≤
      eLpNorm (fun x ↦ (2 : ℝ) • badSubcollectionPrefixMaximal S f I₀ k₀ s scale P P.card x)
        2 volume := by
    apply eLpNorm_mono
    intro x
    rw [Real.norm_of_nonneg (badLengthTailMaximal_nonneg f I₀ k₀ s scale hlam P hP x),
      smul_eq_mul, Real.norm_of_nonneg (mul_nonneg (by norm_num)
        (badSubcollectionPrefixMaximal_nonneg S f I₀ k₀ s scale P P.card x))]
    exact badLengthTailMaximal_le_prefix f I₀ k₀ s scale hlam P hP x
  apply hmono.trans
  change eLpNorm ((2 : ℝ) • badSubcollectionPrefixMaximal S f I₀ k₀ s scale P P.card)
    2 volume ≤ _
  rw [eLpNorm_const_smul, show ‖(2 : ℝ)‖ₑ = ENNReal.ofReal 2 by
      exact Real.enorm_of_nonneg (by norm_num),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_right (eLpNorm_prunedActivePrefixMaximal_le hf I₀ k₀ s hk₀ hs scale
    hlam hparent hsub N hN P.card M) _

/--
@isnad1 id=le.3h9v.s7.d1ed86f10b9c from=translated src=- shape=29394e84 vocab=d13431f7
-/
theorem volume_active_overlap_blocks_le_half_pow
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ) (s t : ℕ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    volume {x | t * activeOverlapBlock s <
      overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x} ≤
      (1 / 2 : ℝ≥0∞) ^ t * ENNReal.ofReal K.length := by
  have hAS := (activeBadIntervals_subset S f I₀ k₀ s scale N).trans
    (hN.trans (intervals_subset S f I₀ k₀ s scale))
  simpa only [activeOverlapBlock_pred_add_one] using
    volume_overlap_blocks_le_half_pow t (activeBadIntervals S f I₀ k₀ s scale N) K
      (activeOverlapBlock s - 1) (1 + (2 : ℝ) ^ (s : ℤ))
      (activeOverlapBlock_real_bound s)
      (fun I hI J hJ hne ↦ hlam (hAS hI) (hAS hJ) hne)
      (fun I hI ↦ hsub I (activeBadIntervals_subset S f I₀ k₀ s scale N hI))
      (sum_activeBadIntervals_descendants_length_le f I₀ k₀ s scale hlam N hN)

/--
@isnad1 id=le.3h8v.s8.49ae59466f22 from=translated src=- shape=e98f6191 vocab=820d08bd
-/
theorem volume_active_exponentialCutoff_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    volume {x | activeExponentialCutoff s <
      overlapCount (activeBadIntervals S f I₀ k₀ s scale N) x} ≤
      (1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal K.length := by
  rw [activeExponentialCutoff_eq_blocks, activeOverlapBlock_pred_add_one]
  exact volume_active_overlap_blocks_le_half_pow f I₀ k₀ s (8 * (s + 1)) scale
    hlam N hN K hsub

/--
@isnad1 id=le.3h8v.s8.a4bb5017e0a2 from=translated src=- shape=a30ffd78 vocab=abed73a9
-/
theorem ofReal_sum_active_removed_length_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    ENNReal.ofReal (∑ I ∈ activeBadIntervals S f I₀ k₀ s scale N \
      overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) (activeExponentialCutoff s),
      I.length) ≤
      ENNReal.ofReal (1 + (2 : ℝ) ^ (s : ℤ)) *
        ((1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal K.length) := by
  have hAS := (activeBadIntervals_subset S f I₀ k₀ s scale N).trans
    (hN.trans (intervals_subset S f I₀ k₀ s scale))
  apply (ofReal_sum_removed_length_le_carleson_mul_highOverlap
    (activeBadIntervals S f I₀ k₀ s scale N) (activeExponentialCutoff s)
    (1 + (2 : ℝ) ^ (s : ℤ)) (by positivity)
    (fun I hI J hJ hne ↦ hlam (hAS hI) (hAS hJ) hne)
    (sum_activeBadIntervals_descendants_length_le f I₀ k₀ s scale hlam N hN)).trans
  exact mul_le_mul_right
    (volume_active_exponentialCutoff_le f I₀ k₀ s scale hlam N hN K hsub) _

/--
@isnad1 id=le.6h7v.s8.71abc008b9d6 from=translated src=- shape=f8737913 vocab=555c86d1
-/
theorem eLpNorm_exponentiallyPruned_badLengthTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) :
    eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale
      (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N)
        (activeExponentialCutoff s))) 2 volume ≤
      ENNReal.ofReal ((4 * (s : ℝ) + 12) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) := by
  apply (eLpNorm_pruned_badLengthTailMaximal_le hf I₀ k₀ s hk₀ (by omega) scale
    hlam hparent hsub N hN (activeExponentialCutoff s)).trans
  apply ENNReal.ofReal_le_ofReal
  have hr : (Nat.log2 (activeExponentialCutoff s) : ℝ) ≤ 2 * (s : ℝ) + 5 := by
    exact_mod_cast log2_activeExponentialCutoff_le s
  nlinarith [Real.sqrt_nonneg (nonstandardSignedEnergyBudget f I₀ s)]

/--
@isnad1 id=le.3h8v.s8.6cfc7060816f from=translated src=- shape=4b728d12 vocab=069868b8
-/
theorem lintegral_active_removed_overlap_sq_le
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (K : RealInterval) (hsub : ∀ I ∈ N, I.carrier ⊆ K.carrier) :
    (∫⁻ x, (overlapCount (activeBadIntervals S f I₀ k₀ s scale N \
      overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N)
        (activeExponentialCutoff s)) x : ℝ≥0∞) ^ 2) ≤
      2 * ENNReal.ofReal (1 + (2 : ℝ) ^ (s : ℤ)) ^ 2 *
        ((1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal K.length) := by
  let A := activeBadIntervals S f I₀ k₀ s scale N
  let R := A \ overlapPrunedFamily A (activeExponentialCutoff s)
  have hRS : R ⊆ S := Finset.sdiff_subset.trans
    ((activeBadIntervals_subset S f I₀ k₀ s scale N).trans
      (hN.trans (intervals_subset S f I₀ k₀ s scale)))
  have hb := lintegral_overlapCount_sq_le R (1 + (2 : ℝ) ^ (s : ℤ)) (by positivity)
    (fun I hI J hJ hne ↦ hlam (hRS hI) (hRS hJ) hne)
    (local_length_packing_mono Finset.sdiff_subset
      (sum_activeBadIntervals_descendants_length_le f I₀ k₀ s scale hlam N hN))
  apply hb.trans
  calc
    _ ≤ (2 * ENNReal.ofReal (1 + (2 : ℝ) ^ (s : ℤ))) *
        (ENNReal.ofReal (1 + (2 : ℝ) ^ (s : ℤ)) *
          ((1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal K.length)) :=
      mul_le_mul_right (ofReal_sum_active_removed_length_le f I₀ k₀ s scale
        hlam N hN K hsub) _
    _ = _ := by rw [pow_two]; simp only [mul_assoc]

/--
@isnad1 id=le.4h8v.s7.3fed4b867467 from=translated src=- shape=dc4d553a vocab=4902a6e6
-/
theorem norm_localizedBadPiece_le_uniform
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    {I : RealInterval} (hI : I ∈ intervals S f I₀ k₀ s scale) (x : ℝ) :
    ‖krauseLaceyLocalizedPiece 1 (scale I) I
      (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖ ≤ badPieceUniformBound f I₀ := by
  let b := badScaleInput S f I₀ k₀ (scale I + 2 - s)
  have hb : Integrable b := integrable_badScaleInput S hf I₀ k₀ (scale I + 2 - s)
  have h := (krauseLaceyPositiveKernel (scale I)).norm_applyIntegral_le
    (hb.indicator I.measurableSet_centralThird) x
  simp only [FiniteRangeKernel.applyIntegral, krauseLaceyPositiveKernel_apply,
    ← krauseLaceyLocalizedPiece_eq_positiveDyadicConvolution] at h
  have hmass := badScaleInput_localMass_le hf I₀ k₀ (scale I + 2 - s)
    hlam hsub (Finset.mem_filter.mp hI).1
  have hid : (∫ t, ‖I.centralThird.indicator b t‖) = ∫ t in I.centralThird, ‖b t‖ := by
    simp only [norm_indicator_eq_indicator_norm]
    exact integral_indicator I.measurableSet_centralThird
  rw [hid] at h
  have hscale := (Finset.mem_filter.mp hI).2.1
  calc
    _ ≤ (positiveDyadicAmplitudeBound / (2 : ℝ) ^ (scale I - 1)) *
        (∫ t in I.centralThird, ‖b t‖) := h
    _ ≤ (positiveDyadicAmplitudeBound / (2 : ℝ) ^ (scale I - 1)) *
        (10 * intervalL1Average f I₀ * I.length) :=
      mul_le_mul_of_nonneg_left hmass (div_nonneg positiveDyadicAmplitudeBound_nonneg
        (by positivity))
    _ = badPieceUniformBound f I₀ := by
      rw [hscale, krauseLacey_scale_eq_eight_mul_radius]
      unfold badPieceUniformBound
      field_simp
      ring

/--
@isnad1 id=le.4h8v.s7.4e00be3034ff from=translated src=- shape=172bf359 vocab=b0f8a21f
-/
theorem badLengthTailMaximal_le_uniform_mul_overlapCount
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (x : ℝ) :
    badLengthTailMaximal S f I₀ k₀ s scale N x ≤
      badPieceUniformBound f I₀ * overlapCount N x := by
  apply ciSup_le
  intro ell
  calc
    _ ≤ ∑ I ∈ N, ‖if (2 : ℝ) ^ ell ≤ I.length then
        krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x else 0‖ := norm_sum_le _ _
    _ ≤ ∑ I ∈ N, if x ∈ I.carrier then badPieceUniformBound f I₀ else 0 := by
      apply Finset.sum_le_sum
      intro I hI
      by_cases hx : x ∈ I.carrier
      · rw [ite_eq_left hx]
        split_ifs
        · exact norm_localizedBadPiece_le_uniform hf I₀ k₀ s scale hlam hsub (hN hI) x
        · simpa only [norm_zero] using badPieceUniformBound_nonneg f I₀
      · rw [ite_eq_right hx, krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 (scale I) I _
          (Finset.mem_filter.mp (hN hI)).2.1 hx]
        simp
    _ = badPieceUniformBound f I₀ * overlapCount N x := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, overlapCount, mul_comm]

/--
@isnad1 id=le.4h7v.s9.98d819d5920d from=translated src=- shape=98de6067 vocab=f95f7449
-/
theorem eLpNorm_removed_badLengthTailMaximal_sq_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) :
    eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale
      (activeBadIntervals S f I₀ k₀ s scale N \
        overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N)
          (activeExponentialCutoff s))) 2 volume ^ 2 ≤
      ENNReal.ofReal (badPieceUniformBound f I₀) ^ 2 *
        (2 * ENNReal.ofReal (1 + (2 : ℝ) ^ (s : ℤ)) ^ 2 *
          ((1 / 2 : ℝ≥0∞) ^ (8 * (s + 1)) * ENNReal.ofReal I₀.length)) := by
  let R := activeBadIntervals S f I₀ k₀ s scale N \
    overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) (activeExponentialCutoff s)
  have hR : R ⊆ intervals S f I₀ k₀ s scale :=
    Finset.sdiff_subset.trans ((activeBadIntervals_subset S f I₀ k₀ s scale N).trans hN)
  have heq : eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale R) 2 volume ^ 2 =
      ∫⁻ x, ‖badLengthTailMaximal S f I₀ k₀ s scale R x‖ₑ ^ 2 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    rw [← ENNReal.rpow_mul_natCast]
    norm_num
  rw [heq]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (badPieceUniformBound f I₀) ^ 2 *
        (overlapCount R x : ℝ≥0∞) ^ 2 := by
      apply lintegral_mono
      intro x
      have hpoint := badLengthTailMaximal_le_uniform_mul_overlapCount hf I₀ k₀ s scale
        hlam hsub R hR x
      have he : ‖badLengthTailMaximal S f I₀ k₀ s scale R x‖ₑ ≤
          ENNReal.ofReal (badPieceUniformBound f I₀) * (overlapCount R x : ℝ≥0∞) := by
        rw [Real.enorm_of_nonneg (badLengthTailMaximal_nonneg f I₀ k₀ s scale hlam R hR x),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (badPieceUniformBound_nonneg f I₀)]
        exact ENNReal.ofReal_le_ofReal hpoint
      simpa only [mul_pow] using pow_le_pow_left' he 2
    _ = ENNReal.ofReal (badPieceUniformBound f I₀) ^ 2 *
        (∫⁻ x, (overlapCount R x : ℝ≥0∞) ^ 2) := by
      rw [lintegral_const_mul _ ((measurable_overlapCount_cast R).pow_const 2)]
    _ ≤ _ := mul_le_mul_right (lintegral_active_removed_overlap_sq_le f I₀ k₀ s scale
      hlam N hN I₀ (fun I hI ↦ hsub I (intervals_subset S f I₀ k₀ s scale (hN hI)))) _

/--
@isnad1 id=le.4h7v.s8.2c917a6d39d3 from=translated src=- shape=fe8afad5 vocab=1b4ebf29
-/
theorem eLpNorm_removed_badLengthTailMaximal_le_sqrt
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) :
    eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale
      (activeBadIntervals S f I₀ k₀ s scale N \
        overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N)
          (activeExponentialCutoff s))) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (badRemovedEnergyBudget f I₀ s)) := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  rw [ENNReal.rpow_two, ENNReal.rpow_two,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2,
    Real.sq_sqrt (badRemovedEnergyBudget_nonneg f I₀ s), ofReal_badRemovedEnergyBudget]
  exact eLpNorm_removed_badLengthTailMaximal_sq_le hf I₀ k₀ s scale hlam hsub N hN

/--
@isnad1 id=eq.1h10v.s6.b89bbab8c2a0 from=translated src=- shape=3baaaead vocab=f619aa97
-/
theorem badLengthTailAction_eq_pruned_add_removed
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval)
    (_hN : N ⊆ intervals S f I₀ k₀ s scale) (M : ℕ) (ell : ℤ) (x : ℝ) :
    badLengthTailAction S f I₀ k₀ s scale N ell x =
      badLengthTailAction S f I₀ k₀ s scale
        (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) ell x +
      badLengthTailAction S f I₀ k₀ s scale
        (activeBadIntervals S f I₀ k₀ s scale N \
          overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) ell x := by
  unfold badLengthTailAction
  rw [sum_lengthTail_localizedBadPiece_eq_active S f I₀ k₀ s scale N ell x]
  rw [← Finset.sum_sdiff (overlapPrunedFamily_subset _ M)]
  ring

/--
@isnad1 id=le.2h9v.s7.074797f46c70 from=translated src=- shape=6bfe88fa vocab=5e58cbcb
-/
theorem badLengthTailMaximal_le_pruned_add_removed
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale)
    (M : ℕ) (x : ℝ) :
    badLengthTailMaximal S f I₀ k₀ s scale N x ≤
      badLengthTailMaximal S f I₀ k₀ s scale
        (overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) x +
      badLengthTailMaximal S f I₀ k₀ s scale
        (activeBadIntervals S f I₀ k₀ s scale N \
          overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N) M) x := by
  have hbound (Q : Finset RealInterval)
      (hQ : Q ⊆ intervals S f I₀ k₀ s scale) :
      BddAbove (Set.range fun ell : ℤ ↦ ‖badLengthTailAction S f I₀ k₀ s scale Q ell x‖) := by
    refine ⟨2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale Q Q.card x, ?_⟩
    rintro _ ⟨ell, rfl⟩
    exact norm_badLengthTailAction_le_prefix f I₀ k₀ s scale hlam Q hQ ell x
  have hA := (activeBadIntervals_subset S f I₀ k₀ s scale N).trans hN
  apply ciSup_le
  intro ell
  rw [badLengthTailAction_eq_pruned_add_removed S f I₀ k₀ s scale N hN M ell x]
  apply (norm_add_le _ _).trans
  exact add_le_add (le_ciSup (hbound _ ((overlapPrunedFamily_subset _ M).trans hA)) ell)
    (le_ciSup (hbound _ (Finset.sdiff_subset.trans hA)) ell)

/--
@isnad1 id=le.6h7v.s8.8b629a46f8b6 from=translated src=- shape=4eebd1f4 vocab=6d2659e8
-/
theorem eLpNorm_nonstandard_badLengthTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) :
    eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale N) 2 volume ≤
      ENNReal.ofReal ((4 * (s : ℝ) + 12) *
        Real.sqrt (nonstandardSignedEnergyBudget f I₀ s) +
          Real.sqrt (badRemovedEnergyBudget f I₀ s)) := by
  let P := overlapPrunedFamily (activeBadIntervals S f I₀ k₀ s scale N)
    (activeExponentialCutoff s)
  let R := activeBadIntervals S f I₀ k₀ s scale N \ P
  have hA := (activeBadIntervals_subset S f I₀ k₀ s scale N).trans hN
  have hP : P ⊆ intervals S f I₀ k₀ s scale :=
    (overlapPrunedFamily_subset _ _).trans hA
  have hR : R ⊆ intervals S f I₀ k₀ s scale := Finset.sdiff_subset.trans hA
  calc
    _ ≤ eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale P +
        badLengthTailMaximal S f I₀ k₀ s scale R) 2 volume := by
      apply eLpNorm_mono
      intro x
      simp only [Pi.add_apply]
      rw [Real.norm_of_nonneg (badLengthTailMaximal_nonneg f I₀ k₀ s scale hlam N hN x),
        Real.norm_of_nonneg (add_nonneg
          (badLengthTailMaximal_nonneg f I₀ k₀ s scale hlam P hP x)
          (badLengthTailMaximal_nonneg f I₀ k₀ s scale hlam R hR x))]
      exact badLengthTailMaximal_le_pruned_add_removed f I₀ k₀ s scale hlam N hN _ x
    _ ≤ eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale P) 2 volume +
        eLpNorm (badLengthTailMaximal S f I₀ k₀ s scale R) 2 volume :=
      eLpNorm_add_le (aemeasurable_badLengthTailMaximal S hf I₀ k₀ s scale P).aestronglyMeasurable
        (aemeasurable_badLengthTailMaximal S hf I₀ k₀ s scale R).aestronglyMeasurable (by norm_num)
    _ ≤ ENNReal.ofReal ((4 * (s : ℝ) + 12) * Real.sqrt (nonstandardSignedEnergyBudget f I₀ s)) +
        ENNReal.ofReal (Real.sqrt (badRemovedEnergyBudget f I₀ s)) :=
      add_le_add (eLpNorm_exponentiallyPruned_badLengthTailMaximal_le hf I₀ k₀ s hk₀
        scale hlam hparent hsub N hN)
        (eLpNorm_removed_badLengthTailMaximal_le_sqrt hf I₀ k₀ s scale hlam hsub N hN)
    _ = _ := (ENNReal.ofReal_add (by positivity) (Real.sqrt_nonneg _)).symm

/--
@isnad1 id=eq.1h9v.s6.348e3d3d386b from=translated src=- shape=cb436e74 vocab=d5ecb97a
-/
theorem badLengthTailAction_eq_at_max_lower_endpoint
    (S : Finset RealInterval) (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ) (N : Finset RealInterval)
    (hN : N ⊆ intervals S f I₀ k₀ s scale) (ell : ℤ) (x : ℝ) :
    badLengthTailAction S f I₀ k₀ s scale N ell x =
      badLengthTailAction S f I₀ k₀ s scale N (max ell (k₀ + s)) x := by
  by_cases he : k₀ + s ≤ ell
  · rw [max_eq_left he]
  rw [max_eq_right (le_of_not_ge he)]
  unfold badLengthTailAction
  apply Finset.sum_congr rfl
  intro I hI
  have hi := (Finset.mem_filter.mp (hN hI)).2
  have hbase : (2 : ℝ) ^ (k₀ + s) ≤ I.length := by
    rw [hi.1]
    exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  have hell : (2 : ℝ) ^ ell ≤ I.length :=
    (zpow_le_zpow_right₀ (by norm_num) (le_of_not_ge he)).trans hbase
  rw [ite_eq_left hbase, ite_eq_left hell]

/--
@isnad1 id=eq.2h8v.s7.0f56736d5d58 from=translated src=- shape=33d52054 vocab=85f90a17
-/
theorem nonstandardSourceTailMaximal_eq_badLengthTailMaximal
    {S : Finset RealInterval} (f : ℝ → ℂ) (I₀ : RealInterval) (k₀ s : ℤ)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) (x : ℝ) :
    nonstandardSourceTailMaximal S f I₀ k₀ s scale N x =
      badLengthTailMaximal S f I₀ k₀ s scale N x := by
  have hb : BddAbove (Set.range fun ell : ℤ ↦ ‖badLengthTailAction S f I₀ k₀ s scale N ell x‖) := by
    refine ⟨2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale N N.card x, ?_⟩
    rintro _ ⟨ell, rfl⟩
    exact norm_badLengthTailAction_le_prefix f I₀ k₀ s scale hlam N hN ell x
  have hbr : BddAbove (Set.range fun ell : {ell : ℤ // k₀ + s ≤ ell} ↦
      ‖badLengthTailAction S f I₀ k₀ s scale N ell.1 x‖) := by
    refine ⟨2 * badSubcollectionPrefixMaximal S f I₀ k₀ s scale N N.card x, ?_⟩
    rintro _ ⟨ell, rfl⟩
    exact norm_badLengthTailAction_le_prefix f I₀ k₀ s scale hlam N hN ell.1 x
  apply le_antisymm
  · exact ciSup_le fun ell ↦ le_ciSup hb ell.1
  · apply ciSup_le
    intro ell
    rw [badLengthTailAction_eq_at_max_lower_endpoint S f I₀ k₀ s scale N hN ell x]
    exact le_ciSup hbr ⟨max ell (k₀ + s), le_max_right _ _⟩

/--
@isnad1 id=le.6h7v.s8.9a8a78daa756 from=translated src=- shape=4eebd1f4 vocab=2a913074
-/
theorem eLpNorm_nonstandardSourceTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ intervals S f I₀ k₀ s scale) :
    eLpNorm (nonstandardSourceTailMaximal S f I₀ k₀ s scale N) 2 volume ≤
      ENNReal.ofReal ((4 * (s : ℝ) + 12) * Real.sqrt (nonstandardSignedEnergyBudget f I₀ s) +
        Real.sqrt (badRemovedEnergyBudget f I₀ s)) := by
  have he : nonstandardSourceTailMaximal S f I₀ k₀ s scale N =
      badLengthTailMaximal S f I₀ k₀ s scale N := funext
    (nonstandardSourceTailMaximal_eq_badLengthTailMaximal f I₀ k₀ s scale hlam N hN)
  rw [he]
  exact eLpNorm_nonstandard_badLengthTailMaximal_le hf I₀ k₀ s hk₀ scale hlam hparent hsub N hN

/-- The unrestricted physical-suffix maximal estimate directly on the
energy classifier's near family, without overlap or cardinality hypotheses.
@isnad1 id=le.6h7v.s8.5a434bfc21ef from=translated src=- shape=4eebd1f4 vocab=ce6421a7
-/
theorem eLpNorm_energyNonstandardSourceTailMaximal_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ : ℤ) (s : ℕ) (hk₀ : 3 ≤ k₀)
    (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hparent : HasDyadicParents S I₀) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (N : Finset RealInterval) (hN : N ⊆ energyNonstandardIntervals S f I₀ k₀ s scale) :
    eLpNorm (nonstandardSourceTailMaximal S f I₀ k₀ s scale N) 2 volume ≤
      ENNReal.ofReal ((4 * (s : ℝ) + 12) * Real.sqrt (nonstandardSignedEnergyBudget f I₀ s) +
        Real.sqrt (badRemovedEnergyBudget f I₀ s)) := by
  apply eLpNorm_nonstandardSourceTailMaximal_le hf I₀ k₀ s hk₀ scale hlam hparent hsub N
  rw [intervals_eq_energyNonstandardIntervals]
  exact hN

end KrauseLaceyScalarNear
end QuadraticCarleson
