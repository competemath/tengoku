import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyNonstandardEnergy
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyGenerationLayers
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyRademacherMenshov

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Genuine nonstandard generation outputs in `L²`

The functions are the actual localized bad-scale operators, grouped by the
proved minimal-generation construction. Disjoint output supports justify
orthogonality within each generation. No signed-sum estimate is assumed.
-/

open Function MeasureTheory Set
open scoped ComplexConjugate

namespace QuadraticCarleson
namespace KrauseLaceyBadScale

open KrauseLaceyStoppingExtraction KrauseLaceyGenerationLayers

set_option autoImplicit false

/--
@isnad1 id=memlp.1h3v.s6.f1de1c516624 from=translated src=- shape=5f080ef2 vocab=a3b6b890
-/
theorem memLp_localizedPiece_of_integrable (k : ℤ) (I : RealInterval)
    {b : ℝ → ℂ} (hb : Integrable b) : MemLp (krauseLaceyLocalizedPiece 1 k I b) 2 := by
  apply (memLp_two_iff_integrable_sq_norm
    (integrable_krauseLaceyLocalizedPiece k I hb).aestronglyMeasurable).mpr
  have h := (integrable_krauseLaceyLocalizedPiece_crossPairing k k I I hb hb).norm
  simpa only [norm_mul, RCLike.norm_conj, ← sq] using h

/-- The actual localized piece, represented in the `L²` space.-/
noncomputable def localizedPieceLp (k : ℤ) (I : RealInterval)
    (b : ℝ → ℂ) (hb : Integrable b) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_localizedPiece_of_integrable k I hb).toLp (krauseLaceyLocalizedPiece 1 k I b)

/--
@isnad1 id=eventual.1h3v.s8.759e05598f8d from=translated src=- shape=49b6813e vocab=60f495f9
-/
theorem localizedPieceLp_ae_eq (k : ℤ) (I : RealInterval)
    (b : ℝ → ℂ) (hb : Integrable b) :
    localizedPieceLp k I b hb =ᵐ[volume] krauseLaceyLocalizedPiece 1 k I b :=
  (memLp_localizedPiece_of_integrable k I hb).coeFn_toLp

/--
@isnad1 id=eq.1h3v.s8.c3d4f06cb94e from=translated src=- shape=1f918a7e vocab=87779767
-/
theorem norm_localizedPieceLp_sq (k : ℤ) (I : RealInterval)
    (b : ℝ → ℂ) (hb : Integrable b) :
    ‖localizedPieceLp k I b hb‖ ^ 2 = ∫ x, ‖krauseLaceyLocalizedPiece 1 k I b x‖ ^ 2 := by
  rw [← KrauseLaceyRademacherMenshov.integral_sq_norm_Lp]
  apply integral_congr_ae
  filter_upwards [localizedPieceLp_ae_eq k I b hb] with x hx
  rw [hx]

/--
@isnad1 id=eq.5h6v.s8.19150812c63e from=translated src=- shape=000b384d vocab=e8ce77f9
-/
theorem inner_localizedPieceLp_eq_zero_of_disjoint
    (j k : ℤ) (I J : RealInterval) (f g : ℝ → ℂ)
    (hf : Integrable f) (hg : Integrable g)
    (hI : I.length = (2 : ℝ) ^ (k + 2))
    (hJ : J.length = (2 : ℝ) ^ (j + 2))
    (hdisj : Disjoint I.carrier J.carrier) :
    inner ℝ (localizedPieceLp k I f hf) (localizedPieceLp j J g hg) = 0 := by
  rw [L2.inner_def]
  have hzero : (fun x ↦ inner ℝ (localizedPieceLp k I f hf x)
      (localizedPieceLp j J g hg x)) =ᵐ[volume] 0 := by
    filter_upwards [localizedPieceLp_ae_eq k I f hf, localizedPieceLp_ae_eq j J g hg]
      with x hx hy
    rw [hx, hy]
    by_cases hxI : x ∈ I.carrier
    · have hxJ : x ∉ J.carrier := fun hxJ ↦ Set.disjoint_left.mp hdisj hxI hxJ
      rw [krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 j J g hJ hxJ, inner_zero_right]
      rfl
    · rw [krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 k I f hI hxI, inner_zero_left]
      rfl
  rw [integral_congr_ae hzero]
  simp

/--
@isnad1 id=eq.1h4v.s7.54a8e62f6df8 from=translated src=- shape=b2d5bee8 vocab=b9e386c4
-/
theorem norm_sum_sq_eq_sum_of_inner_zero
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Finset ι) (v : ι → E)
    (horth : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → inner ℝ (v i) (v j) = 0) :
    ‖∑ i ∈ S, v i‖ ^ 2 = ∑ i ∈ S, ‖v i‖ ^ 2 := by
  classical
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · exact real_inner_self_eq_norm_sq _
  · intro j hj hji
    exact horth i hi j hj hji.symm
  · intro hn
    exact (hn hi).elim

/-- The actual bad piece at the interval's physical scale.-/
noncomputable def badPieceLp
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (I : RealInterval) : Lp ℂ 2 (volume : Measure ℝ) :=
  localizedPieceLp (scale I) I (badScaleInput S f I₀ k₀ (scale I + 2 - s))
    (integrable_badScaleInput S hf I₀ k₀ _)

/-- The genuine generation function `β_n`, as an `L²` element.-/
noncomputable def nonstandardGenerationLp
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (n : ℕ) : Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ I ∈ generation (nonstandardIntervals S f I₀ k₀ s scale) n,
    badPieceLp S f hf I₀ k₀ s scale I

/-- The generation is a.e. equal to its actual finite integral-operator
sum; the `Lp` representative has not changed the mathematical output.
@isnad1 id=eventual.1h7v.s8.ca071dc68767 from=translated src=- shape=efcb19ba vocab=ad1cba0d
-/
theorem nonstandardGenerationLp_ae_eq
    (S : Finset RealInterval) (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ) (n : ℕ) :
    nonstandardGenerationLp S f hf I₀ k₀ s scale n =ᵐ[volume]
      krauseLaceyCollectionAction (generation (nonstandardIntervals S f I₀ k₀ s scale) n)
        scale (fun I ↦ badScaleInput S f I₀ k₀ (scale I + 2 - s)) := by
  have hsum := Lp.coeFn_finsetSum
    (generation (nonstandardIntervals S f I₀ k₀ s scale) n)
    (badPieceLp S f hf I₀ k₀ s scale)
  apply hsum.trans
  have hall : ∀ᵐ x ∂volume, ∀ I ∈ generation (nonstandardIntervals S f I₀ k₀ s scale) n,
      badPieceLp S f hf I₀ k₀ s scale I x =
        krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x := by
    apply (ae_ball_iff (Finset.countable_toSet _)).mpr
    intro I hI
    exact localizedPieceLp_ae_eq _ _ _ _
  filter_upwards [hall] with x hx
  simp only [Finset.sum_apply, krauseLaceyCollectionAction]
  exact Finset.sum_congr rfl hx

/-- Disjointness of the actual minimal layer gives exact orthogonality,
so its squared norm is the sum of the genuine individual energies.
@isnad1 id=eq.2h7v.s8.e24b06d4b4e0 from=translated src=- shape=27c0bd6a vocab=f181c2de
-/
theorem norm_nonstandardGenerationLp_sq_eq
    {S : Finset RealInterval} (f : ℝ → ℂ) (hf : Integrable f) (I₀ : RealInterval)
    (k₀ s : ℤ) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (n : ℕ) :
    ‖nonstandardGenerationLp S f hf I₀ k₀ s scale n‖ ^ 2 =
      ∑ I ∈ generation (nonstandardIntervals S f I₀ k₀ s scale) n,
        ∫ x, ‖krauseLaceyLocalizedPiece 1 (scale I) I
          (badScaleInput S f I₀ k₀ (scale I + 2 - s)) x‖ ^ 2 := by
  classical
  let N := nonstandardIntervals S f I₀ k₀ s scale
  have hN := nonstandardIntervals_subset S f I₀ k₀ s scale
  have hdisj := generation_pairwiseDisjoint
    (S := N) (fun I hI J hJ hne ↦ hlam (hN hI) (hN hJ) hne) n
  rw [nonstandardGenerationLp, norm_sum_sq_eq_sum_of_inner_zero]
  · apply Finset.sum_congr rfl
    intro I hI
    exact norm_localizedPieceLp_sq _ _ _ _
  · intro I hI J hJ hne
    exact inner_localizedPieceLp_eq_zero_of_disjoint _ _ _ _ _ _ _ _
      (Finset.mem_filter.mp (generation_subset N n hI)).2.1
      (Finset.mem_filter.mp (generation_subset N n hJ)).2.1
      (hdisj hI hJ hne)

/-- Each actual nonstandard generation has the derived diagonal energy
bound, uniformly in the number of its intervals and their scales.
@isnad1 id=le.5h7v.s9.21495632c0f9 from=translated src=- shape=44f2f491 vocab=47a44770
-/
theorem norm_nonstandardGenerationLp_sq_le
    {S : Finset RealInterval} {f : ℝ → ℂ} (hf : Integrable f)
    (I₀ : RealInterval) (k₀ s : ℤ) (hk₀ : 0 ≤ k₀) (scale : RealInterval → ℤ)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (hparent : HasDyadicParents S I₀)
    (hsub : ∀ K ∈ S, K.carrier ⊆ I₀.carrier) (n : ℕ) :
    ‖nonstandardGenerationLp S f hf I₀ k₀ s scale n‖ ^ 2 ≤
      (96000 * positiveDyadicAmplitudeBound ^ 2 * intervalL1Average f I₀ *
        (2 : ℝ) ^ (-s)) * ∫ x, ‖f x‖ := by
  rw [norm_nonstandardGenerationLp_sq_eq f hf I₀ k₀ s scale hlam n]
  exact sum_nonstandard_badPiece_diagonalEnergy_le hf I₀ k₀ s hk₀ scale hlam hparent hsub
    _ (generation_subset _ n)

end KrauseLaceyBadScale
end QuadraticCarleson
