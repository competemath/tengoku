/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Seed.Analysis.InnerProductSpace.Dual
import Tengoku.Seed.Analysis.Normed.Module.DoubleDual
import Tengoku.Seed.MeasureTheory.Function.L2Space
import Tengoku.Seed.MeasureTheory.Function.ConvergenceInMeasure
import Tengoku.Seed.MeasureTheory.Function.LpSeminorm.CompareExp
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic
import Tengoku.Randomsettheory.RandomSetTheory.AumannExpectation
import Tengoku.Randomsettheory.RandomSetTheory.AEModification
import Tengoku.Randomsettheory.RandomSetTheory.AumannBinaryPurification
import Tengoku.Randomsettheory.RandomSetTheory.AumannConvexification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Closedness of finite-dimensional Aumann expectations

This file proves the standard compactness theorem for Aumann expectations of
integrably bounded correspondences in finite dimension.

The analytic core realizes an Aumann expectation with a square-integrable
envelope as the image of a closed, convex and bounded subset of `L²`.  Weak
compactness of Hilbert balls then makes this image compact.  A strictly
positive change of density reduces a merely integrable envelope to the `L²`
case.  An almost-everywhere regularization removes any pointwise measurability
requirement on the chosen envelope.

For convex closed fibres, atomlessness and Effros measurability are not
needed.  For arbitrary compact nonempty Effros fibres, finite atomlessness is
used only by the already established purification theorem
`aumannExpectation_closedConvexHull_eq_of_atomless`.  The final endpoint
`closure_aumannExpectation_eq_of_atomless` therefore removes the auxiliary
`closure` from the Aumann expectation under exactly the hypotheses used in
the random-set applications.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Topology
open scoped InnerProductSpace

noncomputable section

open MeasureTheory Filter Metric

namespace RandomSetTheory

/-- A real Hilbert space is reflexive, expressed as surjectivity of its
canonical embedding into the weak-star bidual.-/
theorem inclusionInDoubleDualWeak_surjective_real_hilbert
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] :
    Function.Surjective (NormedSpace.inclusionInDoubleDualWeak ℝ H) := by
  intro Phi
  let Phi' : StrongDual ℝ (StrongDual ℝ H) :=
    WeakDual.toStrongDual Phi
  let psi : StrongDual ℝ H :=
    Phi'.comp (InnerProductSpace.toDual ℝ H).toContinuousLinearEquiv.toContinuousLinearMap
  let x : H := (InnerProductSpace.toDual ℝ H).symm psi
  refine ⟨x, ?_⟩
  apply DFunLike.ext _ _
  intro ell
  change ell x = Phi ell
  let y : H := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual ell)
  have hell : WeakDual.toStrongDual ell = InnerProductSpace.toDual ℝ H y := by
    simp [y]
  have hpsi : psi y = Phi ell := by
    change Phi' (InnerProductSpace.toDual ℝ H y) = Phi ell
    rw [← hell]
    rfl
  have hxpsi : InnerProductSpace.toDual ℝ H x = psi := by simp [x]
  have hx : ⟪x, y⟫_ℝ = Phi ell := by
    rw [← InnerProductSpace.toDual_apply_apply, hxpsi, hpsi]
  have hellx : ell x = ⟪y, x⟫_ℝ := by
    change (WeakDual.toStrongDual ell) x = _
    rw [hell]
    rfl
  rw [hellx, real_inner_comm, hx]

/-- A closed convex bounded subset of a real Hilbert space is compact for the
weak topology.-/
theorem isCompact_toWeakSpace_image_of_isClosed_convex_isBounded
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {C : Set H}
    (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hCbounded : Bornology.IsBounded C) :
    IsCompact ((toWeakSpace ℝ H) '' C) := by
  let S : Set (WeakSpace ℝ H) := (toWeakSpace ℝ H) '' C
  have hpre : (toWeakSpace ℝ H) ⁻¹' S = C := by
    ext x
    simp [S]
  have hSclosure : closure S = S := by
    have h := hCconv.toWeakSpace_closure ℝ
    rw [hCclosed.closure_eq] at h
    simpa [S] using h.symm
  change IsCompact S
  rw [← hSclosure]
  apply NormedSpace.isCompact_closure_of_isBounded ℝ H S
  · rwa [hpre]
  · intro z hz
    exact inclusionInDoubleDualWeak_surjective_real_hilbert z

/-- The image of a closed convex bounded Hilbert subset under a continuous
linear map to a finite-dimensional space is compact.-/
theorem isCompact_image_clm_of_isClosed_convex_isBounded_hilbert
    {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {C : Set H} (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hCbounded : Bornology.IsBounded C) (L : H →L[ℝ] E) :
    IsCompact (L '' C) := by
  let S : Set (WeakSpace ℝ H) := (toWeakSpace ℝ H) '' C
  have hScompact : IsCompact S := by
    exact isCompact_toWeakSpace_image_of_isClosed_convex_isBounded
      hCclosed hCconv hCbounded
  let T : Set (WeakSpace ℝ E) := WeakSpace.map L '' S
  have hTcompact : IsCompact T :=
    hScompact.image (WeakSpace.map L).continuous
  have hTclosed : IsClosed T := hTcompact.isClosed
  have himage : L '' C = (toWeakSpace ℝ E) ⁻¹' T := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨toWeakSpace ℝ H x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨x, hx, rfl⟩, hw⟩
      have hw' : L x = y := by
        exact (toWeakSpace ℝ E).injective hw
      exact ⟨x, hx, hw'⟩
  apply Metric.isCompact_iff_isClosed_bounded.2
  constructor
  · rw [himage]
    exact hTclosed.preimage (toWeakSpaceCLM ℝ E).continuous
  · exact hCbounded.image L

/-- The set of `L²` classes whose representatives select `S` almost
everywhere.-/
def l2SelectionSet
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu : Measure Omega) (S : Omega → Set E) : Set (Omega →₂[mu] E) :=
  {F | ∀ᵐ omega ∂mu, F omega ∈ S omega}

theorem l2SelectionSet_convex
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu : Measure Omega) {S : Omega → Set E}
    (hSconv : ∀ omega, Convex ℝ (S omega)) :
    Convex ℝ (l2SelectionSet mu S) := by
  intro F hF G hG a b ha hb hab
  filter_upwards [hF, hG, Lp.coeFn_add (a • F) (b • G),
    Lp.coeFn_smul a F, Lp.coeFn_smul b G] with omega hFomega hGomega hadd haF hbG
  rw [hadd]
  change (a • F) omega + (b • G) omega ∈ S omega
  rw [haF, hbG]
  change a • F omega + b • G omega ∈ S omega
  exact hSconv omega hFomega hGomega ha hb hab

theorem l2SelectionSet_isClosed
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (mu : Measure Omega) {S : Omega → Set E}
    (hSclosed : ∀ omega, IsClosed (S omega)) :
    IsClosed (l2SelectionSet mu S) := by
  apply IsSeqClosed.isClosed
  intro F z hF hFz
  have hmeasure : TendstoInMeasure mu (fun n => (F n : Omega → E)) atTop z :=
    tendstoInMeasure_of_tendsto_Lp hFz
  obtain ⟨phi, _hphi, hphiAE⟩ := hmeasure.exists_seq_tendsto_ae
  have hmemAE : ∀ᵐ omega ∂mu, ∀ n, F n omega ∈ S omega :=
    ae_all_iff.2 hF
  filter_upwards [hphiAE, hmemAE] with omega hconv hmem
  exact (hSclosed omega).mem_of_tendsto hconv
    (Filter.Eventually.of_forall fun n => hmem (phi n))

theorem l2SelectionSet_isBounded_of_memLp_envelope
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu : Measure Omega) {S : Omega → Set E} {g : Omega → ℝ}
    (hg : MemLp g 2 mu)
    (hdom : ∀ omega, ∀ x ∈ S omega, ‖x‖ ≤ g omega) :
    Bornology.IsBounded (l2SelectionSet mu S) := by
  let G : Omega →₂[mu] ℝ := hg.toLp g
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨‖G‖, ?_⟩
  intro F hF
  rw [mem_closedBall, dist_zero_right]
  have hnormAE : ∀ᵐ omega ∂mu, ‖F omega‖ ≤ ‖G omega‖ := by
    filter_upwards [hF, hg.coeFn_toLp] with omega hFomega hGomega
    rw [hGomega]
    have hg0 : 0 ≤ g omega := (norm_nonneg _).trans (hdom omega _ hFomega)
    simpa [Real.norm_eq_abs, abs_of_nonneg hg0] using hdom omega _ hFomega
  have hLp : eLpNorm F 2 mu ≤ eLpNorm G 2 mu :=
    eLpNorm_mono_ae hnormAE
  rw [Lp.norm_def, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top G) hLp

def l2ToL1LinearMap
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu : Measure Omega) [IsProbabilityMeasure mu] :
    (Omega →₂[mu] E) →ₗ[ℝ] (Omega →₁[mu] E) where
  toFun F := ⟨F.1, Lp.antitone (E := E) (μ := mu)
    (show (1 : ENNReal) ≤ 2 by norm_num) F.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def l2ToL1CLM
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mu : Measure Omega) [IsProbabilityMeasure mu] :
    (Omega →₂[mu] E) →L[ℝ] (Omega →₁[mu] E) :=
  LinearMap.mkContinuous (l2ToL1LinearMap mu) 1 (by
    intro F
    rw [one_mul, Lp.norm_def, Lp.norm_def]
    apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top F)
    exact eLpNorm_le_eLpNorm_of_exponent_le
      (show (1 : ENNReal) ≤ 2 by norm_num) (Lp.memLp F).1)

def integralL2CLM
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure Omega) [IsProbabilityMeasure mu] :
    (Omega →₂[mu] E) →L[ℝ] E :=
  L1.integralCLM.comp (l2ToL1CLM mu)

theorem integralL2CLM_apply
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : Omega →₂[mu] E) :
    integralL2CLM mu F = ∫ omega, F omega ∂mu := by
  have hFint : Integrable (fun omega => F omega) mu :=
    memLp_one_iff_integrable.mp ((Lp.memLp F).mono_exponent (by norm_num))
  rw [MeasureTheory.integral_eq _ hFint]
  change L1.integralCLM (l2ToL1CLM mu F) = L1.integral (hFint.toL1 F)
  rw [← L1.integral_eq]
  congr 1
  apply Lp.ext
  exact hFint.coeFn_toL1.symm

/-- Under an `L²` envelope, the Aumann expectation is exactly the image under
the continuous `L²` integral map of the closed selection set.-/
theorem aumannExpectation_eq_integralL2CLM_image
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (S : Omega → Set E) {g : Omega → ℝ} (hg : MemLp g 2 mu)
    (hdom : ∀ omega, ∀ x ∈ S omega, ‖x‖ ≤ g omega) :
    aumannExpectation mu S =
      integralL2CLM mu '' l2SelectionSet mu S := by
  apply Set.Subset.antisymm
  · rintro z ⟨f, hf, rfl⟩
    have hf2 : MemLp f 2 mu := by
      apply hg.mono' hf.1.aestronglyMeasurable
      filter_upwards [hf.2] with omega hfomega
      exact hdom omega _ hfomega
    let F : Omega →₂[mu] E := hf2.toLp f
    have hFmem : F ∈ l2SelectionSet mu S := by
      filter_upwards [hf.2, hf2.coeFn_toLp] with omega hfomega hFomega
      rwa [hFomega]
    refine ⟨F, hFmem, ?_⟩
    rw [integralL2CLM_apply]
    exact integral_congr_ae hf2.coeFn_toLp
  · rintro z ⟨F, hFmem, rfl⟩
    have hFint : Integrable (fun omega => F omega) mu :=
      memLp_one_iff_integrable.mp ((Lp.memLp F).mono_exponent (by norm_num))
    refine ⟨fun omega => F omega, ⟨hFint, hFmem⟩, ?_⟩
    exact (integralL2CLM_apply mu F).symm

/-- A closed convex correspondence dominated by an `L²` envelope has compact
Aumann expectation on a probability space.-/
theorem aumannExpectation_isCompact_of_memLp_two_envelope
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {S : Omega → Set E} (hclosed : ∀ omega, IsClosed (S omega))
    (hconv : ∀ omega, Convex ℝ (S omega))
    {g : Omega → ℝ} (hg : MemLp g 2 mu)
    (hdom : ∀ omega, ∀ x ∈ S omega, ‖x‖ ≤ g omega) :
    IsCompact (aumannExpectation mu S) := by
  rw [aumannExpectation_eq_integralL2CLM_image mu S hg hdom]
  exact isCompact_image_clm_of_isClosed_convex_isBounded_hilbert
    (l2SelectionSet_isClosed mu hclosed)
    (l2SelectionSet_convex mu hconv)
    (l2SelectionSet_isBounded_of_memLp_envelope mu hg hdom)
    (integralL2CLM mu)

/-- Rescale each fibre by the reciprocal of a strictly positive density.-/
def inverseDensityCorrespondence
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : Omega → NNReal) (S : Omega → Set E) : Omega → Set E :=
  fun omega => (fun x => ((r omega : ℝ)⁻¹) • x) '' S omega

/- Changing simultaneously the base measure by a positive density and each
fibre by the reciprocal density leaves the Aumann expectation unchanged. -/
set_option maxHeartbeats 800000 in
theorem aumannExpectation_inverseDensityCorrespondence
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (mu : Measure Omega) (r : Omega → NNReal) (hr : Measurable r)
    (hrpos : ∀ omega, 0 < r omega) (S : Omega → Set E) :
    aumannExpectation (mu.withDensity fun omega => (r omega : ENNReal))
        (inverseDensityCorrespondence r S) =
      aumannExpectation mu S := by
  let nu : Measure Omega := mu.withDensity fun omega => (r omega : ENNReal)
  have hrE : Measurable fun omega => (r omega : ENNReal) := hr.coe_nnreal_ennreal
  have hrnz : ∀ᵐ omega ∂mu, (r omega : ENNReal) ≠ 0 := by
    filter_upwards [] with omega
    exact_mod_cast (hrpos omega).ne'
  apply Set.Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    let f : Omega → E := fun omega => (r omega : ℝ) • t omega
    have hfint : Integrable f mu := by
      exact (integrable_withDensity_iff_integrable_smul hr).mp ht.1
    have hfmem : ∀ᵐ omega ∂mu, f omega ∈ S omega := by
      have htmem : ∀ᵐ omega ∂nu,
          t omega ∈ inverseDensityCorrespondence r S omega := ht.2
      have htmem' : ∀ᵐ omega ∂mu,
          t omega ∈ inverseDensityCorrespondence r S omega :=
        (withDensity_absolutelyContinuous' hrE.aemeasurable hrnz).ae_le htmem
      filter_upwards [htmem'] with omega htomega
      rcases htomega with ⟨x, hx, htx⟩
      change (r omega : ℝ) • t omega ∈ S omega
      rw [← htx]
      have hrne : (r omega : ℝ) ≠ 0 := by
        exact_mod_cast (hrpos omega).ne'
      simpa [smul_smul, hrne] using hx
    refine ⟨f, ⟨hfint, hfmem⟩, ?_⟩
    rw [integral_withDensity_eq_integral_smul hr]
    rfl
  · rintro z ⟨f, hf, rfl⟩
    let t : Omega → E := fun omega => ((r omega : ℝ)⁻¹) • f omega
    have htint : Integrable t nu := by
      rw [integrable_withDensity_iff_integrable_smul hr]
      simp_rw [NNReal.smul_def]
      have hfun : (fun omega => (r omega : ℝ) • t omega) = f := by
        funext omega
        have hrne : (r omega : ℝ) ≠ 0 := by
          exact_mod_cast (hrpos omega).ne'
        simp [t, smul_smul, hrne]
      rw [hfun]
      exact hf.1
    have htmemMu : ∀ᵐ omega ∂mu,
        t omega ∈ inverseDensityCorrespondence r S omega := by
      filter_upwards [hf.2] with omega hfomega
      exact ⟨f omega, hfomega, rfl⟩
    have htmemNu : ∀ᵐ omega ∂nu,
        t omega ∈ inverseDensityCorrespondence r S omega :=
      (withDensity_absolutelyContinuous mu
        (fun omega => (r omega : ENNReal))).ae_le htmemMu
    refine ⟨t, ⟨htint, htmemNu⟩, ?_⟩
    rw [integral_withDensity_eq_integral_smul hr]
    apply integral_congr_ae
    filter_upwards [] with omega
    have hrne : (r omega : ℝ) ≠ 0 := by
      exact_mod_cast (hrpos omega).ne'
    simp [NNReal.smul_def, t, smul_smul, hrne]

/-- A closed convex finite-dimensional correspondence dominated by a
measurable integrable envelope has compact raw Aumann expectation.-/
theorem aumannExpectation_isCompact_of_integrable_envelope
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {S : Omega → Set E} (hclosed : ∀ omega, IsClosed (S omega))
    (hconv : ∀ omega, Convex ℝ (S omega))
    {g : Omega → ℝ} (hgmeas : Measurable g) (hgint : Integrable g mu)
    (hg0 : ∀ omega, 0 ≤ g omega)
    (hdom : ∀ omega, ∀ x ∈ S omega, ‖x‖ ≤ g omega) :
    IsCompact (aumannExpectation mu S) := by
  let h : Omega → ℝ := fun omega => 1 + g omega
  let c : ℝ := ∫ omega, h omega ∂mu
  have hhint : Integrable h mu := (integrable_const 1).add hgint
  have hhmeas : Measurable h := measurable_const.add hgmeas
  have hhpos : ∀ omega, 0 < h omega := fun omega => by
    dsimp [h]
    linarith [hg0 omega]
  have hcEq : c = 1 + ∫ omega, g omega ∂mu := by
    rw [show c = ∫ omega, (1 : ℝ) + g omega ∂mu by rfl]
    rw [integral_add (integrable_const 1) hgint, integral_const]
    simp
  have hgInt0 : 0 ≤ ∫ omega, g omega ∂mu :=
    integral_nonneg hg0
  have hcpos : 0 < c := by rw [hcEq]; linarith
  let r : Omega → NNReal := fun omega => Real.toNNReal (h omega / c)
  have hrmeas : Measurable r :=
    (hhmeas.div_const c).real_toNNReal
  have hratio0 : ∀ omega, 0 ≤ h omega / c := fun omega =>
    div_nonneg (hhpos omega).le hcpos.le
  have hrreal : ∀ omega, (r omega : ℝ) = h omega / c := fun omega => by
    exact Real.coe_toNNReal _ (hratio0 omega)
  have hrpos : ∀ omega, 0 < r omega := fun omega => by
    rw [← NNReal.coe_pos, hrreal]
    exact div_pos (hhpos omega) hcpos
  let nu : Measure Omega :=
    mu.withDensity fun omega => (r omega : ENNReal)
  have hnu : nu Set.univ = 1 := by
    change (mu.withDensity fun omega => (r omega : ENNReal)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    have hratioInt : Integrable (fun omega => h omega / c) mu :=
      hhint.div_const c
    calc
      (∫⁻ omega, (r omega : ENNReal) ∂mu) =
          ∫⁻ omega, ENNReal.ofReal (h omega / c) ∂mu := by
            apply lintegral_congr
            intro omega
            calc
              (r omega : ENNReal) = ENNReal.ofReal (r omega : ℝ) := by simp
              _ = ENNReal.ofReal (h omega / c) := by rw [hrreal]
      _ = ENNReal.ofReal (∫ omega, h omega / c ∂mu) :=
        (ofReal_integral_eq_lintegral_ofReal hratioInt
          (Filter.Eventually.of_forall hratio0)).symm
      _ = 1 := by
        rw [integral_div]
        simp [c, hcpos.ne']
  letI : IsProbabilityMeasure nu := ⟨hnu⟩
  let T : Omega → Set E := inverseDensityCorrespondence r S
  have hTclosed : ∀ omega, IsClosed (T omega) := by
    intro omega
    have hrne : (r omega : ℝ) ≠ 0 := by
      exact_mod_cast (hrpos omega).ne'
    have ha : ((r omega : ℝ)⁻¹) ≠ 0 := inv_ne_zero hrne
    simpa only [T, inverseDensityCorrespondence, Set.image_smul] using
      (hclosed omega).smul_of_ne_zero ha
  have hTconv : ∀ omega, Convex ℝ (T omega) := by
    intro omega
    simpa only [T, inverseDensityCorrespondence, Set.image_smul] using
      (hconv omega).smul ((r omega : ℝ)⁻¹)
  have hTdom : ∀ omega, ∀ x ∈ T omega, ‖x‖ ≤ c := by
    intro omega x hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (show 0 ≤ (r omega : ℝ) from (hrpos omega).le))]
    calc
      (r omega : ℝ)⁻¹ * ‖y‖ ≤ (r omega : ℝ)⁻¹ * g omega :=
        mul_le_mul_of_nonneg_left (hdom omega y hy) (inv_nonneg.mpr (hrpos omega).le)
      _ ≤ c := by
        rw [hrreal]
        rw [inv_div, div_mul_eq_mul_div]
        apply (div_le_iff₀ (hhpos omega)).2
        dsimp [h]
        nlinarith [hcpos, hg0 omega]
  have hcMemLp : MemLp (fun _omega : Omega => c) 2 nu :=
    memLp_const c
  have hcompactT : IsCompact (aumannExpectation nu T) :=
    aumannExpectation_isCompact_of_memLp_two_envelope
      nu hTclosed hTconv hcMemLp hTdom
  rw [← aumannExpectation_inverseDensityCorrespondence mu r hrmeas hrpos S]
  exact hcompactT

/-- The preceding compactness theorem without pointwise measurability of the
integrable envelope.  A measurable representative and a null-fibre
regularization discharge that technical issue.-/
theorem aumannExpectation_isCompact_of_integrable_envelope_ae
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {S : Omega → Set E} (hclosed : ∀ omega, IsClosed (S omega))
    (hconv : ∀ omega, Convex ℝ (S omega))
    {g : Omega → ℝ} (hgint : Integrable g mu)
    (hg0 : ∀ omega, 0 ≤ g omega)
    (hdom : ∀ omega, ∀ x ∈ S omega, ‖x‖ ≤ g omega) :
    IsCompact (aumannExpectation mu S) := by
  let gm : Omega → ℝ := hgint.aestronglyMeasurable.mk g
  have hgEq : g =ᵐ[mu] gm := hgint.aestronglyMeasurable.ae_eq_mk
  have hbadNull : mu {omega | gm omega ≠ g omega} = 0 := by
    rw [← ae_iff]
    exact hgEq.symm
  obtain ⟨N, hbadN, hNmeas, hNnull⟩ :=
    exists_measurable_superset_of_null hbadNull
  let A : Set Omega := Nᶜ
  have hAmeas : MeasurableSet A := hNmeas.compl
  have hA : ∀ᵐ omega ∂mu, omega ∈ A := by
    rw [ae_iff]
    simpa [A] using hNnull
  have hAgood : ∀ omega ∈ A, gm omega = g omega := by
    intro omega homega
    by_contra hne
    exact homega (hbadN hne)
  let G : Omega → ℝ := fun omega => max (gm omega) 0
  have hGmeas : Measurable G :=
    hgint.aestronglyMeasurable.measurable_mk.max measurable_const
  have hgmint : Integrable gm mu := hgint.congr hgEq
  have hGint : Integrable G mu := by
    apply hgmint.norm.mono' hGmeas.aestronglyMeasurable
    filter_upwards [] with omega
    dsimp [G]
    rw [abs_of_nonneg (le_max_right (gm omega) 0)]
    exact max_le (le_abs_self _) (abs_nonneg _)
  have hG0 : ∀ omega, 0 ≤ G omega := fun omega => le_max_right _ _
  let T : Omega → Set E := correspondenceOn A S ({0} : Set E)
  have hTclosed : ∀ omega, IsClosed (T omega) :=
    correspondenceOn_isClosed (fun omega _ => hclosed omega) isClosed_singleton
  have hTconv : ∀ omega, Convex ℝ (T omega) :=
    correspondenceOn_convex (fun omega _ => hconv omega)
      (convex_singleton (0 : E))
  have hTdom : ∀ omega, ∀ x ∈ T omega, ‖x‖ ≤ G omega := by
    intro omega x hx
    by_cases homega : omega ∈ A
    · change x ∈ correspondenceOn A S ({0} : Set E) omega at hx
      rw [correspondenceOn_of_mem homega] at hx
      exact (hdom omega x hx).trans <| by
        rw [← hAgood omega homega]
        exact le_max_left _ _
    · change x ∈ correspondenceOn A S ({0} : Set E) omega at hx
      rw [correspondenceOn_of_not_mem homega] at hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      simpa using hG0 omega
  have hcompactT : IsCompact (aumannExpectation mu T) :=
    aumannExpectation_isCompact_of_integrable_envelope
      mu hTclosed hTconv hGmeas hGint hG0 hTdom
  rw [← aumannExpectation_correspondenceOn (S := S) (K := ({0} : Set E)) hA]
  exact hcompactT

/-- Nonempty closed convex fibres automatically force their integrable
envelope to be nonnegative, yielding compactness with no extra envelope
hypothesis.-/
theorem aumannExpectation_isCompact_of_integrable_envelope_nonempty
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {S : Omega → Set E} (hclosed : ∀ omega, IsClosed (S omega))
    (hconv : ∀ omega, Convex ℝ (S omega))
    (hne : ∀ omega, (S omega).Nonempty)
    {g : Omega → ℝ} (hgint : Integrable g mu)
    (hdom : ∀ omega, ∀ x ∈ S omega, ‖x‖ ≤ g omega) :
    IsCompact (aumannExpectation mu S) := by
  have hg0 : ∀ omega, 0 ≤ g omega := by
    intro omega
    obtain ⟨x, hx⟩ := hne omega
    exact (norm_nonneg x).trans (hdom omega x hx)
  exact aumannExpectation_isCompact_of_integrable_envelope_ae
    mu hclosed hconv hgint hg0 hdom

/-- **Finite-dimensional Aumann compactness.**  On an atomless probability
space, every compact nonempty Effros-measurable correspondence with an
integrable envelope has compact raw Aumann expectation.-/
theorem aumannExpectation_isCompact_of_atomless
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (hmu : IsAtomlessMeasure mu)
    {S : Omega → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ omega, IsCompact (S omega))
    (hne : ∀ omega, (S omega).Nonempty)
    {g : Omega → ℝ} (hgint : Integrable g mu)
    (hdom : ∀ omega, ∀ x ∈ S omega, ‖x‖ ≤ g omega) :
    IsCompact (aumannExpectation mu S) := by
  let C : Omega → Set E := fun omega => closedConvexHull ℝ (S omega)
  have hCcompact : ∀ omega, IsCompact (C omega) := fun omega =>
    closedConvexHull_compact (hcompact omega)
  have hCclosed : ∀ omega, IsClosed (C omega) := fun omega =>
    (hCcompact omega).isClosed
  have hCconv : ∀ omega, Convex ℝ (C omega) := fun _ =>
    convex_closedConvexHull
  have hCne : ∀ omega, (C omega).Nonempty := fun omega =>
    (hne omega).mono subset_closedConvexHull
  have hCdom : ∀ omega, ∀ x ∈ C omega, ‖x‖ ≤ g omega := fun omega =>
    norm_le_on_closedConvexHull_of_norm_le (hdom omega)
  have hCcompactA : IsCompact (aumannExpectation mu C) :=
    aumannExpectation_isCompact_of_integrable_envelope_nonempty
      mu hCclosed hCconv hCne hgint hCdom
  have hpur : aumannExpectation mu C = aumannExpectation mu S :=
    aumannExpectation_closedConvexHull_eq_of_atomless
      mu hmu hS hcompact hne hgint hdom
  rwa [hpur] at hCcompactA

/-- The raw Aumann expectation in the atomless finite-dimensional setting is
closed.-/
theorem aumannExpectation_isClosed_of_atomless
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (hmu : IsAtomlessMeasure mu)
    {S : Omega → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ omega, IsCompact (S omega))
    (hne : ∀ omega, (S omega).Nonempty)
    {g : Omega → ℝ} (hgint : Integrable g mu)
    (hdom : ∀ omega, ∀ x ∈ S omega, ‖x‖ ≤ g omega) :
    IsClosed (aumannExpectation mu S) :=
  (aumannExpectation_isCompact_of_atomless
    mu hmu hS hcompact hne hgint hdom).isClosed

/-- Closure is redundant for an atomless finite-dimensional Aumann
expectation of an integrably bounded compact random set.-/
theorem closure_aumannExpectation_eq_of_atomless
    {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (hmu : IsAtomlessMeasure mu)
    {S : Omega → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ omega, IsCompact (S omega))
    (hne : ∀ omega, (S omega).Nonempty)
    {g : Omega → ℝ} (hgint : Integrable g mu)
    (hdom : ∀ omega, ∀ x ∈ S omega, ‖x‖ ≤ g omega) :
    closure (aumannExpectation mu S) = aumannExpectation mu S :=
  (aumannExpectation_isClosed_of_atomless
    mu hmu hS hcompact hne hgint hdom).closure_eq

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
