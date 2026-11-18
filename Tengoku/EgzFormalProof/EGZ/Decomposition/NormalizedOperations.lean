import Tengoku.EgzFormalProof.EGZ.Decomposition.NormalizedFace
import Tengoku.EgzFormalProof.EGZ.Decomposition.NormalizedGap
import Tengoku.EgzFormalProof.EGZ.Decomposition.NormalizedComplete

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform providers for normalized refinement operations

The three concrete operations share a single increasing radius bound and a
monotone prime threshold. A finite radius horizon therefore fixes the prime
before any choices in the refinement run are made.
-/

namespace EGZ

open FlagDecomposition

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}

/-- Concrete chart data for a normalized face operation.-/
structure NormalizedFaceStep (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (Γ : (Φ.flag.polytope anchor).Face) (K R : ℕ) where
  odd : Odd p
  charts : ∀ x, IntegerLatticeChart
    ((FaceRefinement.decomposition Φ anchor (Φ.faceSelector anchor Γ) odd).liftedSupport x)
  modInjective : ∀ x, Function.Injective ((Rechart.chart
    (FaceRefinement.decomposition Φ anchor (Φ.faceSelector anchor Γ) odd) charts x).modp p)
  centered : ∀ x q, q ∈ (charts x).coordinateSupport → IsCenteredLift p q
  radius : ℕ
  radius_ge : K ≤ radius
  radius_le : radius ≤ R
  bounded : (FaceRefinement.normalized Φ anchor Γ odd charts modInjective centered).IsKBounded
    (fun _ ↦ radius)

noncomputable abbrev NormalizedFaceStep.decomposition
    {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node}
    {Γ : (Φ.flag.polytope anchor).Face} {K R : ℕ} (D : NormalizedFaceStep Φ anchor Γ K R) :=
  FaceRefinement.normalized Φ anchor Γ D.odd D.charts D.modInjective D.centered

/-- Concrete deletion and chart data for normalized gap cleanup.-/
structure NormalizedGapStep (Φ : FlagDecomposition p d f) (K R : ℕ) (α : ℝ) where
  weights : PrunedWeights Φ
  odd : Odd p
  charts : ∀ x, IntegerLatticeChart ((weights.cleaned odd).liftedSupport x)
  modInjective : ∀ x, Function.Injective ((Rechart.chart (weights.cleaned odd) charts x).modp p)
  centered : ∀ x q, q ∈ (charts x).coordinateSupport → IsCenteredLift p q
  radius : ℕ
  radius_ge : K ≤ radius
  radius_le : radius ≤ R
  atoms : ∀ x v, weights.weight x v = 0 ∨ weights.weight x v = Φ.localWeight x v
  bounded : (weights.normalized odd charts modInjective centered).IsKBounded (fun _ ↦ radius)
  mass_loss : (Φ.retainedMass : ℝ) -
    (weights.normalized odd charts modInjective centered).retainedMass ≤ α * Φ.retainedMass
  gap_bound : ∀ x, α * (Φ.retainedMass : ℝ) /
    ((Fintype.card Φ.flag.Node : ℝ) * (2 * (radius : ℝ) + 1) ^ d) ≤
      ((weights.normalized odd charts modInjective centered).gap x : ℝ)

noncomputable abbrev NormalizedGapStep.decomposition
    {Φ : FlagDecomposition p d f} {K R : ℕ} {α : ℝ} (D : NormalizedGapStep Φ K R α) :=
  D.weights.normalized D.odd D.charts D.modInjective D.centered

/-- Concrete selected directions, active nodes, and charts for a normalized
complete-element operation.-/
structure NormalizedCompleteStep (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (g : ℕ → ℕ) (K R : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1) where
  odd : Odd p
  widths : ℕ → ℕ
  preparation : CompletePreparation Φ anchor widths δ
  charts : ∀ x, IntegerLatticeChart ((preparation.diagram odd hδ hsmall).support x)
  modInjective : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (charts x).map).modp p)
  centered : ∀ x q, q ∈ (charts x).coordinateSupport → IsCenteredLift p q
  radius : ℕ
  radius_ge : K ≤ radius
  radius_le : radius ≤ R
  widths_monotone : Monotone widths
  widths_zero : widths 0 = K
  desired_width : g radius ≤ widths (preparation.count + 1)
  bounded : (preparation.normalized odd hδ hsmall charts modInjective centered).IsKBounded
    (fun _ ↦ radius)

noncomputable abbrev NormalizedCompleteStep.decomposition
    {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node}
    {g : ℕ → ℕ} {K R : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}
    {hsmall : (3 : ℝ) ^ (d + 1) * δ < 1}
    (D : NormalizedCompleteStep Φ anchor g K R δ hδ hsmall) :=
  D.preparation.normalized D.odd hδ hsmall D.charts D.modInjective D.centered

namespace NormalizedFaceStep

variable {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node}
    {Γ : (Φ.flag.polytope anchor).Face} {K R : ℕ} (D : NormalizedFaceStep Φ anchor Γ K R)

/--
@isnad1 id=isminima.0h9v.s6.a191c6185df4 from=translated src=- shape=c5d1393f vocab=5714e986
-/
theorem isMinimal : D.decomposition.IsMinimal :=
  FaceRefinement.normalized_isMinimal Φ anchor Γ D.odd D.charts D.modInjective D.centered

/--
@isnad1 id=isreduce.0h9v.s6.7ebbc8c2b788 from=translated src=- shape=c5d1393f vocab=fc8e5d38
-/
theorem isReduced : D.decomposition.IsReduced :=
  FaceRefinement.normalized_isReduced Φ anchor Γ D.odd D.charts D.modInjective D.centered

/--
@isnad1 id=eq.0h9v.s6.cd6056b46ab8 from=translated src=- shape=6637ffb0 vocab=3d3008ed
-/
theorem retainedMass : D.decomposition.retainedMass = Φ.retainedMass :=
  FaceRefinement.normalized_retainedMass Φ anchor Γ D.odd D.charts D.modInjective D.centered

/--
@isnad1 id=le.0h9v.s7.ab6a6a5d98f9 from=translated src=- shape=8da07ee5 vocab=8ac2fdcd
-/
theorem card_le : @Fintype.card D.decomposition.flag.Node D.decomposition.flag.nodeFintype ≤
    2 * Fintype.card Φ.flag.Node :=
  FaceRefinement.normalized_card_le Φ anchor Γ D.odd D.charts D.modInjective D.centered

noncomputable def subdivisionMap : SubdivisionMap Φ D.decomposition :=
  FaceRefinement.normalizedSubdivisionMap Φ anchor Γ D.odd D.charts D.modInjective D.centered

noncomputable abbrev targetNode (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    D.decomposition.flag.Node :=
  FaceRefinement.normalizedTargetNode Φ anchor Γ D.odd D.charts D.modInjective D.centered hΓ hred

noncomputable def targetFace (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (D.decomposition.flag.polytope (D.targetNode hΓ hred)).Face :=
  FaceRefinement.normalizedTargetFace Φ anchor Γ D.odd D.charts D.modInjective D.centered hΓ hred

/--
@isnad1 id=isrealiz.2h9v.s7.172c579de1b8 from=translated src=- shape=4deebd7e vocab=9aeace2a
-/
theorem target_isRealized (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    D.decomposition.IsRealizedFace (D.targetNode hΓ hred) (D.targetFace hΓ hred) :=
  FaceRefinement.normalizedTargetFace_isRealized Φ anchor Γ D.odd D.charts D.modInjective
    D.centered hΓ hred

/--
@isnad1 id=eq.2h9v.s8.038f1a9a312f from=translated src=- shape=967c40a9 vocab=21f87d67
-/
theorem target_projection (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    D.subdivisionMap.node (D.targetNode hΓ hred) = anchor := rfl

/--
@isnad1 id=eq.2h9v.s12.82849562ab19 from=translated src=- shape=349a28b0 vocab=a5946cc4
-/
theorem targetFace_carrier (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (D.targetFace hΓ hred).carrier =
      (D.decomposition.flag.polytope (D.targetNode hΓ hred)).carrier ∩
        D.subdivisionMap.fibre (D.targetNode hΓ hred) ⁻¹' Γ.carrier := rfl

end NormalizedFaceStep

namespace NormalizedGapStep

variable {Φ : FlagDecomposition p d f} {K R : ℕ} {α : ℝ} (D : NormalizedGapStep Φ K R α)

/--
@isnad1 id=isminima.0h8v.s5.7a8db37df50d from=translated src=- shape=d334cf6a vocab=b29df8cf
-/
theorem isMinimal : D.decomposition.IsMinimal :=
  D.weights.normalized_isMinimal D.odd D.charts D.modInjective D.centered

/--
@isnad1 id=isreduce.0h8v.s5.771de27facbc from=translated src=- shape=d334cf6a vocab=f7a4416d
-/
theorem isReduced : D.decomposition.IsReduced :=
  D.weights.normalized_isReduced D.odd D.charts D.modInjective D.centered

/--
@isnad1 id=le.0h8v.s6.ba78d651d2cf from=translated src=- shape=8c88543e vocab=a1111008
-/
theorem card_le : @Fintype.card D.decomposition.flag.Node D.decomposition.flag.nodeFintype ≤
    Fintype.card Φ.flag.Node :=
  D.weights.normalized_card_le D.odd D.charts D.modInjective D.centered

noncomputable def subdivisionMap : SubdivisionMap Φ D.decomposition :=
  D.weights.normalizedSubdivisionMap D.odd D.charts D.modInjective D.centered

end NormalizedGapStep

namespace NormalizedCompleteStep

variable {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node}
    {g : ℕ → ℕ} {K R : ℕ} {δ : ℝ} {hδ : 0 ≤ δ}
    {hsmall : (3 : ℝ) ^ (d + 1) * δ < 1}
    (D : NormalizedCompleteStep Φ anchor g K R δ hδ hsmall)

/--
@isnad1 id=isminima.2h10v.s7.541261ea047b from=translated src=- shape=15af6531 vocab=8261591f
-/
theorem isMinimal : D.decomposition.IsMinimal :=
  D.preparation.normalized_isMinimal D.odd hδ hsmall D.charts D.modInjective D.centered

/--
@isnad1 id=isreduce.2h10v.s7.a53dc3c02893 from=translated src=- shape=15af6531 vocab=7d24b935
-/
theorem isReduced : D.decomposition.IsReduced :=
  D.preparation.normalized_isReduced D.odd hδ hsmall D.charts D.modInjective D.centered

/--
@isnad1 id=le.2h10v.s7.d219b7f95531 from=translated src=- shape=24dcc2b1 vocab=fd0041a0
-/
theorem mass_loss : (Φ.retainedMass : ℝ) - D.decomposition.retainedMass ≤
    (3 : ℝ) ^ (d + 1) * δ * natMass (Φ.cumulativeWeight anchor) :=
  D.preparation.normalized_retainedMass_loss_le D.odd hδ hsmall D.charts D.modInjective D.centered

/--
@isnad1 id=le.2h10v.s7.a23060bc17e0 from=translated src=- shape=fbf2227b vocab=4fa919cf
-/
theorem card_le : @Fintype.card D.decomposition.flag.Node D.decomposition.flag.nodeFintype ≤
    2 * Fintype.card Φ.flag.Node :=
  D.preparation.normalized_card_le D.odd hδ hsmall D.charts D.modInjective D.centered

noncomputable def subdivisionMap : SubdivisionMap Φ D.decomposition :=
  D.preparation.normalizedSubdivisionMap D.odd hδ hsmall D.charts D.modInjective D.centered

noncomputable abbrev targetNode : D.decomposition.flag.Node :=
  D.preparation.normalizedCompleteNode D.odd hδ hsmall D.charts D.modInjective D.centered

/--
@isnad1 id=iscomple.2h10v.s7.1691a4c09f58 from=translated src=- shape=56abed8d vocab=8ad0032e
-/
theorem target_isComplete : D.decomposition.IsCompleteElement D.targetNode (g D.radius) δ :=
  (D.preparation.normalizedCompleteNode_isCompleteElement D.odd hδ hsmall D.charts
    D.modInjective D.centered).mono_width D.desired_width

/--
@isnad1 id=eq.2h10v.s7.6bb04e9c1ced from=translated src=- shape=7a3aa043 vocab=567ef456
-/
theorem target_cumulativeWeight : D.decomposition.cumulativeWeight D.targetNode =
    restrictWeight (Φ.cumulativeWeight anchor) D.preparation.selectedSet :=
  D.preparation.normalizedCompleteNode_cumulativeWeight D.odd hδ hsmall D.charts
    D.modInjective D.centered

/--
@isnad1 id=ne.2h11v.s8.576232c804d1 from=translated src=- shape=d4134b80 vocab=7fab7ec1
-/
theorem node_ne_upperAnchor (x : D.decomposition.flag.Node) :
    x.val ≠ D.preparation.upperAnchor D.odd hδ hsmall :=
  D.preparation.normalized_node_ne_upperAnchor D.odd hδ hsmall D.charts D.modInjective D.centered x

end NormalizedCompleteStep

/-- Uniform numerical parameters together with providers of all three
concrete normalized operations.-/
structure NormalizedOperationParameters (d : ℕ) (g : ℕ → ℕ) where
  radiusGrowth : ℕ → ℕ
  radiusGrowth_growing : IsGrowing radiusGrowth
  primeThreshold : ℕ → ℕ
  primeThreshold_monotone : Monotone primeThreshold
  primeThreshold_ge_two : ∀ K, 2 ≤ primeThreshold K
  face : ∀ K (p : ℕ) [NeZero p] [Fact p.Prime], primeThreshold K < p →
    ∀ (f : FpCoord p d → ℕ) (Φ : FlagDecomposition p d f)
      (anchor : Φ.flag.Node) (Γ : (Φ.flag.polytope anchor).Face), Γ ≠ ⊤ →
      Φ.IsReducedElement anchor → Φ.IsKBounded (fun _ ↦ K) →
      Nonempty (NormalizedFaceStep Φ anchor Γ K (radiusGrowth K))
  gap : ∀ K (p : ℕ) [NeZero p] [Fact p.Prime], primeThreshold K < p →
    ∀ (f : FpCoord p d → ℕ) (Φ : FlagDecomposition p d f),
      Φ.IsKBounded (fun _ ↦ K) → ∀ α : ℝ, 0 ≤ α → α < 1 →
      Nonempty (NormalizedGapStep Φ K (radiusGrowth K) α)
  complete : ∀ K (p : ℕ) [NeZero p] [Fact p.Prime], primeThreshold K < p →
    ∀ (f : FpCoord p d → ℕ) (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
      (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1),
      Φ.IsKBounded (fun _ ↦ K) →
      Nonempty (NormalizedCompleteStep Φ anchor g K (radiusGrowth K) δ hδ hsmall)

/-- Monotone majorant of a numerical threshold, taking a finite maximum
over all smaller radii.-/
def thresholdEnvelope (q : ℕ → ℕ) (K : ℕ) : ℕ := (Finset.range (K + 1)).sup q

/--
@isnad1 id=le.0h2v.s3.6dc1d97967d2 from=translated src=- shape=55ab8e1f vocab=f49b4e96
-/
theorem le_thresholdEnvelope (q : ℕ → ℕ) (K : ℕ) : q K ≤ thresholdEnvelope q K :=
  Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self K))

/--
@isnad1 id=monotone.0h1v.s3.314429ddd27a from=translated src=- shape=6e7f11e6 vocab=6adef7f7
-/
theorem thresholdEnvelope_monotone (q : ℕ → ℕ) : Monotone (thresholdEnvelope q) := by
  intro a b hab
  apply Finset.sup_mono
  exact Finset.range_mono (Nat.add_le_add_right hab 1)

/--
@isnad1 id=nonempty.1h2v.s4.477f12c7431d from=translated src=- shape=2b849c4a vocab=32d92331
-/
theorem exists_normalizedOperationParameters (d : ℕ) (g : ℕ → ℕ) (hg : Monotone g) :
    Nonempty (NormalizedOperationParameters d g) := by
  classical
  obtain ⟨A, hAmono, hAge, hA⟩ := normalized_face_refinement_lemma d
  obtain ⟨B, hBmono, hBge, hB⟩ := normalized_gap_cleanup_lemma d
  obtain ⟨C, hCmono, hCge, hC⟩ := normalized_complete_refinement_lemma d g hg
  let H : ℕ → ℕ := fun K ↦ max (K + 1) (max (A K) (max (B K) (C K)))
  have hH : IsGrowing H := by
    constructor
    · intro i j hij
      exact max_le_max (Nat.add_le_add_right hij 1)
        (max_le_max (hAmono hij) (max_le_max (hBmono hij) (hCmono hij)))
    · intro i
      exact (Nat.lt_succ_self i).trans_le (le_max_left _ _)
  have hAH : ∀ K, A K ≤ H K := fun K ↦ (le_max_left _ _).trans (le_max_right _ _)
  have hBH : ∀ K, B K ≤ H K := fun K ↦
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCH : ∀ K, C K ≤ H K := fun K ↦
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  let qA := fun K ↦ (hA K).choose
  let qB := fun K ↦ (hB K).choose
  let qC := fun K ↦ (hC K).choose
  let q := fun K ↦ max (qA K) (max (qB K) (qC K))
  let Q := thresholdEnvelope q
  have hAQ : ∀ K, qA K ≤ Q K := fun K ↦ (le_max_left _ _).trans (le_thresholdEnvelope q K)
  have hBQ : ∀ K, qB K ≤ Q K := fun K ↦
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_thresholdEnvelope q K))
  have hCQ : ∀ K, qC K ≤ Q K := fun K ↦
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_thresholdEnvelope q K))
  refine ⟨{
    radiusGrowth := H
    radiusGrowth_growing := hH
    primeThreshold := Q
    primeThreshold_monotone := thresholdEnvelope_monotone q
    primeThreshold_ge_two := fun K ↦ (hA K).choose_spec.1.trans (hAQ K)
    face := ?_
    gap := ?_
    complete := ?_ }⟩
  · intro K p _ _ hp f Φ anchor Γ hΓ hred hΦ
    obtain ⟨hp', charts, hmod, hcenter, _hmin, _hred, hbound, _hrest⟩ :=
      (hA K).choose_spec.2 p ((hAQ K).trans_lt hp) f Φ anchor Γ hΓ hred hΦ
    exact ⟨⟨hp', charts, hmod, hcenter, A K, hAge K, hAH K, hbound⟩⟩
  · intro K p _ _ hp f Φ hΦ α hα hαone
    obtain ⟨D, hp', charts, hmod, hcenter, hatoms, _hmin, _hred, hbound, _hcard, hmass, hgap⟩ :=
      (hB K).choose_spec.2 p ((hBQ K).trans_lt hp) f Φ (fun _ ↦ K) hΦ (fun _ ↦ le_rfl)
        α hα hαone
    exact ⟨⟨D, hp', charts, hmod, hcenter, B K, hBge K, hBH K, hatoms, hbound, hmass, hgap⟩⟩
  · intro K p _ _ hp f Φ anchor δ hδ hsmall hΦ
    obtain ⟨hp', t, D, charts, hmod, hcenter, b, hKb, hbC, ht, ht0, hgb,
      _hmin, _hred, hbound, _hrest⟩ :=
      (hC K).choose_spec.2 p ((hCQ K).trans_lt hp) f Φ anchor δ hδ hsmall hΦ
    exact ⟨⟨hp', t, D, charts, hmod, hcenter, b, hKb, hbC.trans (hCH K), ht, ht0, hgb, hbound⟩⟩

noncomputable def normalizedOperationParameters (d : ℕ) (g : ℕ → ℕ) (hg : Monotone g) :
    NormalizedOperationParameters d g := Classical.choice (exists_normalizedOperationParameters d g hg)

namespace NormalizedOperationParameters

variable {d : ℕ} {g : ℕ → ℕ} (P : NormalizedOperationParameters d g)

/--
@isnad1 id=le.0h4v.s4.245310cbe528 from=translated src=- shape=8c915d88 vocab=ee6a0d0b
-/
theorem radiusGrowth_ge (K : ℕ) : K ≤ P.radiusGrowth K := (P.radiusGrowth_growing.2 K).le

def radiusHorizon (K N : ℕ) : ℕ := P.radiusGrowth^[N] K

def primeHorizon (K N : ℕ) : ℕ := P.primeThreshold (P.radiusHorizon K N)

/--
@isnad1 id=le.2h6v.s6.acabf4945c95 from=translated src=- shape=2c4dc931 vocab=aea196ee
-/
theorem radius_sequence_le (r : ℕ → ℕ) {K : ℕ} (hstart : r 0 ≤ K)
    (hstep : ∀ i, r (i + 1) ≤ P.radiusGrowth (r i)) (i : ℕ) :
    r i ≤ P.radiusHorizon K i := by
  induction i with
  | zero => exact hstart
  | succ i hi =>
    change r (i + 1) ≤ P.radiusGrowth^[i + 1] K
    rw [Function.iterate_succ_apply']
    exact (hstep i).trans (P.radiusGrowth_growing.1 hi)

/--
@isnad1 id=monotone.0h4v.s4.56ba60bd0e89 from=translated src=- shape=b67d32f2 vocab=c8553488
-/
theorem radiusHorizon_monotone (K : ℕ) : Monotone (P.radiusHorizon K) := by
  intro i j hij
  exact Function.monotone_iterate_of_id_le P.radiusGrowth_ge hij K

/-- One prime chosen for the finite horizon works at every smaller radius,
including radii produced by arbitrary prior refinement choices.
@isnad1 id=lt.2h7v.s5.7a5b763f1603 from=translated src=- shape=255d3a1a vocab=e0ae5dfd
-/
theorem primeThreshold_lt_of_le_horizon {K N b p : ℕ}
    (hp : P.primeHorizon K N < p) (hb : b ≤ P.radiusHorizon K N) :
    P.primeThreshold b < p := (P.primeThreshold_monotone hb).trans_lt hp

/--
@isnad1 id=lt.4h8v.s6.2fdcebf103be from=translated src=- shape=d2b0a96a vocab=a5ba8133
-/
theorem primeThreshold_lt_of_radius_sequence (r : ℕ → ℕ) {K N p : ℕ}
    (hp : P.primeHorizon K N < p) (hstart : r 0 ≤ K)
    (hstep : ∀ i, r (i + 1) ≤ P.radiusGrowth (r i)) {i : ℕ} (hi : i ≤ N) :
    P.primeThreshold (r i) < p :=
  P.primeThreshold_lt_of_le_horizon hp
    ((P.radius_sequence_le r hstart hstep i).trans (P.radiusHorizon_monotone K hi))

end NormalizedOperationParameters
end EGZ
