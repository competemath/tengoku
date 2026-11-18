import Tengoku.EgzFormalProof.EGZ.Decomposition.FaceSurvival
import Tengoku.EgzFormalProof.EGZ.Decomposition.Minimalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Minimal and reduced face refinements

Minimalizing the active face split and then restricting to reduced nodes
keeps the upper anchor for every proper selected face of a reduced old node.
This gives a normalized operation with unchanged mass and uniform bounds.
-/

namespace EGZ.FlagDecomposition.Rechart

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (C : ∀ x, IntegerLatticeChart (Φ.liftedSupport x))
    (hp : Odd p) (hmod : ∀ x, Function.Injective ((chart Φ C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

/--
@isnad1 id=iff.3h6v.s10.d553435071f2 from=translated src=- shape=26e612ce vocab=0b984a9e
-/
theorem decomposition_isReducedElement_iff (x : Φ.flag.Node) :
    (decomposition Φ C hp hmod hcenter).IsReducedElement x ↔ Φ.IsReducedElement x := by
  rw [(decomposition Φ C hp hmod hcenter).isReducedElement_iff_sup'_localWeight hp,
    Φ.isReducedElement_iff_sup'_localWeight hp]

end EGZ.FlagDecomposition.Rechart

namespace EGZ.FlagDecomposition.FaceRefinement

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (Γ : (Φ.flag.polytope anchor).Face) (hp : Odd p)
    (C : ∀ x, IntegerLatticeChart
      ((decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).liftedSupport x))
    (hmod : ∀ x, Function.Injective
      ((Rechart.chart (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

noncomputable abbrev minimalized : FlagDecomposition p d f :=
  Rechart.decomposition (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C hp hmod hcenter

noncomputable abbrev normalized : FlagDecomposition p d f :=
  (minimalized Φ anchor Γ hp C hmod hcenter).reduced hp

/--
@isnad1 id=isreduce.5h7v.s11.322adb13f187 from=translated src=- shape=6c3d1f5f vocab=e701fdc8
-/
theorem minimalized_upperAnchor_isReduced (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (minimalized Φ anchor Γ hp C hmod hcenter).IsReducedElement
      (upper Φ anchor (Φ.faceSelector anchor Γ) hp anchor) :=
  (Rechart.decomposition_isReducedElement_iff _ _ _ _ _ _).mpr
    (face_upperAnchor_isReduced Φ anchor hp Γ hΓ hred)

noncomputable abbrev normalizedTargetNode (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (normalized Φ anchor Γ hp C hmod hcenter).flag.Node :=
  ⟨upper Φ anchor (Φ.faceSelector anchor Γ) hp anchor,
    minimalized_upperAnchor_isReduced Φ anchor Γ hp C hmod hcenter hΓ hred⟩

noncomputable def normalizedTargetFace (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    ((normalized Φ anchor Γ hp C hmod hcenter).flag.polytope
      (normalizedTargetNode Φ anchor Γ hp C hmod hcenter hΓ hred)).Face :=
  (Rechart.subdivisionMap (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp)
    C hp hmod hcenter).face (upper Φ anchor (Φ.faceSelector anchor Γ) hp anchor)
      (upperFace Φ anchor (Φ.faceSelector anchor Γ) hp anchor Γ)
      (Rechart.face_preimage_nonempty _ _ _ _)

/--
@isnad1 id=isrealiz.5h7v.s11.85da96ffa8a5 from=translated src=- shape=1cbd2c01 vocab=1a635a89
-/
theorem normalizedTargetFace_isRealized (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (normalized Φ anchor Γ hp C hmod hcenter).IsRealizedFace
      (normalizedTargetNode Φ anchor Γ hp C hmod hcenter hΓ hred)
      (normalizedTargetFace Φ anchor Γ hp C hmod hcenter hΓ hred) := by
  apply ((minimalized Φ anchor Γ hp C hmod hcenter).reduced_isRealizedFace_iff hp _ _).mpr
  exact Rechart.decomposition_isRealizedFace
    (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C hp hmod hcenter _ _
    (face_isRealized Φ anchor hp Γ)

/--
@isnad1 id=isminima.3h7v.s11.f86c04d935a1 from=translated src=- shape=59c05697 vocab=0881bd02
-/
theorem normalized_isMinimal : (normalized Φ anchor Γ hp C hmod hcenter).IsMinimal :=
  (minimalized Φ anchor Γ hp C hmod hcenter).reduced_isMinimal hp
    (Rechart.decomposition_isMinimal _ _ _ _ _)

/--
@isnad1 id=isreduce.3h7v.s11.cac1bf89f5a7 from=translated src=- shape=59c05697 vocab=06a83bbc
-/
theorem normalized_isReduced : (normalized Φ anchor Γ hp C hmod hcenter).IsReduced :=
  (minimalized Φ anchor Γ hp C hmod hcenter).reduced_isReduced hp

/--
@isnad1 id=eq.3h7v.s11.68e71d111c9a from=translated src=- shape=d7413377 vocab=1489a89a
-/
@[simp]
theorem normalized_retainedMass :
    (normalized Φ anchor Γ hp C hmod hcenter).retainedMass = Φ.retainedMass := by
  rw [(minimalized Φ anchor Γ hp C hmod hcenter).reduced_retainedMass,
    Rechart.decomposition_retainedMass]
  exact retainedMass Φ anchor (Φ.faceSelector anchor Γ) hp

/--
@isnad1 id=le.3h7v.s11.7977263b6666 from=translated src=- shape=b3d1b711 vocab=04924ef9
-/
theorem normalized_card_le :
    @Fintype.card (normalized Φ anchor Γ hp C hmod hcenter).flag.Node
      (normalized Φ anchor Γ hp C hmod hcenter).flag.nodeFintype ≤
        2 * Fintype.card Φ.flag.Node :=
  ((minimalized Φ anchor Γ hp C hmod hcenter).card_reduced_le hp).trans
    (card_le Φ anchor (Φ.faceSelector anchor Γ) hp)

/--
@isnad1 id=iskbound.5h9v.s12.d61e6790fddb from=translated src=- shape=3f87eb64 vocab=6dac3c16
-/
theorem normalized_isKBounded {K B : ℕ} (hK : Φ.IsKBounded (fun _ ↦ K))
    (hC : ∀ x (q : IntCoord (C x).rank),
      latticeSupNorm ((C x).map q) ≤ K → latticeSupNorm q ≤ B) :
    (normalized Φ anchor Γ hp C hmod hcenter).IsKBounded (fun _ ↦ B) :=
  (minimalized Φ anchor Γ hp C hmod hcenter).reduced_isKBounded hp
    (Rechart.decomposition_isKBounded _ _ _ _ _
      (isKBounded Φ anchor (Φ.faceSelector anchor Γ) hp hK) hC)

noncomputable def normalizedSubdivisionMap :
    SubdivisionMap Φ (normalized Φ anchor Γ hp C hmod hcenter) :=
  (subdivisionMap Φ anchor (Φ.faceSelector anchor Γ) hp).comp
    ((Rechart.subdivisionMap (decomposition Φ anchor (Φ.faceSelector anchor Γ) hp)
      C hp hmod hcenter).comp
      ((minimalized Φ anchor Γ hp C hmod hcenter).reducedSubdivisionMap hp))

/--
@isnad1 id=eq.5h7v.s11.3b7c57f05bdf from=translated src=- shape=33e8739e vocab=64c176c4
-/
@[simp]
theorem normalizedTargetNode_projection (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).node
      (normalizedTargetNode Φ anchor Γ hp C hmod hcenter hΓ hred) = anchor := rfl

/-- The realized target face is exactly the pullback of the selected old
face through the normalized subdivision, including its polytope constraint.
@isnad1 id=eq.5h7v.s12.74a061f19976 from=translated src=- shape=1b9f7408 vocab=76562f91
-/
theorem normalizedTargetFace_carrier (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor) :
    (normalizedTargetFace Φ anchor Γ hp C hmod hcenter hΓ hred).carrier =
      ((normalized Φ anchor Γ hp C hmod hcenter).flag.polytope
        (normalizedTargetNode Φ anchor Γ hp C hmod hcenter hΓ hred)).carrier ∩
      (normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).fibre
        (normalizedTargetNode Φ anchor Γ hp C hmod hcenter hΓ hred) ⁻¹' Γ.carrier := rfl

/--
@isnad1 id=isrealiz.5h9v.s12.562b6f99bfc0 from=translated src=- shape=d1b8c041 vocab=f2cb83a9
-/
theorem normalized_isRealizedFace
    (x : (normalized Φ anchor Γ hp C hmod hcenter).flag.Node)
    (Δ : (Φ.flag.polytope ((normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).node x)).Face)
    (hne : (((normalized Φ anchor Γ hp C hmod hcenter).flag.polytope x).carrier ∩
      (normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).fibre x ⁻¹' Δ.carrier).Nonempty)
    (hΔ : Φ.IsRealizedFace ((normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).node x) Δ) :
    (normalized Φ anchor Γ hp C hmod hcenter).IsRealizedFace x
      ((normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).face x Δ hne) :=
  (normalizedSubdivisionMap Φ anchor Γ hp C hmod hcenter).isRealizedFace x Δ hne hΔ

end EGZ.FlagDecomposition.FaceRefinement

namespace EGZ

open FlagDecomposition

/-- Uniform normalization of a proper-face refinement at a reduced node.
The new radius depends only on the original radius and ambient dimension.
@isnad1 id=ex.0h1v.s12.7a76bcf9f8f2 from=translated src=- shape=ad4bbf2a vocab=6ed12b74
-/
theorem normalized_face_refinement_lemma (d : ℕ) :
    ∃ A : ℕ → ℕ, Monotone A ∧ (∀ K, K ≤ A K) ∧
      ∀ K : ℕ, ∃ p₀ : ℕ, 2 ≤ p₀ ∧
        ∀ (p : ℕ) [NeZero p] [Fact p.Prime], p₀ < p →
          ∀ (f : FpCoord p d → ℕ) (Φ : FlagDecomposition p d f)
            (anchor : Φ.flag.Node) (Γ : (Φ.flag.polytope anchor).Face)
            (hΓ : Γ ≠ ⊤) (hred : Φ.IsReducedElement anchor),
            Φ.IsKBounded (fun _ ↦ K) →
            ∃ (hp : Odd p)
              (C : ∀ x, IntegerLatticeChart
                ((FaceRefinement.decomposition Φ anchor (Φ.faceSelector anchor Γ) hp).liftedSupport x))
              (hmod : ∀ x, Function.Injective ((Rechart.chart
                (FaceRefinement.decomposition Φ anchor (Φ.faceSelector anchor Γ) hp) C x).modp p))
              (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q),
              let Ψ := FaceRefinement.normalized Φ anchor Γ hp C hmod hcenter
              Ψ.IsMinimal ∧ Ψ.IsReduced ∧ Ψ.IsKBounded (fun _ ↦ A K) ∧
              Ψ.retainedMass = Φ.retainedMass ∧
              @Fintype.card Ψ.flag.Node Ψ.flag.nodeFintype ≤ 2 * Fintype.card Φ.flag.Node ∧
              Ψ.IsRealizedFace
                (FaceRefinement.normalizedTargetNode Φ anchor Γ hp C hmod hcenter hΓ hred)
                (FaceRefinement.normalizedTargetFace Φ anchor Γ hp C hmod hcenter hΓ hred) := by
  obtain ⟨A, hAmono, hAge, hA⟩ := exists_uniform_rechart_parameters d
  refine ⟨A, hAmono, hAge, ?_⟩
  intro K
  obtain ⟨p₀, hp₀, hparams⟩ := hA K
  refine ⟨p₀, hp₀, ?_⟩
  intro p _ _ hpp f Φ anchor Γ hΓ hred hΦ
  have hp : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  let Θ := FaceRefinement.decomposition Φ anchor (Φ.faceSelector anchor Γ) hp
  have hΘ : Θ.IsKBounded (fun _ ↦ K) :=
    FaceRefinement.isKBounded Φ anchor (Φ.faceSelector anchor Γ) hp hΦ
  obtain ⟨C, hmod, hcenter, hbox, _hpoly⟩ :=
    hparams p hpp f Θ (fun _ ↦ K) hΘ (fun _ ↦ le_rfl)
  exact ⟨hp, C, hmod, hcenter,
    FaceRefinement.normalized_isMinimal Φ anchor Γ hp C hmod hcenter,
    FaceRefinement.normalized_isReduced Φ anchor Γ hp C hmod hcenter,
    FaceRefinement.normalized_isKBounded Φ anchor Γ hp C hmod hcenter hΦ hbox,
    FaceRefinement.normalized_retainedMass Φ anchor Γ hp C hmod hcenter,
    FaceRefinement.normalized_card_le Φ anchor Γ hp C hmod hcenter,
    FaceRefinement.normalizedTargetFace_isRealized Φ anchor Γ hp C hmod hcenter hΓ hred⟩

end EGZ
