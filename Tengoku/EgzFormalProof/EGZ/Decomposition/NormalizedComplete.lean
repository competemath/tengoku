import Tengoku.EgzFormalProof.EGZ.Decomposition.UniformCompleteRefinement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reduced complete-element refinements

Restricting the constructed complete-element refinement to its reduced nodes
retains the explicit complete representative and removes the old upper
anchor. Minimality, all mass bounds, and the subdivision map survive.
-/

namespace EGZ.FlagDecomposition.CompletePreparation

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}
    {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node} {t : ℕ → ℕ} {δ : ℝ}
    (D : CompletePreparation Φ anchor t δ)
    (hp : Odd p) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1)
    (C : ∀ x, IntegerLatticeChart ((D.diagram hp hδ hsmall).support x))
    (hmod : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

noncomputable abbrev normalized : FlagDecomposition p d f :=
  (D.refined hp hδ hsmall C hmod hcenter).reduced hp

noncomputable abbrev normalizedCompleteNode :
    (D.normalized hp hδ hsmall C hmod hcenter).flag.Node :=
  ⟨D.completeNode hp hδ hsmall C hmod hcenter,
    D.completeNode_isReduced hp hδ hsmall C hmod hcenter⟩

/--
@isnad1 id=isminima.5h9v.s10.cb0c0820bf02 from=translated src=- shape=17745467 vocab=a978f6f9
-/
theorem normalized_isMinimal : (D.normalized hp hδ hsmall C hmod hcenter).IsMinimal :=
  (D.refined hp hδ hsmall C hmod hcenter).reduced_isMinimal hp
    (D.refined_isMinimal hp hδ hsmall C hmod hcenter)

/--
@isnad1 id=isreduce.5h9v.s10.5d9fbb8c2984 from=translated src=- shape=17745467 vocab=dd3278d3
-/
theorem normalized_isReduced : (D.normalized hp hδ hsmall C hmod hcenter).IsReduced :=
  (D.refined hp hδ hsmall C hmod hcenter).reduced_isReduced hp

/--
@isnad1 id=eq.5h9v.s10.97217d2056ca from=translated src=- shape=fe67163a vocab=b3ce9db4
-/
@[simp]
theorem normalized_retainedMass :
    (D.normalized hp hδ hsmall C hmod hcenter).retainedMass =
      (D.refined hp hδ hsmall C hmod hcenter).retainedMass :=
  (D.refined hp hδ hsmall C hmod hcenter).reduced_retainedMass hp

/--
@isnad1 id=le.5h9v.s10.38bf344c0d86 from=translated src=- shape=27c4a837 vocab=4e08b1d0
-/
theorem normalized_retainedMass_loss_le :
    (Φ.retainedMass : ℝ) - (D.normalized hp hδ hsmall C hmod hcenter).retainedMass ≤
      (3 : ℝ) ^ (d + 1) * δ * natMass (Φ.cumulativeWeight anchor) := by
  rw [D.normalized_retainedMass]
  exact D.refined_retainedMass_loss_le hp hδ hsmall C hmod hcenter

/--
@isnad1 id=le.5h9v.s10.47786cf40c1b from=translated src=- shape=18a739dc vocab=2a7e00db
-/
theorem normalized_card_le :
    @Fintype.card (D.normalized hp hδ hsmall C hmod hcenter).flag.Node
      (D.normalized hp hδ hsmall C hmod hcenter).flag.nodeFintype ≤
        2 * Fintype.card Φ.flag.Node :=
  ((D.refined hp hδ hsmall C hmod hcenter).card_reduced_le hp).trans
    (D.refined_card_le hp hδ hsmall C hmod hcenter)

/--
@isnad1 id=iskbound.6h10v.s10.201e43353b33 from=translated src=- shape=da1f272e vocab=b1a0ed0b
-/
theorem normalized_isKBounded {B : ℕ}
    (hB : (D.refined hp hδ hsmall C hmod hcenter).IsKBounded (fun _ ↦ B)) :
    (D.normalized hp hδ hsmall C hmod hcenter).IsKBounded (fun _ ↦ B) :=
  (D.refined hp hδ hsmall C hmod hcenter).reduced_isKBounded hp hB

/--
@isnad1 id=iscomple.5h9v.s10.ce72ebf77c57 from=translated src=- shape=883d68d0 vocab=d7a32eed
-/
theorem normalizedCompleteNode_isCompleteElement :
    (D.normalized hp hδ hsmall C hmod hcenter).IsCompleteElement
      (D.normalizedCompleteNode hp hδ hsmall C hmod hcenter) (t (D.count + 1)) δ :=
  ((D.refined hp hδ hsmall C hmod hcenter).reduced_isCompleteElement_iff hp _ _ _).mpr
    (D.completeNode_isCompleteElement hp hδ hsmall C hmod hcenter)

/--
@isnad1 id=eq.5h9v.s10.be579fcde4ee from=translated src=- shape=64384e06 vocab=c552acde
-/
theorem normalizedCompleteNode_cumulativeWeight :
    (D.normalized hp hδ hsmall C hmod hcenter).cumulativeWeight
      (D.normalizedCompleteNode hp hδ hsmall C hmod hcenter) =
        restrictWeight (Φ.cumulativeWeight anchor) D.selectedSet := by
  rw [(D.refined hp hδ hsmall C hmod hcenter).reduced_cumulativeWeight]
  exact D.completeNode_cumulativeWeight hp hδ hsmall C hmod hcenter

/-- The old upper anchor is absent from the normalized node subtype.
@isnad1 id=ne.5h10v.s10.98832d5ad7c3 from=translated src=- shape=591dd8ac vocab=c2d65fab
-/
theorem normalized_node_ne_upperAnchor
    (x : (D.normalized hp hδ hsmall C hmod hcenter).flag.Node) :
    x.val ≠ D.upperAnchor hp hδ hsmall := by
  intro heq
  exact D.refined_upperAnchor_not_isReducedElement hp hδ hsmall C hmod hcenter
    (heq ▸ x.property)

noncomputable def normalizedSubdivisionMap :
    SubdivisionMap Φ (D.normalized hp hδ hsmall C hmod hcenter) :=
  (D.refinedSubdivisionMap hp hδ hsmall C hmod hcenter).comp
    ((D.refined hp hδ hsmall C hmod hcenter).reducedSubdivisionMap hp)

/--
@isnad1 id=isrealiz.7h11v.s13.c40d084eeb3e from=translated src=- shape=ad69a246 vocab=2ec5ab1d
-/
theorem normalized_isRealizedFace
    (x : (D.normalized hp hδ hsmall C hmod hcenter).flag.Node)
    (Γ : (Φ.flag.polytope ((D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).node x)).Face)
    (hne : (((D.normalized hp hδ hsmall C hmod hcenter).flag.polytope x).carrier ∩
      (D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).fibre x ⁻¹' Γ.carrier).Nonempty)
    (hΓ : Φ.IsRealizedFace
      ((D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).node x) Γ) :
    (D.normalized hp hδ hsmall C hmod hcenter).IsRealizedFace x
      ((D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).face x Γ hne) :=
  (D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter).isRealizedFace x Γ hne hΓ

end EGZ.FlagDecomposition.CompletePreparation

namespace EGZ

open FlagDecomposition

/-- The uniform complete-element operation with its output already
restricted to reduced nodes. The old upper anchor has no surviving copy.
@isnad1 id=ex.1h2v.s13.f6a15a1a1372 from=translated src=- shape=47c08113 vocab=a717e760
-/
theorem normalized_complete_refinement_lemma (d : ℕ) (g : ℕ → ℕ) (hg : Monotone g) :
    ∃ B : ℕ → ℕ, Monotone B ∧ (∀ K, K ≤ B K) ∧
      ∀ K : ℕ, ∃ p₀ : ℕ, 2 ≤ p₀ ∧
        ∀ (p : ℕ) [NeZero p] [Fact p.Prime], p₀ < p →
          ∀ (f : FpCoord p d → ℕ) (Φ : FlagDecomposition p d f)
            (anchor : Φ.flag.Node) (δ : ℝ) (hδ : 0 ≤ δ)
            (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1),
            Φ.IsKBounded (fun _ ↦ K) →
            ∃ (hp : Odd p) (t : ℕ → ℕ) (D : CompletePreparation Φ anchor t δ)
              (C : ∀ x, IntegerLatticeChart ((D.diagram hp hδ hsmall).support x))
              (hmod : ∀ x, Function.Injective
                ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))
              (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)
              (b : ℕ),
              let Ψ := D.normalized hp hδ hsmall C hmod hcenter
              let S := D.normalizedSubdivisionMap hp hδ hsmall C hmod hcenter
              K ≤ b ∧ b ≤ B K ∧ Monotone t ∧ t 0 = K ∧ g b ≤ t (D.count + 1) ∧
              Ψ.IsMinimal ∧ Ψ.IsReduced ∧ Ψ.IsKBounded (fun _ ↦ b) ∧
              (Φ.retainedMass : ℝ) - Ψ.retainedMass ≤
                (3 : ℝ) ^ (d + 1) * δ * natMass (Φ.cumulativeWeight anchor) ∧
              @Fintype.card Ψ.flag.Node Ψ.flag.nodeFintype ≤
                2 * Fintype.card Φ.flag.Node ∧
              Ψ.IsCompleteElement (D.normalizedCompleteNode hp hδ hsmall C hmod hcenter) (g b) δ ∧
              Ψ.cumulativeWeight (D.normalizedCompleteNode hp hδ hsmall C hmod hcenter) =
                restrictWeight (Φ.cumulativeWeight anchor) D.selectedSet ∧
              (∀ x : Ψ.flag.Node, x.val ≠ D.upperAnchor hp hδ hsmall) ∧
              (∀ (x : Ψ.flag.Node) (Γ : (Φ.flag.polytope (S.node x)).Face)
                (hne : ((Ψ.flag.polytope x).carrier ∩ S.fibre x ⁻¹' Γ.carrier).Nonempty),
                Φ.IsRealizedFace (S.node x) Γ → Ψ.IsRealizedFace x (S.face x Γ hne)) := by
  obtain ⟨B, hBmono, hBge, hB⟩ := complete_refinement_lemma d g hg
  refine ⟨B, hBmono, hBge, ?_⟩
  intro K
  obtain ⟨p₀, hp₀, hparams⟩ := hB K
  refine ⟨p₀, hp₀, ?_⟩
  intro p _ _ hpp f Φ anchor δ hδ hsmall hΦ
  obtain ⟨hp, t, D, C, hmod, hcenter, b, hKb, hbB, ht, ht0, hgb, _hmin, hbound, _hrest⟩ :=
    hparams p hpp f Φ anchor δ hδ hsmall hΦ
  exact ⟨hp, t, D, C, hmod, hcenter, b, hKb, hbB, ht, ht0, hgb,
    D.normalized_isMinimal hp hδ hsmall C hmod hcenter,
    D.normalized_isReduced hp hδ hsmall C hmod hcenter,
    D.normalized_isKBounded hp hδ hsmall C hmod hcenter hbound,
    D.normalized_retainedMass_loss_le hp hδ hsmall C hmod hcenter,
    D.normalized_card_le hp hδ hsmall C hmod hcenter,
    (D.normalizedCompleteNode_isCompleteElement hp hδ hsmall C hmod hcenter).mono_width hgb,
    D.normalizedCompleteNode_cumulativeWeight hp hδ hsmall C hmod hcenter,
    D.normalized_node_ne_upperAnchor hp hδ hsmall C hmod hcenter,
    D.normalized_isRealizedFace hp hδ hsmall C hmod hcenter⟩

end EGZ
