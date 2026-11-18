import Tengoku.EgzFormalProof.EGZ.Decomposition.CompleteBounds
import Tengoku.EgzFormalProof.EGZ.Decomposition.AugmentedDecomposition
import Tengoku.EgzFormalProof.EGZ.Decomposition.Thickness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The complete-element refinement

The prepared lower layer acquires the chosen slab coordinates and is put in
minimal lattice coordinates. Its anchor is complete by maximality of the
thin directions. Passing to the face index of its whole polytope supplies a
reduced complete representative with exactly the same cumulative function.
-/

namespace EGZ.FlagDecomposition.CompletePreparation

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}
    {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node} {t : ℕ → ℕ} {δ : ℝ}
    (D : CompletePreparation Φ anchor t δ)
    (hp : Odd p) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1)
    (C : ∀ x, IntegerLatticeChart ((D.diagram hp hδ hsmall).support x))
    (hmod : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

noncomputable abbrev refined : FlagDecomposition p d f :=
  Augmented.decomposition (D.split hp hδ hsmall) (D.extra hp hδ hsmall) D.chain.direction hp
    (D.extra_antitone hp hδ hsmall) C hmod hcenter

/--
@isnad1 id=isminima.5h9v.s10.2549bb2f93ac from=translated src=- shape=17745467 vocab=3372b88f
-/
theorem refined_isMinimal : (D.refined hp hδ hsmall C hmod hcenter).IsMinimal :=
  Augmented.decomposition_isMinimal _ _ _ _ _ _ _ _

/--
@isnad1 id=eq.5h10v.s10.78f3d3c6f352 from=translated src=- shape=6957f7bf vocab=b40736f0
-/
theorem refined_cumulativeWeight (x : (D.split hp hδ hsmall).flag.Node) :
    (D.refined hp hδ hsmall C hmod hcenter).cumulativeWeight x =
      (D.split hp hδ hsmall).cumulativeWeight x := rfl

/--
@isnad1 id=eq.5h9v.s10.4172344702b3 from=translated src=- shape=7e5e22a6 vocab=689c5db6
-/
theorem refined_retainedMass :
    (D.refined hp hδ hsmall C hmod hcenter).retainedMass =
      (D.split hp hδ hsmall).retainedMass := rfl

/-- The lower anchor is complete after adjoining all chosen directions.
@isnad1 id=iscomple.5h9v.s10.21a28edd545f from=translated src=- shape=88732fa5 vocab=99f43e1b
-/
theorem refined_lowerAnchor_isCompleteElement :
    (D.refined hp hδ hsmall C hmod hcenter).IsCompleteElement
      (D.lowerAnchor hp hδ hsmall) (t (D.count + 1)) δ := by
  intro η hη
  obtain ⟨v, w, hv, hw, hmap, hη⟩ := hη
  have hvold := Augmented.representation_space_le_original (D.split hp hδ hsmall)
    (D.extra hp hδ hsmall) D.chain.direction hp (D.extra_antitone hp hδ hsmall)
    C hmod (D.lowerAnchor hp hδ hsmall) hv
  have hwold := Augmented.representation_space_le_original (D.split hp hδ hsmall)
    (D.extra hp hδ hsmall) D.chain.direction hp (D.extra_antitone hp hδ hsmall)
    C hmod (D.lowerAnchor hp hδ hsmall) hw
  have haug := (Augmented.representation_map_eq_iff (D.split hp hδ hsmall)
    (D.extra hp hδ hsmall) D.chain.direction hp (D.extra_antitone hp hδ hsmall)
    C hmod (D.lowerAnchor hp hδ hsmall) v w hv hw).mp hmap
  have hold : Φ.representation.map anchor v = Φ.representation.map anchor w := by
    have hfirst := congrArg
      (Coord.first ((D.split hp hδ hsmall).flag.rank (D.lowerAnchor hp hδ hsmall))
        (D.extra hp hδ hsmall (D.lowerAnchor hp hδ hsmall))) haug
    simp only [Augmented.map, Coord.first_append] at hfirst
    change (D.split hp hδ hsmall).representation.map (D.lowerAnchor hp hδ hsmall) v =
      (D.split hp hδ hsmall).representation.map (D.lowerAnchor hp hδ hsmall) w at hfirst
    rwa [D.lowerAnchor_map hp hδ hsmall] at hfirst
  have hdir : ∀ i, i < D.count → D.chain.direction i v = D.chain.direction i w := by
    intro i hi
    have hlast := congrArg
      (Coord.last ((D.split hp hδ hsmall).flag.rank (D.lowerAnchor hp hδ hsmall))
        (D.extra hp hδ hsmall (D.lowerAnchor hp hδ hsmall))) haug
    have hindex : i < D.extra hp hδ hsmall (D.lowerAnchor hp hδ hsmall) := by
      rwa [D.extra_lowerAnchor hp hδ hsmall]
    have heq := congrFun hlast (⟨i, hindex⟩ : Fin _)
    simpa only [Augmented.map, Coord.last_append, AffineMap.pi_apply] using heq
  change IsThickAlong ((D.split hp hδ hsmall).cumulativeWeight
    (D.lowerAnchor hp hδ hsmall)) η (t (D.count + 1)) δ
  rw [D.lowerAnchor_cumulativeWeight hp hδ hsmall]
  exact D.chain.thick_slabIntersection_of_augmented_fibre Φ.representation anchor
    hδ D.maximal hvold hwold hold hdir hη

/-- A reduced node below the lower anchor with the same cumulative weight.-/
noncomputable def completeNode : (D.refined hp hδ hsmall C hmod hcenter).flag.Node :=
  (D.refined hp hδ hsmall C hmod hcenter).faceIndex (D.lowerAnchor hp hδ hsmall) ⊤

/--
@isnad1 id=le.5h9v.s11.3145c1b582c9 from=translated src=- shape=739360ad vocab=d3f8635b
-/
theorem completeNode_le_lowerAnchor :
    D.completeNode hp hδ hsmall C hmod hcenter ≤ D.lowerAnchor hp hδ hsmall :=
  (D.refined hp hδ hsmall C hmod hcenter).faceIndex_le _ _

/--
@isnad1 id=isreduce.5h9v.s10.f82b396f0f14 from=translated src=- shape=a8ed17a8 vocab=4e76f201
-/
theorem completeNode_isReduced :
    (D.refined hp hδ hsmall C hmod hcenter).IsReducedElement
      (D.completeNode hp hδ hsmall C hmod hcenter) :=
  (D.refined hp hδ hsmall C hmod hcenter).isReducedElement_faceIndex _ _

/--
@isnad1 id=eq.5h9v.s10.731ede243dad from=translated src=- shape=64384e06 vocab=519d289d
-/
theorem completeNode_cumulativeWeight :
    (D.refined hp hδ hsmall C hmod hcenter).cumulativeWeight
        (D.completeNode hp hδ hsmall C hmod hcenter) =
      restrictWeight (Φ.cumulativeWeight anchor) D.selectedSet := by
  rw [completeNode,
    (D.refined hp hδ hsmall C hmod hcenter).cumulativeWeight_faceIndex_top hp]
  exact D.lowerAnchor_cumulativeWeight hp hδ hsmall

/--
@isnad1 id=iscomple.5h9v.s10.089236179283 from=translated src=- shape=883d68d0 vocab=321f3bcb
-/
theorem completeNode_isCompleteElement :
    (D.refined hp hδ hsmall C hmod hcenter).IsCompleteElement
      (D.completeNode hp hδ hsmall C hmod hcenter) (t (D.count + 1)) δ :=
  (D.refined hp hδ hsmall C hmod hcenter).isCompleteElement_faceIndex_top hp
    (D.refined_isMinimal hp hδ hsmall C hmod hcenter) _
    (D.refined_lowerAnchor_isCompleteElement hp hδ hsmall C hmod hcenter)

/--
@isnad1 id=not.5h9v.s10.a047e8cb8051 from=translated src=- shape=3a627271 vocab=0e87dc1f
-/
theorem refined_upperAnchor_not_isReducedElement :
    ¬ (D.refined hp hδ hsmall C hmod hcenter).IsReducedElement (D.upperAnchor hp hδ hsmall) := by
  rw [Augmented.decomposition_isReducedElement_iff]
  exact D.upperAnchor_not_isReducedElement hp hδ hsmall

/--
@isnad1 id=le.5h9v.s10.9dbbf7914314 from=translated src=- shape=27c4a837 vocab=18d3275b
-/
theorem refined_retainedMass_loss_le :
    (Φ.retainedMass : ℝ) - (D.refined hp hδ hsmall C hmod hcenter).retainedMass ≤
      (3 : ℝ) ^ (d + 1) * δ * natMass (Φ.cumulativeWeight anchor) :=
  D.retainedMass_loss_le hp hδ hsmall

/--
@isnad1 id=le.5h9v.s10.df84b363aa36 from=translated src=- shape=18a739dc vocab=5575fbba
-/
theorem refined_card_le :
    @Fintype.card (D.refined hp hδ hsmall C hmod hcenter).flag.Node
      (D.refined hp hδ hsmall C hmod hcenter).flag.nodeFintype ≤
        2 * Fintype.card Φ.flag.Node := D.card_le hp hδ hsmall

/--
@isnad1 id=iskbound.6h10v.s10.555abe761b0b from=translated src=- shape=212d013b vocab=cf9b8911
-/
theorem refined_isKBounded {B : ℕ}
    (hB : ∀ x (q : IntCoord (C x).rank),
      q.real ∈ (((D.diagram hp hδ hsmall).chartedFlag C).polytope x).carrier →
        latticeSupNorm q ≤ B) :
    (D.refined hp hδ hsmall C hmod hcenter).IsKBounded (fun _ ↦ B) := hB

noncomputable def refinedSubdivisionMap :
    SubdivisionMap Φ (D.refined hp hδ hsmall C hmod hcenter) :=
  (D.subdivisionMap hp hδ hsmall).comp
    (Augmented.subdivisionMap (D.split hp hδ hsmall) (D.extra hp hδ hsmall) D.chain.direction
      hp (D.extra_antitone hp hδ hsmall) C hmod hcenter)

include hδ in
/-- An incomplete anchor forces the construction to add at least one new
direction whenever the first chosen width dominates its requested width.
@isnad1 id=lt.3h9v.s6.7919d928406e from=translated src=- shape=d2b9b959 vocab=0a08528f
-/
theorem count_pos_of_not_complete (T : ℕ) (hwidth : T ≤ t 1)
    (hnot : ¬ Φ.IsCompleteElement anchor T δ) : 0 < D.count := by
  apply D.chain.length_pos_of_exists D.maximal
  simp only [IsCompleteElement, IsThickAlong, not_forall, not_not] at hnot
  obtain ⟨η, hη, hthin⟩ := hnot
  refine ⟨η, ?_, ?_⟩
  · intro hmem
    exact ((Φ.representation.mem_fiberConstantSubmodule_iff anchor η).mp hmem) hη
  · exact (hthin.mono_width hwidth).mono_error (by norm_num; linarith)

end EGZ.FlagDecomposition.CompletePreparation
