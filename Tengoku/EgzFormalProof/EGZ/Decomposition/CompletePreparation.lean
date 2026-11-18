import Tengoku.EgzFormalProof.EGZ.Decomposition.LocalizedPruning
import Tengoku.EgzFormalProof.EGZ.Decomposition.LowerTransfer
import Tengoku.EgzFormalProof.EGZ.Decomposition.AugmentedCompleteness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Preparing a complete-element refinement

Choose the maximal thin directions, prune only below the selected anchor,
and transfer its surviving local mass to a lower layer. This produces an
actual flag decomposition, with controlled mass loss and a non-reduced old
upper anchor, before adjoining the new slab coordinates.
-/

open scoped BigOperators

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}

structure CompletePreparation (Φ : FlagDecomposition p d f) (anchor : Φ.flag.Node)
    (t : ℕ → ℕ) (δ : ℝ) where
  count : ℕ
  count_le : count ≤ d
  chain : DirectionChain (Φ.representation.fiberConstantSubmodule anchor)
    (fun i ξ ↦ IsThinAlong (Φ.cumulativeWeight anchor) ξ (t (i + 1))
      ((3 : ℝ) ^ (i + 1) * δ)) count
  maximal : ∀ ξ, ξ ∉ chain.space count →
    IsThickAlong (Φ.cumulativeWeight anchor) ξ (t (count + 1)) ((3 : ℝ) ^ (count + 1) * δ)

/--
@isnad1 id=nonempty.0h7v.s5.6bb041a2de6b from=translated src=- shape=49e80c96 vocab=1663f000
-/
theorem nonempty_completePreparation (Φ : FlagDecomposition p d f)
    (anchor : Φ.flag.Node) (t : ℕ → ℕ) (δ : ℝ) :
    Nonempty (CompletePreparation Φ anchor t δ) := by
  obtain ⟨k, hk, D, hmax⟩ := exists_maximal_thinDirections Φ.representation anchor
    (Φ.cumulativeWeight anchor) t δ
  exact ⟨⟨k, hk, D, hmax⟩⟩

namespace CompletePreparation

variable {Φ : FlagDecomposition p d f} {anchor : Φ.flag.Node} {t : ℕ → ℕ} {δ : ℝ}
    (D : CompletePreparation Φ anchor t δ)

def selectedSet : Set (FpCoord p d) := slabIntersection D.count D.chain.direction t

/--
@isnad1 id=ex.3h8v.s7.23a137c300f9 from=translated src=- shape=c4371e59 vocab=32da5331
-/
theorem selected_nonzero (_hp : Odd p) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1) :
    ∃ v, restrictWeight (Φ.cumulativeWeight anchor) D.selectedSet v ≠ 0 := by
  apply D.chain.slabIntersection_nonzero hδ D.count_le hsmall
  obtain ⟨q, hq⟩ := Φ.liftedSupport_nonempty anchor
  obtain ⟨_, v, _, hv⟩ := (Φ.originalWeights.hat_ne_zero_iff anchor q).mp
    ((Φ.liftedSupport_spec anchor q).mp hq)
  exact ⟨v, hv⟩

variable (hp : Odd p) (hδ : 0 ≤ δ) (hsmall : (3 : ℝ) ^ (d + 1) * δ < 1)

noncomputable abbrev pruned : FlagDecomposition p d f :=
  LocalizedPruning.decomposition Φ anchor D.selectedSet (D.selected_nonzero hp hδ hsmall) hp

noncomputable abbrev prunedAnchor : (D.pruned hp hδ hsmall).flag.Node :=
  LocalizedPruning.anchorNode Φ anchor D.selectedSet (D.selected_nonzero hp hδ hsmall) hp

noncomputable abbrev split : FlagDecomposition p d f :=
  LowerTransfer.decomposition (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall) hp

noncomputable abbrev lowerAnchor : (D.split hp hδ hsmall).flag.Node :=
  LowerTransfer.lowerAnchor (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall) hp

noncomputable abbrev upperAnchor : (D.split hp hδ hsmall).flag.Node :=
  LowerTransfer.upper (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall) hp
    (D.prunedAnchor hp hδ hsmall)

/--
@isnad1 id=eq.3h8v.s7.6d996d30dd8b from=translated src=- shape=504260d1 vocab=1908bc03
-/
@[simp]
theorem lowerAnchor_cumulativeWeight :
    (D.split hp hδ hsmall).cumulativeWeight (D.lowerAnchor hp hδ hsmall) =
      restrictWeight (Φ.cumulativeWeight anchor) D.selectedSet := by
  rw [LowerTransfer.lowerAnchor_cumulativeWeight]
  exact LocalizedPruning.cumulativeWeight_anchorNode _ _ _ _ _

/--
@isnad1 id=eq.3h8v.s8.6e901bff960a from=translated src=- shape=4e183149 vocab=c64f040e
-/
theorem lowerAnchor_space :
    (D.split hp hδ hsmall).representation.space (D.lowerAnchor hp hδ hsmall) =
      Φ.representation.space anchor := rfl

/--
@isnad1 id=eq.3h8v.s9.81466820fe22 from=translated src=- shape=27633755 vocab=f01f63a9
-/
theorem lowerAnchor_map :
    (D.split hp hδ hsmall).representation.map (D.lowerAnchor hp hδ hsmall) =
      Φ.representation.map anchor := rfl

/--
@isnad1 id=not.3h8v.s7.5d903555ae09 from=translated src=- shape=31003c62 vocab=7a2afc34
-/
theorem upperAnchor_not_isReducedElement :
    ¬ (D.split hp hδ hsmall).IsReducedElement (D.upperAnchor hp hδ hsmall) :=
  LowerTransfer.upperAnchor_not_isReducedElement _ _ _

/--
@isnad1 id=eq.3h8v.s7.00598bb8ef81 from=translated src=- shape=2b7efdce vocab=2e762b90
-/
theorem retainedMass_loss :
    (Φ.retainedMass : ℝ) - (D.split hp hδ hsmall).retainedMass =
      (natMass (Φ.cumulativeWeight anchor) : ℝ) -
        natMass (restrictWeight (Φ.cumulativeWeight anchor) D.selectedSet) := by
  rw [FaceRefinement.retainedMass (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall)
    (fun _ ↦ True) hp]
  exact LocalizedPruning.decomposition_retainedMass_loss _ _ _ _ _

/--
@isnad1 id=le.3h8v.s7.ea44bcfb8256 from=translated src=- shape=376416c6 vocab=79a3e661
-/
theorem retainedMass_loss_le :
    (Φ.retainedMass : ℝ) - (D.split hp hδ hsmall).retainedMass ≤
      (3 : ℝ) ^ (d + 1) * δ * natMass (Φ.cumulativeWeight anchor) := by
  rw [D.retainedMass_loss hp hδ hsmall]
  exact D.chain.slabIntersection_loss_le_dimension hδ D.count_le

/--
@isnad1 id=le.3h8v.s7.f480d2380bec from=translated src=- shape=850fc363 vocab=91365b0c
-/
theorem card_le :
    @Fintype.card (D.split hp hδ hsmall).flag.Node
      (D.split hp hδ hsmall).flag.nodeFintype ≤ 2 * Fintype.card Φ.flag.Node := by
  apply (FaceRefinement.card_le (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall)
    (fun _ ↦ True) hp).trans
  apply Nat.mul_le_mul_left
  exact ((LocalizedPruning.prunedWeights Φ anchor D.selectedSet
    (D.selected_nonzero hp hδ hsmall)).rebuildData hp).card_decomposition_le

/-- Forget the lower-layer labels and recover a proper point of the old flag.-/
noncomputable def subdivisionMap : SubdivisionMap Φ (D.split hp hδ hsmall) :=
  ((LocalizedPruning.prunedWeights Φ anchor D.selectedSet
    (D.selected_nonzero hp hδ hsmall)).rebuiltSubdivisionMap hp).comp
      (FaceRefinement.subdivisionMap (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall)
        (fun _ ↦ True) hp)

noncomputable abbrev extra : (D.split hp hδ hsmall).flag.Node → ℕ :=
  LowerTransfer.extra (D.pruned hp hδ hsmall) (D.prunedAnchor hp hδ hsmall) hp D.count

/--
@isnad1 id=antitone.3h8v.s10.ca01d09624ac from=translated src=- shape=81d1d891 vocab=f549482d
-/
theorem extra_antitone : Antitone (D.extra hp hδ hsmall) :=
  LowerTransfer.extra_antitone _ _ _ _

/--
@isnad1 id=eq.3h8v.s7.f9817567fd66 from=translated src=- shape=1e91a6c5 vocab=af305a46
-/
@[simp]
theorem extra_lowerAnchor : D.extra hp hδ hsmall (D.lowerAnchor hp hδ hsmall) = D.count :=
  LowerTransfer.extra_lowerAnchor _ _ _ _

/--
@isnad1 id=eq.3h8v.s7.9c715ea91307 from=translated src=- shape=9013f1b0 vocab=7bc8b7f4
-/
@[simp]
theorem extra_upperAnchor : D.extra hp hδ hsmall (D.upperAnchor hp hδ hsmall) = 0 :=
  LowerTransfer.extra_upper _ _ _ _ _

end CompletePreparation

end EGZ.FlagDecomposition
