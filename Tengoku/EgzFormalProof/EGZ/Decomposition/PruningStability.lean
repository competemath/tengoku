import Tengoku.EgzFormalProof.EGZ.Decomposition.Completeness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Completeness after pruning local weights

The cumulative atoms at a node form a subset of all local atoms.  Hence
their mass loss is at most the global retained mass loss.  This connects the
gap-pruning estimate to the thickness estimate at every old large node.
-/

open scoped BigOperators

namespace EGZ

namespace FlagDecompositionRaw

variable {p d : ℕ} [NeZero p] {F : ConvexFlag}

/-- Cumulative mass is the mass of the local atoms based below the node.
@isnad1 id=eq.0h5v.s7.a8bdee8325ec from=translated src=- shape=072c444c vocab=0c738dc8
-/
theorem natMass_cumulativeWeight (pieces : F.Node → FpCoord p d → ℕ)
    (x : F.Node) :
    natMass (cumulativeWeight pieces x) =
      natMassOn (fun a : F.Node × FpCoord p d ↦ pieces a.1 a.2)
        {a | a.1 ≤ x} := by
  classical
  unfold natMass cumulativeWeight natMassOn
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- Loss from a cumulative weight is bounded by loss from all local atoms.
@isnad1 id=le.1h6v.s7.f5a2c0831093 from=translated src=- shape=ea78fe8f vocab=efe0a7b4
-/
theorem cumulativeWeight_mass_loss_le
    {pieces pieces' : F.Node → FpCoord p d → ℕ}
    (hle : ∀ x v, pieces' x v ≤ pieces x v) (x : F.Node) :
    natMass (cumulativeWeight pieces x) - natMass (cumulativeWeight pieces' x) ≤
      natMass (retainedWeight pieces) - natMass (retainedWeight pieces') := by
  rw [natMass_cumulativeWeight, natMass_cumulativeWeight,
    natMass_retainedWeight, natMass_retainedWeight]
  exact natMassOn_loss_le (fun a : F.Node × FpCoord p d ↦ hle a.1 a.2)
    {a | a.1 ≤ x}

/-- Real-valued form of the cumulative mass-loss bound, ready for relative
loss estimates.
@isnad1 id=le.1h6v.s7.e12191fc2329 from=translated src=- shape=93a9e39c vocab=d9cecf42
-/
theorem cumulativeWeight_mass_loss_le_real
    {pieces pieces' : F.Node → FpCoord p d → ℕ}
    (hle : ∀ x v, pieces' x v ≤ pieces x v) (x : F.Node) :
    (natMass (cumulativeWeight pieces x) : ℝ) - natMass (cumulativeWeight pieces' x) ≤
      (natMass (retainedWeight pieces) : ℝ) - natMass (retainedWeight pieces') := by
  rw [natMass_cumulativeWeight, natMass_cumulativeWeight,
    natMass_retainedWeight, natMass_retainedWeight]
  exact natMassOn_loss_le_real (fun a : F.Node × FpCoord p d ↦ hle a.1 a.2)
    {a | a.1 ≤ x}

end FlagDecompositionRaw

namespace FlagDecomposition

variable {p d : ℕ} [NeZero p] {f : FpCoord p d → ℕ}

/-- Pruning at most `α` of the original retained mass preserves thickness
at an old `ε`-large node, with deterioration at most `α / ε`.
@isnad1 id=isthicka.8h11v.s8.26e60946561d from=translated src=- shape=90dd54d8 vocab=cea271b6
-/
theorem cumulativeWeight_thick_of_pruning (Φ : FlagDecomposition p d f)
    (hp : Odd p) {pieces : Φ.flag.Node → FpCoord p d → ℕ}
    {x : Φ.flag.Node} {t : ℕ} {δ α ε : ℝ}
    {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p}
    (hthick : IsThickAlong (Φ.cumulativeWeight x) ξ t δ)
    (hle : ∀ y v, pieces y v ≤ Φ.localWeight y v)
    (hε : 0 < ε) (hα : 0 ≤ α) (hlarge : Φ.IsLargeElement ε x)
    (hloss : (Φ.retainedMass : ℝ) -
      natMass (FlagDecompositionRaw.retainedWeight pieces) ≤ α * Φ.retainedMass)
    (hδ : 0 ≤ δ - α / ε) :
    IsThickAlong (FlagDecompositionRaw.cumulativeWeight pieces x) ξ t (δ - α / ε) := by
  apply hthick.of_pruning
    (fun v ↦ FlagDecompositionRaw.cumulativeWeight_mono hle x v) hε hα
    ((Φ.isLargeElement_iff_natMass hp ε x).mp hlarge)
  · exact (FlagDecompositionRaw.cumulativeWeight_mass_loss_le_real hle x).trans hloss
  · exact hδ

/-- Every functional required for completeness remains thick after the
same global pruning, before the surviving flag is repackaged.
@isnad1 id=isthicka.9h11v.s8.fb795560a98f from=translated src=- shape=c1d1caac vocab=bc9cf315
-/
theorem IsCompleteElement.thick_of_pruning {Φ : FlagDecomposition p d f}
    {x : Φ.flag.Node} {t : ℕ} {δ α ε : ℝ}
    (hcomplete : Φ.IsCompleteElement x t δ) (hp : Odd p)
    {pieces : Φ.flag.Node → FpCoord p d → ℕ}
    (hle : ∀ y v, pieces y v ≤ Φ.localWeight y v)
    (hε : 0 < ε) (hα : 0 ≤ α) (hlarge : Φ.IsLargeElement ε x)
    (hloss : (Φ.retainedMass : ℝ) -
      natMass (FlagDecompositionRaw.retainedWeight pieces) ≤ α * Φ.retainedMass)
    (hδ : 0 ≤ δ - α / ε)
    (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p)
    (hξ : Φ.representation.NonconstantOnFibers x ξ) :
    IsThickAlong (FlagDecompositionRaw.cumulativeWeight pieces x) ξ t (δ - α / ε) :=
  Φ.cumulativeWeight_thick_of_pruning hp (hcomplete ξ hξ) hle hε hα hlarge hloss hδ

end FlagDecomposition

end EGZ
