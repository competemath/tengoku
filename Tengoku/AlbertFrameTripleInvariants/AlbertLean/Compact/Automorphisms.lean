import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Compact.Dictionary
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.AutomorphismLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Transport of automorphisms through the compact dictionary -/

noncomputable section
namespace CompactOneBit

def toOldAut (g : Aut) : AlbertLean.JordanAut where
  toLinearEquiv := g.linear
  map_one := by simpa only [← unit_eq] using g.unit
  map_circle := by
    intro x y
    simpa only [← product_eq] using g.product x y

theorem transports_toOldAut (g : Aut) (X Y : Triple)
    (h : Transports g X Y) :
    AlbertLean.Transports (toOldAut g) (oldTriple X) (oldTriple Y) := by
  refine ⟨h 0, h 1, h 2⟩

theorem detector_invariant (g : Aut) (X Y : Triple)
    (h : Transports g X Y) : detector Y = detector X := by
  rw [detector_eq, detector_eq]
  exact AlbertLean.traceCubeDetector_invariant
    (toOldAut g) (oldTriple X) (oldTriple Y) (transports_toOldAut g X Y h)

theorem no_compact_transporter : ¬ ∃ g : Aut, Transports g first second := by
  rintro ⟨g, hg⟩
  apply AlbertLean.solution.noUnitalProductAutomorphismTransports
  refine ⟨toOldAut g, ?_⟩
  rw [← oldTriple_first, ← oldTriple_second]
  exact transports_toOldAut g first second hg

end CompactOneBit
