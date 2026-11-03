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

/--
@isnad1 id=transpor.1h3v.s4.6894a6166580 from=translated src=- shape=884da206 vocab=ef24cce5
-/
theorem transports_toOldAut (g : Aut) (X Y : Triple)
    (h : Transports g X Y) :
    AlbertLean.Transports (toOldAut g) (oldTriple X) (oldTriple Y) := by
  refine ⟨h 0, h 1, h 2⟩

/--
@isnad1 id=eq.1h3v.s4.6ea7ff3ffdc8 from=translated src=- shape=7dc06ae2 vocab=c1ef88d6
-/
theorem detector_invariant (g : Aut) (X Y : Triple)
    (h : Transports g X Y) : detector Y = detector X := by
  rw [detector_eq, detector_eq]
  exact AlbertLean.traceCubeDetector_invariant
    (toOldAut g) (oldTriple X) (oldTriple Y) (transports_toOldAut g X Y h)

/--
@isnad1 id=not.0h0v.s3.f31c3ecc9c9e from=translated src=- shape=94301928 vocab=f91ac717
-/
theorem no_compact_transporter : ¬ ∃ g : Aut, Transports g first second := by
  rintro ⟨g, hg⟩
  apply AlbertLean.solution.noUnitalProductAutomorphismTransports
  refine ⟨toOldAut g, ?_⟩
  rw [← oldTriple_first, ← oldTriple_second]
  exact transports_toOldAut g first second hg

end CompactOneBit
