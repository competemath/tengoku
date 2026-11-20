import Tengoku.QuartetDistanceBandeltDress.QuartetDistance.Circular

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The three quartet topologies

This file records explicitly that a four-element set has exactly three `2+2` splits.  The
paper uses this fact twice: crossing orders and quartet topologies are identified, and the
two wrong-channel supports of distinct true topologies have a one-element intersection.
-/

namespace QuartetDistance
namespace Splits

open Circular

/-- The three perfect matchings of the four standard positions.-/
def canonicalSplits : Finset (QuartetSplit Four) :=
  {splitOf 0 2 1 3, splitOf 0 1 2 3, splitOf 0 1 3 2}

/--
@isnad1 id=eq.0h0v.s3.bdcbf086fd51 from=translated src=- shape=6afa1142 vocab=627efd7e
-/
theorem card_canonicalSplits : canonicalSplits.card = 3 := by decide

/--
@isnad1 id=mem.0h0v.s4.36e3e0fa036c from=translated src=- shape=80a7a8bb vocab=054bcce0
-/
theorem canonicalCrossing_mem : canonicalCrossing ∈ canonicalSplits := by decide

/-- Relabelling is an embedding on quartet splits.-/
def mapSplitEmbedding [DecidableEq X] (q : Four ↪ X) :
    QuartetSplit Four ↪ QuartetSplit X where
  toFun := mapSplit q
  inj' := mapSplit_injective q

/-- The three quartet topologies on the range of `q`.-/
def allSplits [DecidableEq X] (q : Four ↪ X) : Finset (QuartetSplit X) :=
  canonicalSplits.map (mapSplitEmbedding q)

/--
@isnad1 id=eq.0h2v.s4.f002485f8aff from=translated src=- shape=8e95fe61 vocab=38b064ac
-/
@[simp] theorem card_allSplits [DecidableEq X] (q : Four ↪ X) :
    (allSplits q).card = 3 := by
  simp [allSplits, card_canonicalSplits]

/--
@isnad1 id=mem.0h2v.s5.25757bbffd7f from=translated src=- shape=8f184c87 vocab=64307c9c
-/
@[simp] theorem crossing_mem_allSplits [DecidableEq X] (q : Four ↪ X) :
    crossing q ∈ allSplits q := by
  simp [crossing, allSplits, mapSplitEmbedding, canonicalCrossing_mem]

/-- Reordering four fixed labels always selects one of their three splits.
@isnad1 id=mem.0h3v.s5.f53430b220e4 from=translated src=- shape=0527ca58 vocab=3d2dd538
-/
theorem crossing_reindex_mem_allSplits [DecidableEq X] (q : Four ↪ X) (σ : Perm4) :
    crossing (σ.toEmbedding.trans q) ∈ allSplits q := by
  have hfinite : mapSplit σ.toEmbedding canonicalCrossing ∈ canonicalSplits := by
    revert σ
    decide
  rw [crossing_comp]
  exact Finset.mem_map.mpr ⟨_, hfinite, rfl⟩

/-- The complement of one topology in the three-element topology set has size two.
@isnad1 id=eq.2h3v.s5.668daa62219e from=translated src=- shape=926f3a83 vocab=9414761d
-/
theorem card_erase_topology [DecidableEq α] {U : Finset α} {s : α}
    (hU : U.card = 3) (hs : s ∈ U) :
    (U.erase s).card = 2 := by
  rw [Finset.card_erase_of_mem hs, hU]

/-- Distinct true topologies have exactly one common wrong topology.
@isnad1 id=eq.4h4v.s6.ae3b1ff1dffc from=translated src=- shape=eb4c5164 vocab=1a6d48b3
-/
theorem card_common_wrong [DecidableEq α] {U : Finset α} {s t : α}
    (hU : U.card = 3) (hs : s ∈ U) (ht : t ∈ U) (hst : s ≠ t) :
    ((U.erase s) ∩ (U.erase t)).card = 1 := by
  have hinter : (U.erase s) ∩ (U.erase t) = (U.erase s).erase t := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hxs, hxU⟩, hxt, _⟩
      exact ⟨hxt, hxs, hxU⟩
    · rintro ⟨hxt, hxs, hxU⟩
      exact ⟨⟨hxs, hxU⟩, hxt, hxU⟩
  rw [hinter, Finset.card_erase_of_mem]
  · rw [card_erase_topology hU hs]
  · simp [ht, Ne.symm hst]

/-- The two wrong supports coincide when the true topology coincides.
@isnad1 id=eq.0h3v.s5.a41bda1bfd00 from=translated src=- shape=15e4dff2 vocab=27d1da82
-/
theorem common_wrong_self [DecidableEq α] {U : Finset α} {s : α} :
    (U.erase s) ∩ (U.erase s) = U.erase s := by simp

end Splits
end QuartetDistance
