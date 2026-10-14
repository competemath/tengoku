/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsRootDecisionData0
public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsRootDecisionData1
public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsRootDecisionData2
public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsRootDecisionData3

/-!
# Complete normalized root dispatch

The 1,023-node trie has 432 leaves, one for each proper normalized coloring of
the 13-vertex 2-Golomb root. Every leaf names a separately checked Parts tree.
-/

@[expose] public section

namespace HadwigerNelsonBounds

/-- All chunks of the complete normalized root-decision trie. -/
def partsRootDecisionNodes : Array (Array PartsRootNode) := #[
  partsRootDecisionChunk0,
  partsRootDecisionChunk1,
  partsRootDecisionChunk2,
  partsRootDecisionChunk3,
  partsRootDecisionChunk4,
  partsRootDecisionChunk5,
  partsRootDecisionChunk6,
  partsRootDecisionChunk7,
  partsRootDecisionChunk8,
  partsRootDecisionChunk9,
  partsRootDecisionChunk10,
  partsRootDecisionChunk11,
  partsRootDecisionChunk12,
  partsRootDecisionChunk13,
  partsRootDecisionChunk14,
  partsRootDecisionChunk15,
]

/--
@isnad1 id=eq.0h0v.s4.23a196ba1b61 from=translated src=- shape=63965382 vocab=9bc36e76
-/
theorem partsRootDecision_verifies :
    PartsRootVerifiesNodeB partsRootDecisionNodes 1024
      partsNormalizedRootPath 0 = true := by
  decide +kernel

/-- No proper coloring of the Parts graph extends the normalized fixed root.
@isnad1 id=false.2h1v.s4.9848aa17321c from=translated src=- shape=775d695d vocab=9471ac6e
-/
theorem no_parts_coloring_of_normalized_root {coloring : Fin 481 → Fin 4}
    (hproper : PartsProper coloring)
    (hroots : PartsExtends coloring partsNormalizedRootPath) : False := by
  exact partsRootDecision_not_colorable partsRootDecisionNodes 1023
    partsRootDecision_verifies hproper hroots

end HadwigerNelsonBounds
