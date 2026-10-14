/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoveragePairRowIndexMasks
public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageSearchRowChoiceSoundness
public import Tengoku

/-! # Soundness of the transposed legal-row pair masks -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence

/-- The transposed pair table records exactly which row choices contain each pair bit.
@isnad1 id=eq.0h3v.s6.a2061525d278 from=translated src=- shape=1b39666d vocab=2e273ae4
-/
theorem pairRowIndexMasks_bit
    (centre : Vertex) (pairIndex : Fin 64) (rowIndex : Fin 35) :
    bitSetB ((pairRowIndexMasks.getD centre.val #[]).getD pairIndex.val 0)
        rowIndex.val =
      bitSetB (searchRowChoiceAt centre rowIndex).pairMask pairIndex.val := by
  revert centre pairIndex rowIndex
  decide +kernel

end Erdos97Octagon.RawIncidence
