/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Tengoku.Data.Real.ENatENNReal
public import Tengoku.Topology.Instances.ENat
import Tengoku.Algebra.Order.Floor.Extended
public import Tengoku.Algebra.Order.Module.Field
public import Tengoku.Data.EReal.Operations
public import Tengoku.Topology.Algebra.InfiniteSum.Order
public import Tengoku.Topology.MetricSpace.Bounded
public import Tengoku.Topology.Order.Real

/-!
# Topology lemma for `ENat.toENNReal`

This file shows `ENat.toENNReal` is a closed embedding.
-/

public section

namespace ENat

@[continuity]
theorem continuous_toENNReal : Continuous toENNReal := by
  refine OrderTopology.continuous_iff.mpr fun a ↦ ⟨?_, ?_⟩
  · simpa using isOpen_Ioi
  · simpa using isOpen_Iio

theorem isClosedEmbedding_toENNReal : Topology.IsClosedEmbedding toENNReal :=
  continuous_toENNReal.isClosedEmbedding toENNReal_strictMono.injective

end ENat
