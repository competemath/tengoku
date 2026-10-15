/-
Copyright (c) 2026 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
module

public import Tengoku
import Tengoku.LeanPool.LeanPool.SardMoreira.MeasureComap

/-!
# LeanPool.SardMoreira.MeasureNNReal
-/

@[expose] public section

open scoped ENNReal NNReal Set.Notation Pointwise
open MeasureTheory Filter Set Function Metric Topology

noncomputable instance instMeasureSpaceNNRealLeanPool : MeasureSpace ℝ≥0 where
  volume := .comap (↑) (volume : Measure ℝ)

/--
@isnad1 id=eq.0h0v.s4.b46687d7dc4e from=translated src=- shape=f8dce2c6 vocab=52328930
-/
theorem NNReal.volume_def : (volume : Measure ℝ≥0) = .comap (↑) (volume : Measure ℝ) := rfl

-- TODO: should we have this instance? I'm not sure.
