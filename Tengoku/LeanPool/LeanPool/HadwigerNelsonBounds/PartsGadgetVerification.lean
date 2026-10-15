/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.PartsGadgetMiddleData
public import Tengoku

/-! Kernel verification of the two normalized second-stage coloring trees. -/

@[expose] public section

namespace HadwigerNelsonBounds

/-- The middle-color normalized second-stage certificate checks by reduction.
@isnad1 id=verifies.0h0v.s1.92f1461e50c9 from=translated src=- shape=49959d42 vocab=5a70a068
-/
theorem partsGadgetMiddleCertificate_verifies :
    partsGadgetMiddleCertificate.Verifies := by
  decide

end HadwigerNelsonBounds
