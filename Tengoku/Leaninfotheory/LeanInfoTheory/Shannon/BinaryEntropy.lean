/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.Entropy
import Tengoku

/-!
# Boolean entropy

This opt-in module identifies the project's finite Shannon entropy of a
Boolean PMF with mathlib's `Real.binEntropy`. Both sides use natural
logarithms, so the identity is in nats.
-/

namespace LeanInfoTheory
namespace Shannon

open scoped BigOperators

noncomputable section

/--
The entropy of a Boolean PMF is the binary entropy of its `true` mass.

The identity includes the endpoint laws without separate positivity
assumptions.
-/
theorem entropy_bool (p : PMF Bool) :
    entropy p = Real.binEntropy (p true).toReal := by
  have hfalse : (p false).toReal = 1 - (p true).toReal := by
    have hmass := PMF.sum_toReal p
    rw [Fintype.sum_bool] at hmass
    linarith
  rw [entropy_eq_sum, Fintype.sum_bool,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hfalse]

end

end Shannon
end LeanInfoTheory
