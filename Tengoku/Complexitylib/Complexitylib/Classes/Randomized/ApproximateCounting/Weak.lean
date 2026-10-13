/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Classes.Randomized.ApproximateCounting.Weak.Defs
import Tengoku.Complexitylib.Complexitylib.Classes.Randomized.ApproximateCounting.Weak.Internal

/-!
# Weak approximate counting

Accurate high- and low-occupancy answers at logarithmically many hash widths
determine the set cardinality within a symmetric factor of sixteen.
-/

public section

namespace Complexity

namespace ApproximateCounting

namespace Weak

/-- Every weak estimate fits below the first power of two beyond its finite
level range.
@isnad1 id=lt.0h2v.s5.7ac9045bfa53 from=translated src=- shape=7eade5ef vocab=15a04ed5
-/
theorem estimate_lt_two_pow_add_four {domainWidth : ℕ}
    (responses : Level domainWidth → Bool) :
    estimate responses < 2 ^ (domainWidth + 4) :=
  estimate_lt_two_pow_add_four_internal responses

/-- The weak Stockmeyer estimator gives a factor-`16` approximation whenever
all occupancy responses satisfy their high- and low-mean contracts.
@isnad1 id=isfactor.2h3v.s5.15ed2bb5752b from=translated src=- shape=acc50611 vocab=ef2d3715
-/
theorem estimate_isFactorApproximation
    {domainWidth cardinality : ℕ} {responses : Level domainWidth → Bool}
    (hcardinality : cardinality ≤ 2 ^ domainWidth)
    (haccurate : ResponsesAccurate (cardinality := cardinality) responses) :
    IsFactorApproximation 16 cardinality (estimate responses) :=
  estimate_isFactorApproximation_internal hcardinality haccurate

end Weak

end ApproximateCounting

end Complexity
