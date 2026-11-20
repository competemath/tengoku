/-
Copyright (c) 2026 Brandon Yates. All rights reserved.
Released under Apache 2.0 license.
-/
import Tengoku.Grlab.GRLab.SSRicci

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar curvature and the Einstein tensor of the static spherically symmetric chart

`GRLab.SSRicci.ricci_ss` computes the Ricci tensor of

  `ds² = −f(r) dt² + f(r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²`

for an *arbitrary* lapse `f`.  Contracting it with the inverse metric
`diag(−1/f, f, 1/r², 1/(r² sin²θ))` collapses the four diagonal Ricci components onto the
two scalar brackets of `GRLab/Lapse.lean`,

  `A(r) := 1 − f − r f′`   (areal / angular block),
  `B(r) := f″/2 + f′/r`    (radial block),

giving the **Ricci scalar**

  `R = 2A/r² − 2B`.

The two `tt`/`rr` contributions each contribute `−B` (the lapse cancels), and the two
angular contributions each contribute `A/r²` (the `sin²θ` cancels).

Values, cross-checked against an independent sympy implementation of the exact index
formulas used here and against a separate computer-algebra curvature engine:

| solution                | `A`       | `B`       | `R = 2A/r² − 2B` |
| ----------------------- | --------- | --------- | ---------------- |
| Schwarzschild           | `0`       | `0`       | `0`              |
| Reissner–Nordström      | `Q²/r²`   | `Q²/r⁴`   | `0`              |
| Schwarzschild–de Sitter | `Λr²`     | `−Λ`      | `4Λ`             |
| static de Sitter        | `Λr²`     | `−Λ`      | `12/L²` (`Λ = 3/L²`) |

The Reissner–Nordström row is the tracelessness of the Maxwell stress tensor, and it is
what makes `GRLab.ReissnerNordstrom` able to read the Einstein tensor straight off the
Ricci tensor; that is the second theorem here.
-/

namespace GRLab

open Matrix Filter Topology

end GRLab
