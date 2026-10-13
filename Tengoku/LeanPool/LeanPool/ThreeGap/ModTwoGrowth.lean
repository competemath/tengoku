/-
Copyright (c) 2026 Vico Bonfioli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vico Bonfioli
-/
module

public import Tengoku.LeanPool.LeanPool.ThreeGap.SimultaneousApprox
public import Tengoku

/-!
# The any-norm growth inequality via the mod-2 pigeonhole (Lagarias II, Theorem 6)

The canonical growth inequality for best simultaneous Diophantine approximations, valid for **every
norm** on `ℝ^d` (Lagarias, *Best simultaneous Diophantine approximations II*, Pacific J. Math. 102
(1982), Thm 6; restated in the Chevallier survey 2011, p. 5):

  `q_{n + 2^{d+1}} ≥ 2 q_{n+1} + q_n`.

The proof is a **mod-2 pigeonhole**: among the `2^{d+1} + 1` best-approximation vectors
`(P_{n+k}, q_{n+k})`, two agree mod 2 (there are only `2^{d+1}` parity classes in `(ℤ/2)^{d+1}`);
their half-difference `(P, q)` is an integer vector with `0 < q < q_{n+1}` and remainder norm
`≤ ½(δ_{q_{n+1}} + δ_{q_n}) < δ_{q_n}`, contradicting the best-approximation/record property.

To get genuine **any-norm** generality we abstract the norm as a function `N` with the three norm
properties (`hN_nonneg`, `hN_tri`, `hN_smul`) and the approximation defect as `δ` (a lower bound on
`N (rem …)`, with the best-approximation record structure). The norm-free remainder algebra
(`SimApprox.rem`, `rem_sub`, `rem_two_smul`) is reused verbatim. Instantiating `N` at the Euclidean
norm gives the Euclidean growth inequality (`q_{n+8} ≥ 2q_{n+1}+q_n` for `d = 2`), the input for the
five-distance theorem.

Axiom-clean.
-/

@[expose] public section

namespace ThreeGap.SimApprox

end ThreeGap.SimApprox
