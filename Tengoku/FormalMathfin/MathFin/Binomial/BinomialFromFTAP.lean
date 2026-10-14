/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Tengoku
public import Tengoku.FormalMathfin.MathFin.Foundations.FTAPTwoState
public import Tengoku.FormalMathfin.MathFin.Binomial.Model

/-!
# Binomial price as iterated two-state FTAP (phase 43)

The pre-existing `Binomial/Model.lean` defines the one-period option
pricing formula `binomialOptionPriceOnePeriod` directly as `e^{−r}·(q·V_u
+ (1−q)·V_d)` with `q = (e^r − d) / (u − d)`, and verifies it via the
replicating-portfolio cost.

This file derives the **same q** from the two-state FTAP machinery in
`Foundations/FTAPTwoState.lean` (phase 37, after Nagy 2026). The binomial
risk-neutral up-probability `q = (e^r − d) / (u − d)` is exactly the
EMM weight constructed from the excess-return data

  `z_u := u − e^r,    z_d := d − e^r`,

under the no-arbitrage condition `d < e^r < u` (which gives `z_u > 0,
z_d < 0`, matching Nagy's `emm_of_signs`).

## Why this is a useful bridge

It connects two strands previously separate in our library:
- `Foundations/FTAPTwoState.lean` (phase 37): general two-state EMM
  construction from sign data.
- `Binomial/Model.lean`: specific binomial-tree pricing with `q = (e^r −
  d)/(u − d)`.

The connection: **the binomial `q` IS the EMM**. The same Nagy backward
FTAP construction (Theorem 7.3) gives the binomial up-probability. This
makes `binomialOptionPriceOnePeriod` a *consequence* of the general
no-arbitrage principle, not a stand-alone definition.

## Results

* `binomial_excess_return_signs`: under `BinomialNoArb`, `z_u > 0` and
  `z_d < 0`.
* `binomial_q_eq_emm`: the EMM constructed from `(z_u, z_d)` via
  Nagy's formula matches `crrUpProb` from `Binomial/Model.lean`.
* `binomial_emm_exists`: under `BinomialNoArb`, an EMM exists for the
  excess-return market `(z_u, z_d)`.
-/

@[expose] public section

namespace MathFin

/-- **Excess-return signs from `BinomialNoArb`**: under `d < e^r < u`,
the up-state excess return `z_u = u − e^r > 0` and the down-state
excess return `z_d = d − e^r < 0`.
@isnad1 id=and.1h3v.s5.d0d5f5b57756 from=translated src=- shape=3e41ec98 vocab=1500a003
-/
theorem binomial_excess_return_signs {u d r : ℝ} (h : BinomialNoArb u d r) :
    0 < u - Real.exp r ∧ d - Real.exp r < 0 := by
  refine ⟨?_, ?_⟩
  · linarith [h.lt_u]
  · linarith [h.d_lt]

/-- **EMM existence in the binomial market** (Nagy 2026 §7 applied to the
binomial excess-return market). Under `BinomialNoArb`, the excess-return
vector `(u − e^r, d − e^r)` satisfies the sign condition of Nagy's
backward FTAP (Theorem 7.3), so an EMM exists.
@isnad1 id=hasemmtw.1h3v.s5.14ac5d7d919b from=translated src=- shape=02e57f67 vocab=d5ac2408
-/
theorem binomial_emm_exists {u d r : ℝ} (h : BinomialNoArb u d r) :
    HasEMM_two_state (u - Real.exp r) (d - Real.exp r) :=
  emm_of_signs (u - Real.exp r) (d - Real.exp r)
    (binomial_excess_return_signs h).1 (binomial_excess_return_signs h).2

/-- **The binomial up-probability `q` equals the EMM weight** constructed
from the excess-return data via Nagy's backward FTAP formula. With
`z_u := u − e^r, z_d := d − e^r`:

  `−z_d / (z_u − z_d) = (e^r − d) / (u − d) = crrUpProb u d r`.

The two characterisations of the risk-neutral up-probability — *binomial
replicating-portfolio formula* (current `Binomial/Model.lean`) and
*EMM constructed from no-arbitrage* (Phase 37 backward FTAP) — coincide.
@isnad1 id=eq.1h3v.s6.9c04c8692569 from=translated src=- shape=7c598e63 vocab=47a8a511
-/
theorem binomial_q_eq_emm {u d r : ℝ} (_h : BinomialNoArb u d r) :
    -(d - Real.exp r) / ((u - Real.exp r) - (d - Real.exp r)) =
      crrUpProb u d r := by
  unfold crrUpProb
  have h_denom_eq : (u - Real.exp r) - (d - Real.exp r) = u - d := by ring
  have h_num_eq : -(d - Real.exp r) = Real.exp r - d := by ring
  rw [h_denom_eq, h_num_eq]

/-- **No-arbitrage in the binomial market** (forward FTAP applied):
`BinomialNoArb` ⟹ no portfolio can produce a sure non-negative excess
return with at least one strictly positive outcome.
@isnad1 id=not.1h3v.s5.cb0798092992 from=translated src=- shape=1b09f094 vocab=3bb8fc8e
-/
theorem binomial_no_arbitrage {u d r : ℝ} (h : BinomialNoArb u d r) :
    ¬ HasArbitrage_two_state (u - Real.exp r) (d - Real.exp r) :=
  noArbitrage_of_emm _ _ (binomial_emm_exists h)

end MathFin
