/-
Copyright (c) 2026 Scott D. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott D. Hughes
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos137.JointFiniteness
public import Tengoku

/-!
# Erdős Problem #137: the smooth-part radical refinement and the sharpened threshold (g = 3)

`Erdos137/Finiteness.lean` derives the threshold `n > k^6` from the crude powerful bound
`rad(F k n)^2 ≤ F k n` (`powerful_rad_sq_le`). That bound is wasteful: the `k`-smooth part of a
powerful `F k n` is itself very powerful, and its radical is bounded by the primorial of `k`.

The smooth-part machinery itself — the primorial-type quantities `P`, `L`, the smooth/rough split
`Ssmooth`/`Rrough`, and the smooth refinement `rad (F k n) ^ 2 * L k ≤ F k n * P k ^ 2`
(`smooth_refinement`) — is `g`-independent and now lives in `Erdos137.Base`. This file specializes
it to the `g = 3` smooth-refined threshold via the generic master inequality `master_ineq_g 3`
(`BlockFramework`).

The headline `not_powerful_of_large'` is stated in the exact, fully-proved integer form

  `(k^{2k})^3 · P^6 < n^k · L^3  ⟹  ¬ Powerful (F k n)`;

feeding in the Mertens lower bound `log L = k log k − O(k)` (which is not in Mathlib and so is not
formalized here) turns this threshold into `n > k^{3 + o(1)}`, cubically below the crude `k^6`.

The smooth-refined master inequality `master_ineq` is the `g = 3` instance of the generic
`master_ineq_g`: with `(3 - 2) * k = k` and `2 * 3 = 6`, `master_ineq_g 3` reads
`n^k · L^3 ≤ (k^{2k})^3 · P^6`. The `BlockRadLB` hypothesis is the `g = 3` instance of `BlockRadLBg`
(via `blockRadLB_iff`).
-/

@[expose] public section

namespace Erdos137

open scoped BigOperators
open Finset

noncomputable section

/-! ## The sharpened threshold

Feeding `smooth_refinement` (`rad(F)^2 · L ≤ F · P^2`) into the block chain
`Φ^{2/3} ≤ ∏ rad ≤ rad(F) · W ≤ rad(F) · k^k` (with `W ≤ k^k`, `Φ = F k n`) in place of the crude
`rad(F)^2 ≤ Φ` gives, after squaring and dividing by `Φ`,

  `Φ^{1/3} · L ≤ k^{2k} · P^2`,

equivalently (cubing, and using `Φ ≥ n^k`)

  `n^k · L^3 ≤ k^{6k} · P^6`.

This is the **smooth-refined master inequality** (`master_ineq`); the crude route gave only
`n^k ≤ k^{6k}` (i.e. `n ≤ k^6`). The new inequality has the extra `L^3` on the left — the smooth
gain — so the threshold drops from `k^6` to `k^6 · (P^2 / L)^3 = k^{3 + o(1)}`.

It is the `g = 3` instance of the generic `master_ineq_g`, proved once for all `g ≥ 3` in
`BlockFramework`. -/

/-- **Smooth-refined master inequality.** Under `BlockRadLB`, for `k ≥ 3` and a powerful `F k n`
with `n ≥ 1`:  `n^k · L k ^ 3 ≤ (k ^ (2 * k)) ^ 3 * P k ^ 6`. The left factor `L k ^ 3` is the
smooth gain absent from the crude `n^k ≤ (k^{2k})^3 = k^{6k}` route. The `g = 3` instance of
`master_ineq_g` (`(3 - 2) * k = k`, `2 * 3 = 6`). -/
theorem master_ineq (hBlock : BlockRadLB) {k n : ℕ}
    (hk : 3 ≤ k) (hn : 1 ≤ n) (hPow : Powerful (F k n)) :
    (n : ℝ) ^ k * (L k : ℝ) ^ 3 ≤ ((k : ℝ) ^ (2 * k)) ^ 3 * (P k : ℝ) ^ 6 := by
  have hg := master_ineq_g 3 (blockRadLB_iff.mp hBlock) (by norm_num) hk hn hPow
  simpa using hg

end  -- noncomputable section

end Erdos137
