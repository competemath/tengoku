/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter2.Section2_6.RatFuncEmbedding
import Tengoku.Seed.RingTheory.HahnSeries.Binomial
import Tengoku.Seed.RingTheory.HahnSeries.HEval
import Tengoku.Seed.FieldTheory.IsRealClosed.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # BPR §2.6 Lemma 2.93 — positive elements of `R⟨⟨ε⟩⟩` are squares

For `R` a real closed field, every positive element of the ordered field of Puiseux series
`R⟨⟨ε⟩⟩` is a square. Following BPR: write a positive `ā = a_k ε^{k/q}(1 + b̄)` with `a_k > 0`
and `o(b̄) > 0`; the square root of `1 + b̄` is the Taylor expansion `(1 + b̄)^{1/2}`, and since
`R` is real closed `√a_k ∈ R`, so `√a_k · ε^{k/(2q)} · (1 + b̄)^{1/2}` is a square root of `ā`.

The Taylor expansion `(1 + b̄)^{1/2}` is realized by Mathlib's `PowerSeries.heval` (evaluation of
the binomial power series at the positive-order series `b̄`), with `(1+X)^{1/2}` squaring to
`1 + X` via `binomialSeries_add`. The construction is carried out one denominator `q` lower (the
`(1+b̄)^{1/2}` part needs no finer exponents), and only the leading monomial requires the finer
denominator `2q`; this keeps everything inside the bounded-denominator subfield `R⟨⟨ε⟩⟩`.
-/

namespace Azurite.BPR

open HahnSeries PowerSeries

variable {R : Type*} [Field R]

/-- `puiseuxEmb` of a single term scales the exponent by `1/q`.-/
theorem puiseuxEmb_single (q : ℕ+) (g : ℤ) (r : R) :
    puiseuxEmb R q (HahnSeries.single g r) = HahnSeries.single (puiseuxExpHom q g) r := by
  rw [puiseuxEmb, HahnSeries.embDomainRingHom_apply, HahnSeries.embDomain_single]; rfl

variable [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- A positive element of a real closed field is a square.-/
theorem isSquare_of_pos {x : R} (hx : 0 < x) : IsSquare x := by
  rcases IsRealClosed.isSquare_or_isSquare_neg x with h | h
  · exact h
  · obtain ⟨t, ht⟩ := h; exfalso; nlinarith [mul_self_nonneg t]

end Azurite.BPR
