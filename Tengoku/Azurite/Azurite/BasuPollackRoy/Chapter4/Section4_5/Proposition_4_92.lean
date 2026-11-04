/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_90
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Theorem_4_86
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Definition_4_89
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_5.Lemma_4_87
import Tengoku.Azurite.Azurite.BasuPollackRoy.Chapter4.Section4_4.Theorem_4_72
import Tengoku.Seed.RingTheory.Nullstellensatz
import Tengoku.Seed.RingTheory.Nilpotent.Defs
import Tengoku.Seed.Algebra.CharP.Algebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# BPR §4.5, Proposition 4.92: a complete set of orthogonal idempotents indexed by the zeros

Let `K` be a field of characteristic zero, `C` an algebraically closed field extension of `K`,
and `𝒫` a finite subset of `K[X₁, …, X_k]` with `Zer(𝒫, Cᵏ)` finite. Then there is a family
`(e_x)_{x ∈ Zer(𝒫, Cᵏ)}` of elements of `Ā = C[X]/Ideal(𝒫, C)` that is a complete set of
orthogonal idempotents (`∑ e_x = 1`, `e_x e_y = 0` for `x ≠ y`, `e_x² = e_x`), and such that
`e_x` evaluates to `1` at `x` and to `0` at every other zero `y`.
-/

namespace Azurite.BPR.Chapter4

open MvPolynomial
open scoped Classical

variable {k : ℕ} {K : Type*} [Field K]

/-- Evaluating the image of a constant `c ∈ C` in `Ā` returns `c`.
@isnad1 id=eq.1h6v.s8.6bbc45cc144c from=translated src=- shape=991d5d58 vocab=18f395d9
-/
theorem evalBar_algebraMap {C : Type*} [Field C] [Algebra K C]
    (Ps : Finset (MvPolynomial (Fin k) K)) (z : Fin k → C) (hz : z ∈ zerOfFinset C Ps) (c : C) :
    evalBar C Ps z hz (algebraMap C (quotPolysExt C Ps) c) = c := by
  rw [← Ideal.Quotient.mk_algebraMap, evalBar_mk]
  show MvPolynomial.aeval z (MvPolynomial.C c) = c
  rw [MvPolynomial.aeval_C]
  rfl

/-- **Nilpotency criterion.** If `w ∈ Ā` evaluates to `0` at every zero of `𝒫`, then `w` is
nilpotent.
@isnad1 id=isnilpot.1h5v.s8.98faac8c95c7 from=translated src=- shape=4bedd0b0 vocab=ceaf74ab
-/
theorem nilpotent_of_eval_zero {C : Type*} [Field C] [IsAlgClosed C] [Algebra K C]
    (Ps : Finset (MvPolynomial (Fin k) K)) (w : quotPolysExt C Ps)
    (h : ∀ (z : Fin k → C) (hz : z ∈ zerOfFinset C Ps), evalBar C Ps z hz w = 0) :
    IsNilpotent w := by
  obtain ⟨W, hW⟩ := Ideal.Quotient.mk_surjective w
  have hWvanish : ∀ z ∈ zerOfFinset C Ps, MvPolynomial.aeval z W = 0 := by
    intro z hz
    have := h z hz
    rw [← hW, evalBar_mk] at this
    exact this
  have hWrad : W ∈ (idealOfPolysExt C Ps).radical := by
    have hmem : W ∈ MvPolynomial.vanishingIdeal C (zerOfFinset C Ps) :=
      MvPolynomial.mem_vanishingIdeal_iff.mpr hWvanish
    rw [zerOfFinset_eq_zeroLocus, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at hmem
    exact hmem
  obtain ⟨m, hm⟩ := Ideal.mem_radical_iff.mp hWrad
  refine ⟨m, ?_⟩
  rw [← hW, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact hm
