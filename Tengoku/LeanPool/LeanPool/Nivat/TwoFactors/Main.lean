/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import Tengoku.LeanPool.LeanPool.Nivat.Core.Lattice
public import Tengoku.LeanPool.LeanPool.Nivat.Core.BoundedDifferences
public import Tengoku.LeanPool.LeanPool.Nivat.TwoFactors.WindowNormalization
public import Tengoku.LeanPool.LeanPool.Nivat.TwoFactors.WindowCriterion

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Two difference operators

Theorem 5.1 (`thm:twofactor`) of `paper/nivat.tex`. A primitive lattice basis
puts the first direction on the horizontal axis. Lemma 5.5 selects and
normalizes a low-cost boundary in the preimage of the original rectangle.
The positive-height argument uses Lemmas 5.6–5.8; a one-row window uses the
factorial common period from Corollary 5.3. Directional periods are transported
back through both coordinate changes. The parallel case uses bounded finite
differences. The final corollary treats sums of two periodic configurations.
-/

@[expose] public section

namespace Nivat.TwoFactors

/-- The word complexity of any row is bounded by the configuration's horizontal-edge complexity,
which counts translations on all rows. Theorem 5.1 (`thm:twofactor`), one-row case using
Corollary 5.3 (`cor:morse`). -/
theorem wordComplexity_row_le {A : Type*} (c : Configuration A) (hc : FiniteRange c)
    (e : ℕ) (j : ℤ) :
    wordComplexity (fun i : ℤ => c (i, j)) e ≤ complexity c (rowPrefix e) := by
  let extract : (rowPrefix e → A) → (Fin e → A) := fun p r =>
    p ⟨((r : ℕ), 0), (mem_rowPrefix _ e).mpr ⟨r, r.isLt, rfl⟩⟩
  have hsubset : Set.range (word (fun i : ℤ => c (i, j)) e) ⊆
      extract '' patterns c (rowPrefix e) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨patternAt c (rowPrefix e) (i, j), ⟨(i, j), rfl⟩, ?_⟩
    funext r
    simp [extract, patternAt, word, add_comm]
  exact (Set.ncard_le_ncard hsubset ((patterns_finite hc _).image extract)).trans
    (Set.ncard_image_le (patterns_finite hc _))

/-- In the one-row case of Theorem 5.1 (`thm:twofactor`), Corollary 5.3
bounds every row period by the edge length, so its factorial is a period of
all rows simultaneously. -/
theorem isPeriod_factorial_of_lowcomplex_rowPrefix {A : Type*} (c : Configuration A)
    (hc : FiniteRange c) (e : ℕ) (he : 0 < e)
    (hlow : complexity c (rowPrefix e) ≤ e) :
    IsPeriod c ((e.factorial : ℤ), 0) := by
  rintro ⟨i, j⟩
  have hrowfin : (Set.range (fun i : ℤ => c (i, j))).Finite := hc.subset (by
    rintro _ ⟨l, rfl⟩
    exact ⟨(l, j), rfl⟩)
  obtain ⟨p, hp, hpe, hper⟩ := morse_hedlund (fun i : ℤ => c (i, j)) hrowfin e he
    ((wordComplexity_row_le c hc e j).trans hlow)
  obtain ⟨k, hk⟩ := Nat.dvd_factorial hp hpe
  have h := hper.nat_mul k i
  simpa only [Prod.mk_add_mk, add_zero, hk, Nat.cast_mul, mul_comm] using h

/-- Reversing the transverse direction preserves the mixed-difference identity, by commutation
and negation of a period. Theorem 5.1 (`thm:twofactor`). -/
theorem mixed_difference_neg_right {A : Type*} [AddCommGroup A]
    (c : Configuration A) (h t : Lattice) (hmix : difference h (difference t c) = 0) :
    difference h (difference (-t) c) = 0 := by
  rw [difference_comm]
  apply (difference_eq_zero_iff (-t) _).mpr
  apply IsPeriod.neg
  apply (difference_eq_zero_iff t _).mp
  rwa [difference_comm]

end Nivat.TwoFactors

namespace Nivat

/-- Difference operators distribute over sums, the algebraic observation after
Theorem 5.1 (`thm:twofactor`) that gives the two-periodic-summand corollary. -/
theorem difference_add {A : Type*} [AddCommGroup A] (h : Lattice)
    (a b : Configuration A) : difference h (a + b) = difference h a + difference h b := by
  funext z
  simp only [difference_apply, Pi.add_apply]
  abel

end Nivat
