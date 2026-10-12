/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import Tengoku.LeanPool.LeanPool.Nivat.Algebra.Action
public import Tengoku.LeanPool.LeanPool.Nivat.Core.Patterns
public import Tengoku

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
# Multiples supported in a rectangle

The support equality in Lemma 2.1 (`lem:supported`) is
`support_mul_subset_rectangle_iff`. Coordinate extrema of a nonzero product
add: lexicographic refinement gives an extreme support pair whose sum has a
unique representation and therefore a nonzero coefficient.

The definitions `erosion` and `erodedWindow` express containment of every
translated filter-support point. The equality holds for empty erosion as well
as for positive rectangles. The injective finite multiplier map and the
associated dimension calculation from Lemma 2.1 are constructed in
`Nivat.Descent.ExactDescent`, where they enter Theorem 2.2 (`thm:descent`).
-/

@[expose] public section

namespace Nivat.Algebra

open scoped Pointwise

/-- The eroded support window in Section 1.2, equation (`eq:erosion-definition`), and Lemma 2.1
(`lem:supported`): all translates of the filter support contained in the target. -/
def erosion (Φ : Laurent) (R : Finset Lattice) : Set Lattice :=
  {z | ∀ a ∈ Φ.coeff.support, z + a ∈ R}

/-- Auxiliary to Lemma 2.1 (`lem:supported`): erosion by a nonzero filter is finite because any one
support point embeds it into a translate of the finite target window. -/
theorem erosion_finite (Φ : Laurent) (hΦ : Φ ≠ 0) (R : Finset Lattice) :
    (erosion Φ R).Finite := by
  have hS : Φ.coeff.support.Nonempty := by simpa [Finsupp.support_nonempty_iff] using hΦ
  obtain ⟨a, ha⟩ := hS
  apply (R.finite_toSet.image (fun r => r - a)).subset
  intro z hz
  exact ⟨z + a, hz a ha, by simp⟩

/-- The finite-set form of the erosion in Lemma 2.1 (`lem:supported`), including empty erosion. -/
noncomputable def erodedWindow (Φ : Laurent) (hΦ : Φ ≠ 0) (R : Finset Lattice) :
    Finset Lattice := (erosion_finite Φ hΦ R).toFinset

/-- The membership condition for the eroded window of Lemma 2.1 (`lem:supported`). -/
@[simp] theorem mem_erodedWindow (Φ : Laurent) (hΦ : Φ ≠ 0) (R : Finset Lattice)
    (z : Lattice) : z ∈ erodedWindow Φ hΦ R ↔ ∀ a ∈ Φ.coeff.support, z + a ∈ R := by
  simp [erodedWindow, erosion]

end Nivat.Algebra
