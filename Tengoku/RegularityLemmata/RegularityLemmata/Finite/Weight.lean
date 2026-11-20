/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
SPDX-License-Identifier: Apache-2.0
-/
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Data.Finset.SymmDiff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Raw finite weights and masses

The shared raw-weight vocabulary: a weight is an arbitrary `w : X → ℝ`, and the mass of a
finset is the sum of its weights. Nonnegativity is a **hypothesis**, never a field — that is
what keeps this usable by the kernel layer, the box layer, and the existing weighted-choice
machinery without any of them importing the others.

There is deliberately no normalized probability structure anywhere in the library. A
normalized carrier would exclude the empty carrier, make zero-mass cells awkward, force
conditioning to carry normalization proofs, and add coercion friction to every analytic
estimate. Probabilities and expectations are obtained by dividing by a mass at the point of
use, under the guard-free convention that division by zero is zero.

Note that a **nonempty** finset can have **zero** mass: every weight may be zero. Statements
that genuinely need a positive denominator therefore assume `0 < finsetMass w A`, not
`A.Nonempty`. The distinction is load-bearing and recurs throughout the kernel layer.
-/

namespace RegularityLemmata

open scoped symmDiff

variable {X : Type*} {w w' : X → ℝ} {A B : Finset X}

/-- The mass of a finset under a raw weight.-/
def finsetMass (w : X → ℝ) (A : Finset X) : ℝ := ∑ x ∈ A, w x

/-- A weighted sum over a finset.-/
def weightedSum (w : X → ℝ) (A : Finset X) (f : X → ℝ) : ℝ := ∑ x ∈ A, w x * f x

/--
@isnad1 id=eq.0h2v.s4.2d47fd66b2b3 from=translated src=- shape=5c0a7ff2 vocab=f2ca66a4
-/
@[simp] theorem finsetMass_empty (w : X → ℝ) : finsetMass w ∅ = 0 := by
  rw [finsetMass, Finset.sum_empty]

/--
@isnad1 id=eq.0h3v.s4.f3d2e04433f4 from=translated src=- shape=d7704b98 vocab=27a9606d
-/
@[simp] theorem weightedSum_empty (w : X → ℝ) (f : X → ℝ) : weightedSum w ∅ f = 0 := by
  rw [weightedSum, Finset.sum_empty]

/--
@isnad1 id=eq.0h3v.s4.67202ddae7fd from=translated src=- shape=86b3e86d vocab=fba0a8a2
-/
theorem weightedSum_one (w : X → ℝ) (A : Finset X) :
    weightedSum w A (fun _ => 1) = finsetMass w A := by
  rw [weightedSum, finsetMass]
  exact Finset.sum_congr rfl fun x _ => mul_one _

/-- Counting weights recover the cardinality.
@isnad1 id=eq.0h2v.s4.c4d2ea58a583 from=translated src=- shape=41e3fd90 vocab=7c3efe30
-/
@[simp] theorem finsetMass_one (A : Finset X) :
    finsetMass (fun _ => (1 : ℝ)) A = (A.card : ℝ) := by
  rw [finsetMass, Finset.sum_const, nsmul_eq_mul, mul_one]

/--
@isnad1 id=le.1h3v.s5.6693c109f6af from=translated src=- shape=5cb2963f vocab=1d7d4ea0
-/
theorem finsetMass_nonneg (hw : ∀ x ∈ A, 0 ≤ w x) : 0 ≤ finsetMass w A :=
  Finset.sum_nonneg hw

/-- Additivity over a disjoint union.
@isnad1 id=eq.1h4v.s5.80532d855e45 from=translated src=- shape=f6225fa3 vocab=2139985e
-/
theorem finsetMass_union_of_disjoint [DecidableEq X] (w : X → ℝ) (h : Disjoint A B) :
    finsetMass w (A ∪ B) = finsetMass w A + finsetMass w B := by
  rw [finsetMass, finsetMass, finsetMass, Finset.sum_union h]

/-- Monotone in the finset, **given nonnegative weights on the larger one**. Without that
hypothesis a larger finset can carry less mass.
@isnad1 id=le.2h4v.s6.c40fa65b42a9 from=translated src=- shape=ea16ac55 vocab=1d7d4ea0
-/
theorem finsetMass_mono (hw : ∀ x ∈ B, 0 ≤ w x) (h : A ⊆ B) :
    finsetMass w A ≤ finsetMass w B :=
  Finset.sum_le_sum_of_subset_of_nonneg h fun x hx _ => hw x hx

/-- **Rescaling a carrier weight rescales its mass.** The identity behind the rescaling
invariance of normalized quantities.
@isnad1 id=eq.0h4v.s5.aaf99c927011 from=translated src=- shape=3e2ef6d3 vocab=72a7f8c2
-/
theorem finsetMass_smul (c : ℝ) (w : X → ℝ) (A : Finset X) :
    finsetMass (fun x => c * w x) A = c * finsetMass w A := by
  rw [finsetMass, finsetMass, Finset.mul_sum]

/--
@isnad1 id=eq.0h4v.s5.bb044d9971ed from=translated src=- shape=19799c85 vocab=ee0f22f0
-/
theorem finsetMass_add (w w' : X → ℝ) (A : Finset X) :
    finsetMass (fun x => w x + w' x) A = finsetMass w A + finsetMass w' A := by
  rw [finsetMass, finsetMass, finsetMass, Finset.sum_add_distrib]

/-- Additivity over a pairwise-disjoint finite cover.
@isnad1 id=eq.1h3v.s5.12153606b4de from=translated src=- shape=43cc70c7 vocab=729204d3
-/
theorem finsetMass_biUnion [DecidableEq X] (w : X → ℝ) {s : Finset (Finset X)}
    (hdisj : (s : Set (Finset X)).PairwiseDisjoint id) :
    finsetMass w (s.biUnion id) = ∑ A ∈ s, finsetMass w A := by
  rw [finsetMass]
  exact Finset.sum_biUnion hdisj

/-! ### Subadditivity and the symmetric-difference bound

Additivity over a disjoint union is an identity and needs no sign hypothesis. Everything below
compares masses of **different** finsets, which is exactly when a signed weight can make a
larger set lighter, so each carries nonnegativity — stated on the sets involved, never
globally. -/

/-- **Subadditive over a union.** Unlike `finsetMass_union_of_disjoint` this needs
nonnegativity, because the overlap is counted twice on the right.
@isnad1 id=le.1h4v.s6.6e492e294698 from=translated src=- shape=2cc10b93 vocab=d6375d61
-/
theorem finsetMass_union_le [DecidableEq X] {w : X → ℝ} {A B : Finset X}
    (hw : ∀ x ∈ A ∪ B, 0 ≤ w x) : finsetMass w (A ∪ B) ≤ finsetMass w A + finsetMass w B := by
  rw [← Finset.union_sdiff_self_eq_union, finsetMass_union_of_disjoint w Finset.disjoint_sdiff]
  have hle : finsetMass w (B \ A) ≤ finsetMass w B :=
    finsetMass_mono (fun x hx => hw x (Finset.mem_union_right _ hx)) Finset.sdiff_subset
  linarith

/-- **The union bound over a finite family.** Proved by induction: the pinned Mathlib has
cardinality and density versions of this, but no weighted one.
@isnad1 id=le.1h5v.s6.ada23eb9d50c from=translated src=- shape=1bfe8192 vocab=5d148c6f
-/
theorem finsetMass_biUnion_le [DecidableEq X] {w : X → ℝ} {κ : Type*} [DecidableEq κ]
    {s : Finset κ} {t : κ → Finset X} (hw : ∀ x ∈ s.biUnion t, 0 ≤ w x) :
    finsetMass w (s.biUnion t) ≤ ∑ k ∈ s, finsetMass w (t k) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
      rw [Finset.sum_insert hk, Finset.biUnion_insert] at *
      have hrest := ih fun x hx => hw x (Finset.mem_union_right _ hx)
      have hpair := finsetMass_union_le (w := w) hw
      linarith

/-- **A mass difference is controlled by the symmetric difference.**

Nonnegativity is required **only on `A ∆ B`**: the two masses share the mass of `A ∩ B`, which
cancels in the difference, so the weight is unconstrained there. The bound assumes neither
disjointness nor nesting.
@isnad1 id=le.1h4v.s6.f8def2605213 from=translated src=- shape=93f77b8e vocab=4f28f0ea
-/
theorem abs_sub_finsetMass_le [DecidableEq X] {w : X → ℝ} {A B : Finset X}
    (hw : ∀ x ∈ A ∆ B, 0 ≤ w x) :
    |finsetMass w A - finsetMass w B| ≤ finsetMass w (A ∆ B) := by
  have hA : finsetMass w A = finsetMass w (A \ B) + finsetMass w (A ∩ B) := by
    rw [← finsetMass_union_of_disjoint w (Finset.disjoint_sdiff_inter A B),
      Finset.sdiff_union_inter]
  have hB : finsetMass w B = finsetMass w (B \ A) + finsetMass w (B ∩ A) := by
    rw [← finsetMass_union_of_disjoint w (Finset.disjoint_sdiff_inter B A),
      Finset.sdiff_union_inter]
  have hcomm : finsetMass w (B ∩ A) = finsetMass w (A ∩ B) := by rw [Finset.inter_comm]
  have hsplit : finsetMass w (A ∆ B) = finsetMass w (A \ B) + finsetMass w (B \ A) := by
    rw [Finset.symmDiff_def, finsetMass_union_of_disjoint w disjoint_sdiff_sdiff]
  have hAB : 0 ≤ finsetMass w (A \ B) :=
    finsetMass_nonneg fun x hx =>
      hw x (by rw [Finset.symmDiff_def]; exact Finset.mem_union_left _ hx)
  have hBA : 0 ≤ finsetMass w (B \ A) :=
    finsetMass_nonneg fun x hx =>
      hw x (by rw [Finset.symmDiff_def]; exact Finset.mem_union_right _ hx)
  rw [hA, hB, hcomm, hsplit, abs_le]
  constructor <;> linarith

/-! ### Zero mass is not emptiness -/

/-- A nonempty finset all of whose weights vanish has zero mass. This is why positive-mass
hypotheses are not interchangeable with nonemptiness.
@isnad1 id=eq.1h3v.s5.28d6b326e004 from=translated src=- shape=6b4a315e vocab=82d1e962
-/
theorem finsetMass_eq_zero_of_forall_eq_zero (h : ∀ x ∈ A, w x = 0) : finsetMass w A = 0 :=
  Finset.sum_eq_zero h

/-- Under nonnegative weights, positive mass forces a witness of positive weight.
@isnad1 id=ex.2h3v.s6.1fb70f9a542a from=translated src=- shape=05ca2aee vocab=e0d85020
-/
theorem exists_pos_of_finsetMass_pos (hw : ∀ x ∈ A, 0 ≤ w x) (h : 0 < finsetMass w A) :
    ∃ x ∈ A, 0 < w x := by
  by_contra hcon
  push Not at hcon
  exact absurd h (not_lt.mpr (le_of_eq (finsetMass_eq_zero_of_forall_eq_zero fun x hx =>
    le_antisymm (hcon x hx) (hw x hx))))

/-! ### Relative mass

The fraction of a cell's mass carried by a test set. These are exactly the `[0,1]`
coefficients that the bilinear domination lemma of `RegularityLemmata/Finite/Inequalities.lean`
consumes, so
the `≤ 1` bound must hold with **no** positive-mass hypothesis. -/

/-- The relative mass of `S` inside the cell `C`, guard-free: `0` on a zero-mass cell.-/
noncomputable def relMass [DecidableEq X] (w : X → ℝ) (S C : Finset X) : ℝ :=
  finsetMass w (S ∩ C) / finsetMass w C

/--
@isnad1 id=le.1h4v.s5.d42729d3dc7c from=translated src=- shape=4d9aa2e3 vocab=c032b1b7
-/
theorem relMass_nonneg [DecidableEq X] {C : Finset X} (hw : ∀ x ∈ C, 0 ≤ w x)
    (S : Finset X) : 0 ≤ relMass w S C :=
  div_nonneg (finsetMass_nonneg fun x hx => hw x (Finset.mem_of_mem_inter_right hx))
    (finsetMass_nonneg hw)

/-- **Guard-free `≤ 1`.** On a zero-mass cell the quotient is `0/0 = 0`, so no positivity
hypothesis is needed — which is what lets the contraction argument avoid a positive-mass
side condition on every cell.
@isnad1 id=le.1h4v.s5.070245f37c64 from=translated src=- shape=29caf1a1 vocab=c032b1b7
-/
theorem relMass_le_one [DecidableEq X] {C : Finset X} (hw : ∀ x ∈ C, 0 ≤ w x)
    (S : Finset X) : relMass w S C ≤ 1 := by
  rcases eq_or_lt_of_le (finsetMass_nonneg hw) with h | h
  · rw [relMass, ← h, div_zero]
    norm_num
  · rw [relMass, div_le_one h]
    exact finsetMass_mono hw Finset.inter_subset_right

/-- At the full cell the relative mass is `1` — unless the cell has zero mass, where it is
`0`. Both cases are correct; neither needs a guard.
@isnad1 id=eq.1h3v.s5.ee4e0ca2ad3e from=translated src=- shape=216078aa vocab=44e12186
-/
theorem relMass_self_of_pos [DecidableEq X] {C : Finset X} (h : 0 < finsetMass w C) :
    relMass w C C = 1 := by
  rw [relMass, Finset.inter_self, div_self (ne_of_gt h)]

/-! ### Tests -/

section Tests

-- A nonuniform weight on `Fin 3`.

end Tests

end RegularityLemmata
