/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.Truncation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `thm:increments-levy`, part one: the null-array estimate

Home: line:thm:increments-levy

Blueprint: `blueprint/src/parts/05-cascade.tex`, `thm:increments-levy`, the first step of the
proof ("the null array").

In the semigroup case every kernel is a convolution power and infinite divisibility is
immediate. In the hemigroup case there is no such power, and what replaces it is a null-array
limit: for the uniform partition `s = s_0 < ... < s_n = t` and `Π_n := Σ_i μ_{s_i,s_{i+1}}`,

  `∫ (1 - cos ω x) dΠ_n(x) → g_{s,t}(ω)` for every `ω`.

Each `Π_n` is a *finite* measure, of mass `n`; the divergence of the masses is what the
weighting of `LevyExtraction` cures.

## Why this step is elementary

Three ingredients, and no limit theorem for triangular arrays:

* additivity (`sum_exponent_part`), which makes `g_{s,t}(ω)` the sum of the increments;
* uniform continuity of `G(·,ω)` on the compact `[s,t]`, which makes the increments uniformly
  small;
* the inequality `0 ≤ u - (1 - e^{-u}) ≤ u²` (`sub_one_sub_exp_neg_le`, in
  `Truncation`), which converts a sum of exponents into a sum of
  `1 - μ̂_i(ω)`, that is into an integral against `Π_n`.

twin: `Hemigroup.CascadeCore.tendsto_integral_partitionMeasure` (`Hemigroup/NullArray.lean`),
which this file follows step for step with `1 - e^{-sx}` replaced by `1 - cos ωx`. The
partition points and their six elementary lemmas are Paper I's verbatim; they are a candidate
for `ScaleSpaceCore`, being about `ℝ` alone.

## Provenance

Moved by Q-0305 from Paper V's `SpatialLine/NullArray.lean` (the public cone export,
`cone-v0.1`, commit `f28c066e`) for the line classification (`MainAnalysis`,
`MainConstruction`): only the declarations those theorems reach, with statements and
proofs unchanged up to the namespace. Blueprint labels are Paper V's.
-/

namespace ScaleSpace

open MeasureTheory Set Filter Finset
open scoped ENNReal Topology

/-! ## The uniform partition -/

/-- The `i`-th point of the uniform `n`-partition of `[s,t]`. Total in `n`: at `n = 0` the Lean
convention `i / 0 = 0` makes every point `s`, which no statement below uses.

twin: `Hemigroup.part`, verbatim.-/
noncomputable def part (s t : ℝ) (n i : ℕ) : ℝ := s + (i / n : ℝ) * (t - s)

/--
@isnad1 id=eq.0h3v.s4.c446c92a2864 from=translated src=- shape=85114b07 vocab=d333ffcb
-/
@[simp] lemma part_zero (s t : ℝ) (n : ℕ) : part s t n 0 = s := by simp [part]

/--
@isnad1 id=eq.1h3v.s4.df438e41aa23 from=translated src=- shape=174e2989 vocab=d333ffcb
-/
lemma part_self {n : ℕ} (hn : n ≠ 0) (s t : ℝ) : part s t n n = t := by
  rw [part, div_self (Nat.cast_ne_zero.mpr hn)]
  ring

variable {s t : ℝ}

/--
@isnad1 id=le.1h4v.s5.3583e867f9ae from=translated src=- shape=1cac4067 vocab=8435a46d
-/
lemma part_le_succ (hst : s ≤ t) (n i : ℕ) : part s t n i ≤ part s t n (i + 1) := by
  have hfrac : (i / n : ℝ) ≤ ((i + 1 : ℕ) / n : ℝ) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
      gcongr
      exact_mod_cast Nat.le_succ i
  have hd : 0 ≤ t - s := sub_nonneg.mpr hst
  rw [part, part]
  nlinarith

/--
@isnad1 id=mem.3h4v.s5.97a2c884eae2 from=translated src=- shape=056e999f vocab=9ffca277
-/
lemma part_mem_Icc (hst : s ≤ t) {n i : ℕ} (hn : n ≠ 0) (hi : i ≤ n) :
    part s t n i ∈ Icc s t := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h0 : (0 : ℝ) ≤ (i / n : ℝ) := by positivity
  have h1 : (i / n : ℝ) ≤ 1 := by
    rw [div_le_one hn']
    exact_mod_cast hi
  have hd : 0 ≤ t - s := sub_nonneg.mpr hst
  constructor
  · rw [part]; nlinarith
  · rw [part]; nlinarith

/--
@isnad1 id=le.2h4v.s5.b9688e56c900 from=translated src=- shape=756130b9 vocab=7f4e3365
-/
lemma part_nonneg (hs : 0 ≤ s) (hst : s ≤ t) (n i : ℕ) : 0 ≤ part s t n i := by
  have hfrac : (0 : ℝ) ≤ (i / n : ℝ) := by positivity
  have hd : 0 ≤ t - s := sub_nonneg.mpr hst
  rw [part]
  nlinarith

/-- The mesh: consecutive partition points are `(t - s)/n` apart.
@isnad1 id=eq.1h4v.s6.2a0a2d1aec25 from=translated src=- shape=0f8c1618 vocab=55ed6fba
-/
lemma part_succ_sub {n : ℕ} (hn : n ≠ 0) (s t : ℝ) (i : ℕ) :
    part s t n (i + 1) - part s t n i = (t - s) / n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [part, part]
  push_cast
  field_simp
  ring

/-! ## Additivity along the partition -/

variable {Fam : PreCascadeCore} {μ : ℝ → ℝ → Measure ℝ}

/-! ## `Π_n`, the partition measures -/

/-- `Π_n = Σ_i μ_{s_i,s_{i+1}}`: a finite measure of total mass `n`.-/
noncomputable def partitionMeasure (μ : ℝ → ℝ → Measure ℝ) (s t : ℝ) (n : ℕ) : Measure ℝ :=
  ∑ i ∈ range n, μ (part s t n i) (part s t n (i + 1))

/-- An integral against `Π_n` is the sum of the integrals against the increments.
@isnad1 id=eq.1h5v.s7.a55d0f11e94e from=translated src=- shape=bcd7cee2 vocab=876e3b99
-/
lemma integral_partitionMeasure_eq_sum (μ : ℝ → ℝ → Measure ℝ) (s t : ℝ) (n : ℕ) {f : ℝ → ℝ}
    (hf : ∀ i ∈ range n, Integrable f (μ (part s t n i) (part s t n (i + 1)))) :
    ∫ x, f x ∂(partitionMeasure μ s t n)
      = ∑ i ∈ range n, ∫ x, f x ∂(μ (part s t n i) (part s t n (i + 1))) := by
  rw [partitionMeasure, integral_finsetSum_measure hf]

/-! ## The estimate

The whole of the null-array argument, in one inequality. The caller supplies the bound `m` on
the partition increments; where `m` comes from — uniform continuity — is separated out below,
so that this step has no analysis in it at all.
-/

/-! ## The mesh vanishes

The only analysis in the file: `G(·,ω)` is continuous on the compact `[s,t]`, hence uniformly
continuous there, so the partition increments — differences of `G` across a gap of `(t-s)/n` —
are eventually uniformly small.
-/

end ScaleSpace
