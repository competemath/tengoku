/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.Core.DyadicCell
import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Topology.Compactness.Compact
import Tengoku.Seed.Topology.MetricSpace.Pseudo.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Infinite dyadic paths

An infinite Boolean history determines a nested sequence of exact closed
dyadic cells. Their widths tend to zero, so their intersection contains exactly
one real point. This is the limit semantics behind finite dyadic addresses.
-/

open scoped LeanCert.Core.Expr

namespace LeanCert.Core

/-- An infinite sequence of left (`false`) and right (`true`) decisions. -/
abbrev InfiniteDyadicPath := Nat → Bool

namespace InfiniteDyadicPath

/-- The finite address consisting of the first `depth` decisions. -/
def finitePrefix (bits : InfiniteDyadicPath) : Nat → DyadicPath
  | 0 => []
  | depth + 1 => finitePrefix bits depth ++ [bits depth]

/-- The closed cell reached after the first `depth` decisions. -/
def cell (root : IntervalDyadic) (bits : InfiniteDyadicPath) : Nat → IntervalDyadic
  | 0 => root
  | depth + 1 =>
      if bits depth then (cell root bits depth).bisect.2
      else (cell root bits depth).bisect.1

/--
@isnad1 id=eq.0h1v.s3.f2554108bbf3 from=translated src=- shape=a4e673c7 vocab=d6aac1bd
-/
@[simp] theorem finitePrefix_zero (bits : InfiniteDyadicPath) : bits.finitePrefix 0 = [] := rfl

/--
@isnad1 id=eq.0h2v.s5.53e1d0838dbf from=translated src=- shape=7900910d vocab=781385e3
-/
@[simp] theorem finitePrefix_succ (bits : InfiniteDyadicPath) (depth : Nat) :
    bits.finitePrefix (depth + 1) = bits.finitePrefix depth ++ [bits depth] := rfl

/--
@isnad1 id=eq.0h2v.s3.c047dd6bd345 from=translated src=- shape=3a916253 vocab=555e7396
-/
@[simp] theorem cell_zero (root : IntervalDyadic) (bits : InfiniteDyadicPath) :
    bits.cell root 0 = root := rfl

/--
@isnad1 id=eq.0h3v.s5.4976179ec04e from=translated src=- shape=264a6d82 vocab=bd2a7d52
-/
@[simp] theorem cell_succ (root : IntervalDyadic) (bits : InfiniteDyadicPath)
    (depth : Nat) :
    bits.cell root (depth + 1) =
      if bits depth then (bits.cell root depth).bisect.2
      else (bits.cell root depth).bisect.1 := rfl

/-- Infinite-path decoding agrees with recursive finite-address decoding at
every finite depth.
@isnad1 id=eq.0h3v.s4.4f30128c0539 from=translated src=- shape=e16dcb96 vocab=343ad075
-/
theorem cell_eq_decode_finitePrefix (root : IntervalDyadic) (bits : InfiniteDyadicPath)
    (depth : Nat) :
    bits.cell root depth = (bits.finitePrefix depth).decodeByBisection root := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [cell_succ, finitePrefix_succ]
      cases hbit : bits depth
      · simp only [Bool.false_eq_true, ↓reduceIte,
          DyadicPath.decodeByBisection_append_false, ih]
      · simp only [↓reduceIte, DyadicPath.decodeByBisection_append_true, ih]

/-- Every successor cell is contained in its predecessor.
@isnad1 id=mem.1h4v.s5.566f2b091e33 from=translated src=- shape=ee11f4e7 vocab=cec76213
-/
theorem mem_cell_of_mem_succ {root : IntervalDyadic} {bits : InfiniteDyadicPath}
    {depth : Nat} {x : ℝ} (hx : x ∈ bits.cell root (depth + 1)) :
    x ∈ bits.cell root depth := by
  rw [cell_succ] at hx
  split at hx
  · exact IntervalDyadic.mem_of_mem_bisect_right hx
  · exact IntervalDyadic.mem_of_mem_bisect_left hx

/-- Exact semantic width after `depth` binary refinements.
@isnad1 id=eq.0h3v.s5.8f2487fcf206 from=translated src=- shape=c137b488 vocab=e27ae41d
-/
theorem cell_width_toRat (root : IntervalDyadic) (bits : InfiniteDyadicPath)
    (depth : Nat) :
    (bits.cell root depth).width.toRat = root.width.toRat * (1 / 2 : ℚ) ^ depth := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      rw [cell_succ]
      split
      · rw [IntervalDyadic.bisect_right_width_toRat, ih, pow_succ]
        ring
      · rw [IntervalDyadic.bisect_left_width_toRat, ih, pow_succ]
        ring

/-- Cell widths along every infinite history converge to zero.
@isnad1 id=tendsto.0h2v.s5.e5e4bf7e54c7 from=translated src=- shape=23dfcae8 vocab=2b1a1ecd
-/
theorem cell_width_tendsto_zero (root : IntervalDyadic) (bits : InfiniteDyadicPath) :
    Filter.Tendsto (fun depth => ((bits.cell root depth).width.toRat : ℝ))
      Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun depth : Nat => (1 / 2 : ℝ) ^ depth)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hmul : Filter.Tendsto
      (fun depth : Nat => (root.width.toRat : ℝ) * (1 / 2 : ℝ) ^ depth)
      Filter.atTop (nhds 0) := by
    simpa using hpow.const_mul (root.width.toRat : ℝ)
  apply hmul.congr'
  exact Filter.Eventually.of_forall fun depth => by
    change (root.width.toRat : ℝ) * (1 / 2 : ℝ) ^ depth =
      ((bits.cell root depth).width.toRat : ℝ)
    rw [cell_width_toRat]
    norm_num

/-- The ordinary real endpoint width also converges to zero.
@isnad1 id=tendsto.0h2v.s5.ce0dcbe5f3f7 from=translated src=- shape=16e3100e vocab=6aceb9c6
-/
theorem cell_real_width_tendsto_zero (root : IntervalDyadic)
    (bits : InfiniteDyadicPath) :
    Filter.Tendsto
      (fun depth => (bits.cell root depth).hi.toReal -
        (bits.cell root depth).lo.toReal)
      Filter.atTop (nhds 0) := by
  apply (cell_width_tendsto_zero root bits).congr'
  exact Filter.Eventually.of_forall fun depth => by
    change ((bits.cell root depth).width.toRat : ℝ) =
      (bits.cell root depth).hi.toReal - (bits.cell root depth).lo.toReal
    rw [IntervalDyadic.width_toRat]
    simp only [Dyadic.toReal, Rat.cast_sub]

/-- Each closed cell is nonempty.
@isnad1 id=nonempty.0h3v.s3.81c14d7dfa2f from=translated src=- shape=ec1c07e4 vocab=dbffa8e6
-/
theorem cell_nonempty (root : IntervalDyadic) (bits : InfiniteDyadicPath)
    (depth : Nat) : (bits.cell root depth).toSet.Nonempty := by
  rw [IntervalDyadic.toSet, Set.nonempty_Icc]
  change ((bits.cell root depth).lo.toRat : ℝ) ≤
    ((bits.cell root depth).hi.toRat : ℝ)
  exact_mod_cast (bits.cell root depth).le

/-- The nested closed cells along an infinite path have a common point.
@isnad1 id=nonempty.0h2v.s4.aff0aeb218e3 from=translated src=- shape=8f211bde vocab=b77e43a3
-/
theorem intersection_nonempty (root : IntervalDyadic) (bits : InfiniteDyadicPath) :
    (⋂ depth, (bits.cell root depth).toSet).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
  · intro depth x hx
    exact mem_cell_of_mem_succ hx
  · exact cell_nonempty root bits
  · simpa [IntervalDyadic.toSet] using
      (isCompact_Icc : IsCompact (Set.Icc (root.lo : ℝ) root.hi))
  · intro depth
    exact isClosed_Icc

/-- The intersection of all cells on one path contains at most one point.
@isnad1 id=subsingl.0h2v.s4.ec972acc9fe9 from=translated src=- shape=8f211bde vocab=518818f3
-/
theorem intersection_subsingleton (root : IntervalDyadic) (bits : InfiniteDyadicPath) :
    (⋂ depth, (bits.cell root depth).toSet).Subsingleton := by
  intro x hx y hy
  have hdist : ∀ depth,
      dist x y ≤ ((bits.cell root depth).width.toRat : ℝ) := by
    intro depth
    have hxCell := Set.mem_iInter.mp hx depth
    have hyCell := Set.mem_iInter.mp hy depth
    have h := Real.dist_le_of_mem_Icc hxCell hyCell
    simpa [IntervalDyadic.toSet, IntervalDyadic.width_toRat, Dyadic.toReal] using h
  have hzero : dist x y ≤ 0 :=
    ge_of_tendsto' (cell_width_tendsto_zero root bits) hdist
  exact dist_eq_zero.mp (le_antisymm hzero dist_nonneg)

/-- Every infinite dyadic history denotes exactly one real point.
@isnad1 id=existsun.0h2v.s4.555ee446eec0 from=translated src=- shape=666057f4 vocab=1b6b2e74
-/
theorem exists_unique_limit (root : IntervalDyadic) (bits : InfiniteDyadicPath) :
    ∃! x : ℝ, ∀ depth, x ∈ bits.cell root depth := by
  obtain ⟨x, hx⟩ := intersection_nonempty root bits
  refine ⟨x, Set.mem_iInter.mp hx, ?_⟩
  intro y hy
  exact intersection_subsingleton root bits (Set.mem_iInter.mpr hy) hx

/-- The real point decoded by an infinite history. -/
noncomputable def decode (root : IntervalDyadic) (bits : InfiniteDyadicPath) : ℝ :=
  Classical.choose (exists_unique_limit root bits)

/-- The decoded point belongs to every finite prefix cell.
@isnad1 id=mem.0h3v.s4.5ae213178dd0 from=translated src=- shape=b7a23ecf vocab=451bda83
-/
theorem decode_mem_cell (root : IntervalDyadic) (bits : InfiniteDyadicPath)
    (depth : Nat) : bits.decode root ∈ bits.cell root depth :=
  (Classical.choose_spec (exists_unique_limit root bits)).1 depth

/-- Any choice of representatives from the nested cells converges to the point
decoded by the history.
@isnad1 id=tendsto.1h3v.s5.f136a25f43ee from=translated src=- shape=ec134218 vocab=8ada9008
-/
theorem tendsto_decode_of_mem_cell (root : IntervalDyadic) (bits : InfiniteDyadicPath)
    (points : Nat → ℝ) (hpoints : ∀ depth, points depth ∈ bits.cell root depth) :
    Filter.Tendsto points Filter.atTop (nhds (bits.decode root)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero
  · exact fun _ => dist_nonneg
  · intro depth
    have h := Real.dist_le_of_mem_Icc (hpoints depth) (decode_mem_cell root bits depth)
    simpa [IntervalDyadic.toSet, Dyadic.toReal] using h
  · exact cell_real_width_tendsto_zero root bits

end InfiniteDyadicPath

end LeanCert.Core
