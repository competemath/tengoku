/-
Copyright (c) 2026 Vladislav Galkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladislav Galkin
-/

import Tengoku.Roundedrootsums.RoundedRootSums.RationalShiftInversion
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact inversion for arbitrary positive real exponents

This file formalizes the exact lattice-point inversion formula
for rounded sums with an arbitrary positive real exponent
and a real shift in `[0, 1)`.
-/

namespace RoundedRootSums

/--
The real power `k^α` used in the arbitrary-exponent theory.-/
noncomputable def realShiftPower
    (α : ℝ)
    (k : Nat) : ℝ :=
  Real.rpow (k : ℝ) α

/--
The shifted rounded value

`⌊k^α + θ⌋`.-/
noncomputable def realShiftRoundedValue
    (α θ : ℝ)
    (k : Nat) : Nat :=
  ⌊realShiftPower α k + θ⌋₊

/--
The shifted rounded sum

`R_{α,θ}(n) = ∑_{k=1}^n ⌊k^α + θ⌋`.-/
noncomputable def realShiftRoundedSum
    (α θ : ℝ)
    (n : Nat) : Nat :=
  Finset.sum
    (Finset.Icc 1 n)
    (fun k =>
      realShiftRoundedValue α θ k)

/--
The maximal shifted level reached at `n`:

`M_{α,θ}(n) = ⌊n^α + θ⌋`.-/
noncomputable def realShiftMaxLevel
    (α θ : ℝ)
    (n : Nat) : Nat :=
  realShiftRoundedValue α θ n

/--
The dual ceiling threshold

`⌈(m - θ)^(1/α)⌉`.-/
noncomputable def realShiftDualCeil
    (α θ : ℝ)
    (m : Nat) : Nat :=
  ⌈Real.rpow
      ((m : ℝ) - θ)
      α⁻¹⌉₊

/--
The natural-number form of the exact inversion sum:

`∑_{m=1}^{M_{α,θ}(n)}
  (n + 1 - ⌈(m - θ)^(1/α)⌉)`.-/
noncomputable def realShiftInversionSum
    (α θ : ℝ)
    (n : Nat) : Nat :=
  Finset.sum
    (Finset.Icc
      1
      (realShiftMaxLevel α θ n))
    (fun m =>
      n + 1 -
        realShiftDualCeil α θ m)

/--
A finite incidence relation can be counted by first summing
over either coordinate.-/
theorem finiteIncidenceSum_comm
    {ι κ : Type*}
    (s : Finset ι)
    (t : Finset κ)
    (p : ι → κ → Prop) :
    Finset.sum s
        (fun i =>
          Finset.sum t
            (fun j =>
              @ite Nat
                (p i j)
                (Classical.propDecidable (p i j))
                1
                0)) =
      Finset.sum t
        (fun j =>
          Finset.sum s
            (fun i =>
              @ite Nat
                (p i j)
                (Classical.propDecidable (p i j))
                1
                0)) := by
  exact Finset.sum_comm

/--
The incidence indicator for the lattice point `(k, m)`.

It equals one precisely when the level `m` lies below the
shifted rounded value at `k`.-/
noncomputable def realShiftIncidence
    (α θ : ℝ)
    (k m : Nat) : Nat :=
  if m ≤ realShiftRoundedValue α θ k then
    1
  else
    0

/--
The number of admissible levels for a fixed index `k`,
with levels restricted by the maximal level at `n`.-/
noncomputable def realShiftRowCount
    (α θ : ℝ)
    (n k : Nat) : Nat :=
  Finset.sum
    (Finset.Icc
      1
      (realShiftMaxLevel α θ n))
    (fun m =>
      realShiftIncidence α θ k m)

/--
The number of indices `1 ≤ k ≤ n` whose shifted rounded
value reaches the level `m`.-/
noncomputable def realShiftLevelCount
    (α θ : ℝ)
    (n m : Nat) : Nat :=
  Finset.sum
    (Finset.Icc 1 n)
    (fun k =>
      realShiftIncidence α θ k m)

/--
Summing the incidence matrix first by levels or first by
indices gives the same total.-/
theorem realShiftRowSum_eq_levelSum
    (α θ : ℝ)
    (n : Nat) :
    Finset.sum
        (Finset.Icc 1 n)
        (fun k =>
          realShiftRowCount α θ n k) =
      Finset.sum
        (Finset.Icc
          1
          (realShiftMaxLevel α θ n))
        (fun m =>
          realShiftLevelCount α θ n m) := by
  unfold
    realShiftRowCount
    realShiftLevelCount
  exact Finset.sum_comm

/--
If `a ≤ B`, then exactly the integers `1, ..., a` in
`Icc 1 B` satisfy `m ≤ a`.-/
theorem sum_Icc_indicator_le
    (a B : Nat)
    (hAB : a ≤ B) :
    Finset.sum
        (Finset.Icc 1 B)
        (fun m =>
          if m ≤ a then (1 : Nat) else 0) =
      a := by
  classical
  rw [Finset.sum_boole]
  have hfilter :
      (Finset.Icc 1 B).filter
          (fun m => m ≤ a) =
        Finset.Icc 1 a := by
    ext m
    simp only [
      Finset.mem_filter,
      Finset.mem_Icc
    ]
    omega
  rw [hfilter]
  calc
    (Finset.Icc 1 a).card =
        a + 1 - 1 :=
      Nat.card_Icc 1 a
    _ = a :=
      Nat.add_sub_cancel_right a 1

/--
Provided that the rounded value at `k` does not exceed the
maximal level at `n`, the row count equals that rounded
value.-/
theorem realShiftRowCount_eq_roundedValue
    (α θ : ℝ)
    (n k : Nat)
    (hk :
      realShiftRoundedValue α θ k ≤
        realShiftMaxLevel α θ n) :
    realShiftRowCount α θ n k =
      realShiftRoundedValue α θ k := by
  unfold
    realShiftRowCount
    realShiftIncidence
  exact
    sum_Icc_indicator_le
      (realShiftRoundedValue α θ k)
      (realShiftMaxLevel α θ n)
      hk

/--
If every index in `1, ..., n` has rounded value at most the
rounded value at `n`, then the rounded sum equals the sum of
the level counts.-/
theorem realShiftRoundedSum_eq_levelSum_of_rowBound
    (α θ : ℝ)
    (n : Nat)
    (hrow :
      ∀ k ∈ Finset.Icc 1 n,
        realShiftRoundedValue α θ k ≤
          realShiftMaxLevel α θ n) :
    realShiftRoundedSum α θ n =
      Finset.sum
        (Finset.Icc
          1
          (realShiftMaxLevel α θ n))
        (fun m =>
          realShiftLevelCount α θ n m) := by
  rw [← realShiftRowSum_eq_levelSum]
  unfold realShiftRoundedSum
  apply Finset.sum_congr rfl
  intro k hk
  exact
    (realShiftRowCount_eq_roundedValue
      α θ n k
      (hrow k hk)).symm

/--
For a positive exponent, the real power is monotone on
natural-number arguments.-/
theorem realShiftPower_le_of_le
    (α : ℝ)
    (hα : 0 < α)
    (k n : Nat)
    (hkn : k ≤ n) :
    realShiftPower α k ≤
      realShiftPower α n := by
  unfold realShiftPower
  apply Real.rpow_le_rpow
  · exact_mod_cast
      (Nat.zero_le k)
  · exact_mod_cast hkn
  · exact hα.le

/--
For a positive exponent, the shifted rounded value is
monotone in its natural-number argument.-/
theorem realShiftRoundedValue_le_of_le
    (α θ : ℝ)
    (hα : 0 < α)
    (k n : Nat)
    (hkn : k ≤ n) :
    realShiftRoundedValue α θ k ≤
      realShiftRoundedValue α θ n := by
  unfold realShiftRoundedValue
  apply Nat.floor_le_floor
  gcongr
  exact
    realShiftPower_le_of_le
      α hα k n hkn

/--
For every positive real exponent, the shifted rounded sum
equals the sum of its finite level counts.-/
theorem realShiftRoundedSum_eq_levelSum
    (α θ : ℝ)
    (n : Nat)
    (hα : 0 < α) :
    realShiftRoundedSum α θ n =
      Finset.sum
        (Finset.Icc
          1
          (realShiftMaxLevel α θ n))
        (fun m =>
          realShiftLevelCount α θ n m) := by
  apply
    realShiftRoundedSum_eq_levelSum_of_rowBound
      α θ n
  intro k hk
  have hkn : k ≤ n :=
    (Finset.mem_Icc.mp hk).2
  simpa [realShiftMaxLevel] using
    realShiftRoundedValue_le_of_le
      α θ hα k n hkn

/--
For a positive natural level `m`, membership below the
rounded value is equivalent to the corresponding real
inequality.-/
theorem le_realShiftRoundedValue_iff
    (α θ : ℝ)
    (k m : Nat)
    (hm : 0 < m) :
    m ≤ realShiftRoundedValue α θ k ↔
      (m : ℝ) ≤ realShiftPower α k + θ := by
  unfold realShiftRoundedValue
  exact
    Nat.le_floor_iff'
      (Nat.ne_of_gt hm)

/--
For `α > 0`, the shifted level inequality is equivalent to
the corresponding inequality for the inverse power.-/
theorem realShiftLevelReal_iff_dualPower_le
    (α θ : ℝ)
    (k m : Nat)
    (hα : 0 < α)
    (hθ : θ < 1)
    (hm : 0 < m) :
    (m : ℝ) ≤ realShiftPower α k + θ ↔
      Real.rpow
          ((m : ℝ) - θ)
          α⁻¹ ≤
        (k : ℝ) := by
  have hmOneNat :
      1 ≤ m := by
    omega
  have hmOne :
      (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hmOneNat
  have hbase :
      0 ≤ (m : ℝ) - θ := by
    linarith
  have hkNonneg :
      0 ≤ (k : ℝ) := by
    positivity
  have hpowIff :
      Real.rpow
          ((m : ℝ) - θ)
          α⁻¹ ≤
        (k : ℝ) ↔
      (m : ℝ) - θ ≤
        Real.rpow (k : ℝ) α := by
    exact
      Real.rpow_inv_le_iff_of_pos
        hbase
        hkNonneg
        hα
  unfold realShiftPower
  constructor
  · intro h
    apply hpowIff.mpr
    linarith
  · intro h
    have hlevel :
        (m : ℝ) - θ ≤
          Real.rpow (k : ℝ) α :=
      hpowIff.mp h
    linarith

/--
For `α > 0`, `θ < 1`, and a positive level `m`, reaching
the rounded level `m` is equivalent to the dual ceiling
threshold being at most `k`.-/
theorem le_realShiftRoundedValue_iff_dualCeil_le
    (α θ : ℝ)
    (k m : Nat)
    (hα : 0 < α)
    (hθ : θ < 1)
    (hm : 0 < m) :
    m ≤ realShiftRoundedValue α θ k ↔
      realShiftDualCeil α θ m ≤ k := by
  calc
    m ≤ realShiftRoundedValue α θ k ↔
        (m : ℝ) ≤
          realShiftPower α k + θ :=
      le_realShiftRoundedValue_iff
        α θ k m hm
    _ ↔
        Real.rpow
            ((m : ℝ) - θ)
            α⁻¹ ≤
          (k : ℝ) :=
      realShiftLevelReal_iff_dualPower_le
        α θ k m hα hθ hm
    _ ↔
        realShiftDualCeil α θ m ≤ k := by
      unfold realShiftDualCeil
      symm
      exact Nat.ceil_le

/--
For every positive level `m` and every shift `θ < 1`, the
dual ceiling threshold is positive.-/
theorem realShiftDualCeil_pos
    (α θ : ℝ)
    (m : Nat)
    (hθ : θ < 1)
    (hm : 0 < m) :
    0 < realShiftDualCeil α θ m := by
  have hmOneNat :
      1 ≤ m := by
    omega
  have hmOne :
      (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hmOneNat
  have hbasePos :
      0 < (m : ℝ) - θ := by
    linarith
  unfold realShiftDualCeil
  rw [
    Nat.lt_iff_add_one_le,
    zero_add,
    Nat.one_le_ceil_iff
  ]
  exact
    Real.rpow_pos_of_pos
      hbasePos
      α⁻¹

/--
For a positive threshold `c`, the number of integers
`k ∈ Icc 1 n` satisfying `c ≤ k` is `n + 1 - c`.-/
theorem sum_Icc_indicator_ge
    (c n : Nat)
    (hc : 0 < c) :
    Finset.sum
        (Finset.Icc 1 n)
        (fun k =>
          if c ≤ k then (1 : Nat) else 0) =
      n + 1 - c := by
  classical
  have hcOne :
      1 ≤ c := by
    omega
  have hsumCard :
      Finset.sum
          (Finset.Icc 1 n)
          (fun k =>
            if c ≤ k then (1 : Nat) else 0) =
        ((Finset.Icc 1 n).filter
          (fun k => c ≤ k)).card := by
    induction (Finset.Icc 1 n) using Finset.induction_on with
    | empty =>
        simp
    | @insert a s ha ih =>
        by_cases hca : c ≤ a <;>
          simp_all
  have hfilter :
      (Finset.Icc 1 n).filter
          (fun k => c ≤ k) =
        Finset.Icc c n := by
    ext k
    simp only [
      Finset.mem_filter,
      Finset.mem_Icc
    ]
    omega
  calc
    Finset.sum
          (Finset.Icc 1 n)
          (fun k =>
            if c ≤ k then (1 : Nat) else 0) =
        ((Finset.Icc 1 n).filter
          (fun k => c ≤ k)).card :=
      hsumCard
    _ =
        (Finset.Icc c n).card := by
      rw [hfilter]
    _ =
        n + 1 - c :=
      Nat.card_Icc c n

/--
For every positive level `m`, the level count is the length
of the interval beginning at the dual ceiling threshold.-/
theorem realShiftLevelCount_eq
    (α θ : ℝ)
    (n m : Nat)
    (hα : 0 < α)
    (hθ : θ < 1)
    (hm : 0 < m) :
    realShiftLevelCount α θ n m =
      n + 1 -
        realShiftDualCeil α θ m := by
  have hdualPos :
      0 < realShiftDualCeil α θ m :=
    realShiftDualCeil_pos
      α θ m hθ hm
  unfold
    realShiftLevelCount
    realShiftIncidence
  calc
    Finset.sum
          (Finset.Icc 1 n)
          (fun k =>
            if m ≤ realShiftRoundedValue α θ k then
              (1 : Nat)
            else
              0) =
        Finset.sum
          (Finset.Icc 1 n)
          (fun k =>
            if realShiftDualCeil α θ m ≤ k then
              (1 : Nat)
            else
              0) := by
      apply Finset.sum_congr rfl
      intro k _hk
      have hiff :
          m ≤ realShiftRoundedValue α θ k ↔
            realShiftDualCeil α θ m ≤ k :=
        le_realShiftRoundedValue_iff_dualCeil_le
          α θ k m hα hθ hm
      by_cases hlevel :
          m ≤ realShiftRoundedValue α θ k
      · have hdual :
            realShiftDualCeil α θ m ≤ k :=
          hiff.mp hlevel
        simp [hlevel, hdual]
      · have hdual :
            ¬ realShiftDualCeil α θ m ≤ k := by
          intro h
          exact hlevel (hiff.mpr h)
        simp [hlevel, hdual]
    _ =
        n + 1 -
          realShiftDualCeil α θ m :=
      sum_Icc_indicator_ge
        (realShiftDualCeil α θ m)
        n
        hdualPos

/--
For a positive exponent and a shift below one, replacing
every level count by its explicit interval length gives the
inversion sum.-/
theorem realShiftLevelSum_eq_inversionSum
    (α θ : ℝ)
    (n : Nat)
    (hα : 0 < α)
    (hθ : θ < 1) :
    Finset.sum
        (Finset.Icc
          1
          (realShiftMaxLevel α θ n))
        (fun m =>
          realShiftLevelCount α θ n m) =
      realShiftInversionSum α θ n := by
  unfold realShiftInversionSum
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos :
      0 < m :=
    (Finset.mem_Icc.mp hm).1
  exact
    realShiftLevelCount_eq
      α θ n m hα hθ hmPos

/--
The shifted rounded sum equals its exact dual inversion sum
for every positive real exponent and every shift below one.-/
theorem realShiftRoundedSum_eq_inversionSum
    (α θ : ℝ)
    (n : Nat)
    (hα : 0 < α)
    (hθ : θ < 1) :
    realShiftRoundedSum α θ n =
      realShiftInversionSum α θ n := by
  calc
    realShiftRoundedSum α θ n =
        Finset.sum
          (Finset.Icc
            1
            (realShiftMaxLevel α θ n))
          (fun m =>
            realShiftLevelCount α θ n m) :=
      realShiftRoundedSum_eq_levelSum
        α θ n hα
    _ =
        realShiftInversionSum α θ n :=
      realShiftLevelSum_eq_inversionSum
        α θ n hα hθ

/--
Exact inversion for arbitrary positive real exponents.

For `α > 0` and `0 ≤ θ < 1`,

`∑_{k=1}^n ⌊k^α + θ⌋ =
  ∑_{m=1}^{⌊n^α + θ⌋}
    (n + 1 - ⌈(m - θ)^(1/α)⌉)`.-/
theorem realShiftExactInversion
    (α θ : ℝ)
    (n : Nat)
    (hα : 0 < α)
    (hθ : θ ∈ Set.Ico (0 : ℝ) 1) :
    Finset.sum
        (Finset.Icc 1 n)
        (fun k =>
          ⌊Real.rpow (k : ℝ) α + θ⌋₊) =
      Finset.sum
        (Finset.Icc
          1
          ⌊Real.rpow (n : ℝ) α + θ⌋₊)
        (fun m =>
          n + 1 -
            ⌈Real.rpow
                ((m : ℝ) - θ)
                α⁻¹⌉₊) := by
  simpa only [
    realShiftRoundedSum,
    realShiftRoundedValue,
    realShiftPower,
    realShiftInversionSum,
    realShiftMaxLevel,
    realShiftDualCeil
  ] using
    realShiftRoundedSum_eq_inversionSum
      α θ n hα hθ.2

/--
The floor power sum

`F_α(n) = ∑_{k=1}^n ⌊k^α⌋`.-/
noncomputable def realFloorPowerSum
    (α : ℝ)
    (n : Nat) : Nat :=
  Finset.sum
    (Finset.Icc 1 n)
    (fun k =>
      ⌊Real.rpow (k : ℝ) α⌋₊)

/--
The ceiling power sum

`C_α(n) = ∑_{k=1}^n ⌈k^α⌉`.-/
noncomputable def realCeilPowerSum
    (α : ℝ)
    (n : Nat) : Nat :=
  Finset.sum
    (Finset.Icc 1 n)
    (fun k =>
      ⌈Real.rpow (k : ℝ) α⌉₊)

/--
The reciprocal cutoff

`r = ⌊n^α⌋`.-/
noncomputable def realFloorPowerCutoff
    (α : ℝ)
    (n : Nat) : Nat :=
  ⌊Real.rpow (n : ℝ) α⌋₊

/--
The zero-shift specialization of exact inversion:

`F_α(n) =
  ∑_{m=1}^{⌊n^α⌋}
    (n + 1 - ⌈m^(1/α)⌉)`.-/
theorem realFloorPowerSum_eq_dualSum
    (α : ℝ)
    (n : Nat)
    (hα : 0 < α) :
    realFloorPowerSum α n =
      Finset.sum
        (Finset.Icc
          1
          (realFloorPowerCutoff α n))
        (fun m =>
          n + 1 -
            ⌈Real.rpow
                (m : ℝ)
                α⁻¹⌉₊) := by
  have hzero :
      (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
    constructor <;> norm_num
  simpa [
    realFloorPowerSum,
    realFloorPowerCutoff
  ] using
    realShiftExactInversion
      α 0 n hα hzero

/--
Every dual ceiling threshold occurring in the reciprocal
sum lies at most at `n`.-/
theorem realDualCeil_le_of_mem_cutoff
    (α : ℝ)
    (n m : Nat)
    (hα : 0 < α)
    (hm :
      m ∈ Finset.Icc
        1
        (realFloorPowerCutoff α n)) :
    ⌈Real.rpow
        (m : ℝ)
        α⁻¹⌉₊ ≤ n := by
  have hmPos :
      0 < m :=
    (Finset.mem_Icc.mp hm).1
  have hmUpper :
      m ≤ realFloorPowerCutoff α n :=
    (Finset.mem_Icc.mp hm).2
  have hlevel :
      m ≤ realShiftRoundedValue α 0 n := by
    simpa [
      realFloorPowerCutoff,
      realShiftRoundedValue,
      realShiftPower
    ] using hmUpper
  have hdual :
      realShiftDualCeil α 0 m ≤ n :=
    (le_realShiftRoundedValue_iff_dualCeil_le
      α 0 n m
      hα
      (by norm_num)
      hmPos).mp hlevel
  simpa [realShiftDualCeil] using hdual

/--
Each summand in the inversion formula, together with the
corresponding dual ceiling term, equals `n + 1`.-/
theorem realInversionTerm_add_dualCeil
    (α : ℝ)
    (n m : Nat)
    (hα : 0 < α)
    (hm :
      m ∈ Finset.Icc
        1
        (realFloorPowerCutoff α n)) :
    (n + 1 -
        ⌈Real.rpow
            (m : ℝ)
            α⁻¹⌉₊) +
      ⌈Real.rpow
          (m : ℝ)
          α⁻¹⌉₊ =
        n + 1 := by
  have hceil :
      ⌈Real.rpow
          (m : ℝ)
          α⁻¹⌉₊ ≤ n :=
    realDualCeil_le_of_mem_cutoff
      α n m hα hm
  apply Nat.sub_add_cancel
  omega

/--
The inversion sum plus the reciprocal ceiling sum equals
`(n + 1)` times the reciprocal cutoff.-/
theorem realDualInversionSum_add_ceilSum
    (α : ℝ)
    (n : Nat)
    (hα : 0 < α) :
    Finset.sum
        (Finset.Icc
          1
          (realFloorPowerCutoff α n))
        (fun m =>
          n + 1 -
            ⌈Real.rpow
                (m : ℝ)
                α⁻¹⌉₊) +
      realCeilPowerSum
        α⁻¹
        (realFloorPowerCutoff α n) =
      (n + 1) *
        realFloorPowerCutoff α n := by
  unfold realCeilPowerSum
  rw [← Finset.sum_add_distrib]
  calc
    Finset.sum
          (Finset.Icc
            1
            (realFloorPowerCutoff α n))
          (fun m =>
            (n + 1 -
                ⌈Real.rpow
                    (m : ℝ)
                    α⁻¹⌉₊) +
              ⌈Real.rpow
                  (m : ℝ)
                  α⁻¹⌉₊) =
        Finset.sum
          (Finset.Icc
            1
            (realFloorPowerCutoff α n))
          (fun _ => n + 1) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact
        realInversionTerm_add_dualCeil
          α n m hα hm
    _ =
        (n + 1) *
          realFloorPowerCutoff α n := by
      simp [Nat.card_Icc, Nat.mul_comm]

/--
Exact reciprocity for arbitrary positive real exponents.

If `r = ⌊n^α⌋`, then

`F_α(n) + C_(1/α)(r) = (n + 1) r`.-/
theorem realPowerReciprocity
    (α : ℝ)
    (n : Nat)
    (hα : 0 < α) :
    realFloorPowerSum α n +
      realCeilPowerSum
        α⁻¹
        (realFloorPowerCutoff α n) =
      (n + 1) *
        realFloorPowerCutoff α n := by
  rw [
    realFloorPowerSum_eq_dualSum
      α n hα
  ]
  exact
    realDualInversionSum_add_ceilSum
      α n hα

/--
Explicit form of the reciprocity law.

For every `α > 0`,

`∑_{k=1}^n ⌊k^α⌋ +
 ∑_{m=1}^{⌊n^α⌋} ⌈m^(1/α)⌉ =
 (n + 1) ⌊n^α⌋`.-/
theorem realPowerReciprocity_explicit
    (α : ℝ)
    (n : Nat)
    (hα : 0 < α) :
    Finset.sum
        (Finset.Icc 1 n)
        (fun k =>
          ⌊Real.rpow (k : ℝ) α⌋₊) +
      Finset.sum
        (Finset.Icc
          1
          ⌊Real.rpow (n : ℝ) α⌋₊)
        (fun m =>
          ⌈Real.rpow
              (m : ℝ)
              α⁻¹⌉₊) =
      (n + 1) *
        ⌊Real.rpow (n : ℝ) α⌋₊ := by
  simpa [
    realFloorPowerSum,
    realCeilPowerSum,
    realFloorPowerCutoff
  ] using
    realPowerReciprocity
      α n hα

/--
The complete arbitrary-real-exponent inversion result.

It packages together:

* exact shifted inversion for `0 ≤ θ < 1`;
* the zero-shift floor/ceiling reciprocity law.-/
theorem realShiftRealInversionMainTheorem
    (α θ : ℝ)
    (n : Nat)
    (hα : 0 < α)
    (hθ : θ ∈ Set.Ico (0 : ℝ) 1) :
    (Finset.sum
          (Finset.Icc 1 n)
          (fun k =>
            ⌊Real.rpow (k : ℝ) α + θ⌋₊) =
        Finset.sum
          (Finset.Icc
            1
            ⌊Real.rpow (n : ℝ) α + θ⌋₊)
          (fun m =>
            n + 1 -
              ⌈Real.rpow
                  ((m : ℝ) - θ)
                  α⁻¹⌉₊)) ∧
      (Finset.sum
            (Finset.Icc 1 n)
            (fun k =>
              ⌊Real.rpow (k : ℝ) α⌋₊) +
          Finset.sum
            (Finset.Icc
              1
              ⌊Real.rpow (n : ℝ) α⌋₊)
            (fun m =>
              ⌈Real.rpow
                  (m : ℝ)
                  α⁻¹⌉₊) =
        (n + 1) *
          ⌊Real.rpow (n : ℝ) α⌋₊) := by
  constructor
  · exact
      realShiftExactInversion
        α θ n hα hθ
  · exact
      realPowerReciprocity_explicit
        α n hα

end RoundedRootSums
