/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: Weaver (exploration and formalization); GPT-5.6 Sol (review).
-/
import Tengoku.Goemans.Goemans.Model
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Cost bookkeeping

Path-level cost identities (paper, "Cost bookkeeping", Section 3): with
`WZ i`/`WE i` the per-unit costs of the cheap/expensive path of terminal `i`,

* `ucost S = base + Σ_{i ∉ S} sav i`, and
* `fcost = base + Σ_i (dᵢ - fᵢ)(WEᵢ - WZᵢ)`,

where `base = Σᵢ dᵢ·WZᵢ` is the all-cheap cost and
`sav i = dᵢ·(WEᵢ - WZᵢ)` the (possibly negative) full-demand saving of
routing `i` cheap. Everything here is ring-level (no division).
-/

namespace Goemans

namespace FlowInstance

variable {K : Type*} [CommRing K] [LinearOrder K]
variable (I : FlowInstance K)

/-- Per-unit cost of the cheap path `Z i`.-/
def WZ (i : Terminal) : K := ∑ a, if onZ i a then I.c a else 0

/-- Per-unit cost of the expensive path `E i`.-/
def WE (i : Terminal) : K := ∑ a, if onE i a then I.c a else 0

theorem WZ_nonneg [IsStrictOrderedRing K] (i : Terminal) : 0 ≤ I.WZ i :=
  Finset.sum_nonneg fun a _ => by
    split_ifs
    · exact I.c_nonneg a
    · exact le_refl 0

theorem WE_nonneg [IsStrictOrderedRing K] (i : Terminal) : 0 ≤ I.WE i :=
  Finset.sum_nonneg fun a _ => by
    split_ifs
    · exact I.c_nonneg a
    · exact le_refl 0

/-- The all-cheap base cost `B = Σᵢ dᵢ·WZᵢ`.-/
def base : K := ∑ i, I.d i * I.WZ i

/-- Full-demand saving `sav i = dᵢ·(WEᵢ - WZᵢ)` (the paper's `hᵢ`; possibly
negative).-/
def sav (i : Terminal) : K := I.d i * (I.WE i - I.WZ i)

/-- `sav i ≥ -dᵢ·WZᵢ` (since the expensive path costs at least `0`).-/
theorem sav_lower [IsStrictOrderedRing K] (i : Terminal) :
    -(I.d i * I.WZ i) ≤ I.sav i := by
  have h : 0 ≤ I.d i * I.WE i := mul_nonneg (I.d_pos i).le (I.WE_nonneg i)
  rw [sav]
  nlinarith [h]

/-- Routing cost through path costs: `ucost S = Σᵢ dᵢ·(WZᵢ or WEᵢ)`.-/
theorem ucost_eq (S : Finset Terminal) :
    I.ucost S = ∑ i, I.d i * (if i ∈ S then I.WZ i else I.WE i) := by
  rw [ucost]
  simp_rw [load, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S
  · simp only [hi, ite_true, WZ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by split_ifs <;> ring
  · simp only [hi, ite_false, WE, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by split_ifs <;> ring

/-- Fractional cost through path costs: `fcost = Σᵢ (fᵢ·WZᵢ + (dᵢ-fᵢ)·WEᵢ)`.-/
theorem fcost_eq :
    I.fcost = ∑ i, (I.f i * I.WZ i + (I.d i - I.f i) * I.WE i) := by
  rw [fcost]
  simp_rw [x, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [WZ, WE, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs <;> ring

/-- `ucost S = base + Σ_{i ∉ S} sav i`.-/
theorem ucost_eq_base (S : Finset Terminal) :
    I.ucost S = I.base + ∑ i, (if i ∈ S then 0 else I.sav i) := by
  rw [ucost_eq, base, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sav]
  split_ifs <;> ring

/-- `fcost = base + Σᵢ (dᵢ - fᵢ)(WEᵢ - WZᵢ)`.-/
theorem fcost_eq_base :
    I.fcost = I.base + ∑ i, (I.d i - I.f i) * (I.WE i - I.WZ i) := by
  rw [fcost_eq, base, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end FlowInstance

end Goemans
