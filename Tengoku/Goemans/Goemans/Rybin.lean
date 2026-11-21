/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: Weaver (exploration and formalization); GPT-5.6 Sol (review).
-/
import Tengoku.Goemans.Goemans.Optimization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Rybin's counterexample: Goemans's cost conjecture is false

D. Rybin's instance of July 22, 2026 on the digraph `H*`:
demands `d = (15, 10, 15)`, splits `f = (5, 4, 5)`, per-unit costs
`2, 3, 2` on `s→t₁`, `s→t₂`, `u→t₃` and `0` elsewhere.

* the fractional flow costs `58`;
* every admissible unsplittable routing (`y_a ≤ x_a + D`) costs at least `60`,
  and `60` is attained (route `t₃` cheap, `t₁, t₂` expensive);
* hence **no** unsplittable flow within the Dinitz–Garg–Goemans capacity bound
  matches the fractional cost: Goemans's cost conjecture is false, with
  ratio `60/58 = 30/29 ≈ 1.0345`.

All statements are checked by `decide` — kernel-verified exhaustive
enumeration of the `2³ = 8` routings in exact integer arithmetic (the
instance is integral, so `ℤ` carries it faithfully; the generic model also
instantiates it over `ℚ` and `ℝ`). Mirrors `src/goemans_gap/verify_goemans.py`.
-/

namespace Goemans

open Arc

/-- Rybin's instance (July 22, 2026): `d = (15,10,15)`, `f = (5,4,5)`,
per-unit costs `2, 3, 2` on `s→t₁`, `s→t₂`, `u→t₃`, zero elsewhere.-/
def rybin : FlowInstance ℤ where
  d := ![15, 10, 15]
  f := ![5, 4, 5]
  c a := match a with
    | st1 => 2
    | st2 => 3
    | ut3 => 2
    | _ => 0
  d_pos := by decide
  f_nonneg := by decide
  f_le_d := by decide
  c_nonneg := by decide

/-- The fractional flow costs 58.-/
theorem rybin_fcost : rybin.fcost = 58 := by decide

/-- The admissible routings are exactly `∅` and the three singletons.-/
theorem rybin_admissible_iff :
    ∀ S : Finset Terminal, rybin.Admissible S ↔ S.card ≤ 1 := by decide

/-- Every admissible unsplittable routing costs at least 60.-/
theorem rybin_min : ∀ S : Finset Terminal, rybin.Admissible S → 60 ≤ rybin.ucost S := by
  decide

/-- Cost 60 is attained: route `t₃` on its cheap path, `t₁, t₂` expensive.-/
theorem rybin_min_attained :
    rybin.Admissible {2} ∧ rybin.ucost {2} = 60 := by decide

/-- **Goemans's cost conjecture is false** (Rybin, July 22, 2026):
there is an instance on `H*` in which *every* unsplittable flow obeying the
capacity bound `y_a ≤ x_a + d_max` costs strictly more than the fractional
flow.-/
theorem cost_conjecture_false :
    ∃ I : FlowInstance ℤ, ∀ S : Finset Terminal,
      I.Admissible S → I.fcost < I.ucost S :=
  ⟨rybin, by decide⟩

/-- Quantitative form (division-free): on Rybin's instance the optimum
admissible unsplittable cost is exactly `30/29` times the fractional cost:
`30·fcost ≤ 29·ucost S` for every admissible `S`, with equality attained.-/
theorem rybin_ratio :
    (0 < rybin.fcost ∧
      ∀ S : Finset Terminal, rybin.Admissible S →
        30 * rybin.fcost ≤ 29 * rybin.ucost S) ∧
      ∃ S : Finset Terminal, rybin.Admissible S ∧
        29 * rybin.ucost S = 30 * rybin.fcost := by
  refine ⟨⟨by decide, by decide⟩, {2}, by decide⟩

/-! ### The same counterexample in the real optimization problem -/

/-- Rybin's integral instance embedded in the real-valued model.-/
noncomputable def rybinReal : FlowInstance ℝ := rybin.toReal

@[simp] theorem rybinReal_fcost : rybinReal.fcost = 58 := by
  simp [rybinReal, rybin_fcost]

theorem rybinReal_admissible_iff (S : Finset Terminal) :
    rybinReal.Admissible S ↔ S.card ≤ 1 := by
  simpa [rybinReal] using rybin_admissible_iff S

theorem rybinReal_min (S : Finset Terminal) (hS : rybinReal.Admissible S) :
    60 ≤ rybinReal.ucost S := by
  have hSint : rybin.Admissible S := by simpa [rybinReal] using hS
  have hcost : (60 : ℝ) ≤ (rybin.ucost S : ℝ) := by
    exact_mod_cast rybin_min S hSint
  simpa [rybinReal] using hcost

theorem rybinReal_min_attained :
    rybinReal.Admissible {2} ∧ rybinReal.ucost {2} = 60 := by
  constructor
  · simpa [rybinReal] using rybin_min_attained.1
  · have hcost : (rybin.ucost {2} : ℝ) = 60 := by
      exact_mod_cast rybin_min_attained.2
    simpa [rybinReal] using hcost

/-- The optimal admissible cost of Rybin's real instance is exactly `60`.-/
theorem rybinReal_optimalUCost : rybinReal.optimalUCost = 60 := by
  apply le_antisymm
  · exact rybinReal.optimalUCost_le rybinReal_min_attained.1 |>.trans_eq
      rybinReal_min_attained.2
  · exact rybinReal.le_optimalUCost rybinReal_min

/-- The exact optimum-to-fractional-cost ratio of Rybin's instance.-/
theorem rybinReal_ratio :
    rybinReal.optimalUCost / rybinReal.fcost = (30 : ℝ) / 29 := by
  rw [rybinReal_optimalUCost, rybinReal_fcost]
  norm_num

/-- Rybin's instance as an element of the positive-cost parameter space.-/
noncomputable def rybinPositive : PositiveCostInstance :=
  ⟨rybinReal, by rw [rybinReal_fcost]; norm_num⟩

@[simp] theorem rybinPositive_ratio :
    rybinPositive.ratio = (30 : ℝ) / 29 := by
  exact rybinReal_ratio

/-- Real-valued formulation of Rybin's counterexample.-/
theorem cost_conjecture_false_real :
    ∃ I : FlowInstance ℝ, 0 < I.fcost ∧ ∀ S : Finset Terminal,
      I.Admissible S → I.fcost < I.ucost S := by
  refine ⟨rybinReal, by rw [rybinReal_fcost]; norm_num, ?_⟩
  intro S hS
  rw [rybinReal_fcost]
  linarith [rybinReal_min S hS]

end Goemans
