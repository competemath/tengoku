/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: Weaver (exploration and formalization); GPT-5.6 Sol (review).
-/
import Tengoku.Goemans.Goemans.Costs
import Tengoku.Goemans.Goemans.Optimization
import Tengoku.Goemans.Goemans.RhoStar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Concrete members of the Proposition 4.1 family: lower-bound records

Proposition 4.1 of the paper: for integers `a > b > a/2` and `M ≥ 1`, the
instance on `H*` with demands `d = (aM, bM, aM)`, splits
`f = ((a-b)M - 1, (2b-a)M, (a-b)M - 1)` and per-unit costs `(b, a, b)` on
`s→t₁, s→t₂, u→t₃` has fractional cost `(a² - ab + 2b²)M + 2b`, minimum
admissible unsplittable cost `2abM`, and ratio
`ρ = 2abM / ((a² - ab + 2b²)M + 2b) → R(b/a) → ρ* = 2/(2√2 - 1)` as
`b/a → 1/√2`, `M → ∞`.

This file `decide`-verifies two members, giving kernel-checked *lower-bound
records* for the extremal ratio `ρ(H*)`:

* `(a,b,M) = (17,12,1000)`: ratio `408000/373024 ≈ 1.09376`;
* `(a,b,M) = (577,408,10⁶)` (Pell convergent): ratio
  `470832000000/430441000816 ≈ 1.09383632`, within `2.1·10⁻⁹` of
  `ρ* ≈ 1.0938363213`.

The file also proves the general symbolic formulas and supplies the integral
family used by the exact limiting argument. It mirrors
`src/goemans_gap/revision_checks.py`, Part 1.
-/

namespace Goemans

open Arc

/-! ### The symbolic Proposition 4.1 family -/

/-- Parameters for the three-parameter lower-bound family.  The inequalities
say `0 < b < a < 2b`, `M > 0`, and ensure the two split coordinates
`(a-b)M-1` are nonnegative.-/
structure FamilyParams (K : Type*) [CommRing K] [LinearOrder K]
    [IsStrictOrderedRing K] where
  /-- The larger of the two Pell-style integer parameters.-/
  a : K
  /-- The smaller parameter, constrained by `a / 2 < b < a`.-/
  b : K
  /-- The positive scaling parameter.-/
  M : K
  b_pos : 0 < b
  b_lt_a : b < a
  a_lt_two_b : a < 2 * b
  M_pos : 0 < M
  gap : 1 ≤ (a - b) * M

namespace FamilyParams

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem sum_arc (g : Arc → K) :
    ∑ e, g e =
      g st1 + g st2 + g su + g ut3 + g uv + g vt1 + g vw + g wt2 + g wt3 := by
  rw [show (Finset.univ : Finset Arc) =
      {st1, st2, su, ut3, uv, vt1, vw, wt2, wt3} by decide]
  simp
  ring

/-- The Proposition 4.1 flow instance associated to `(a,b,M)`.-/
def flow (P : FamilyParams K) : FlowInstance K where
  d := ![P.a * P.M, P.b * P.M, P.a * P.M]
  f := ![(P.a - P.b) * P.M - 1, (2 * P.b - P.a) * P.M,
    (P.a - P.b) * P.M - 1]
  c e := match e with
    | st1 => P.b
    | st2 => P.a
    | ut3 => P.b
    | _ => 0
  d_pos := by
    intro i
    fin_cases i
    · exact mul_pos (lt_trans P.b_pos P.b_lt_a) P.M_pos
    · exact mul_pos P.b_pos P.M_pos
    · exact mul_pos (lt_trans P.b_pos P.b_lt_a) P.M_pos
  f_nonneg := by
    intro i
    fin_cases i
    · change 0 ≤ (P.a - P.b) * P.M - 1
      exact sub_nonneg.mpr P.gap
    · change 0 ≤ (2 * P.b - P.a) * P.M
      exact mul_nonneg (sub_nonneg.mpr P.a_lt_two_b.le) P.M_pos.le
    · change 0 ≤ (P.a - P.b) * P.M - 1
      exact sub_nonneg.mpr P.gap
  f_le_d := by
    intro i
    have ha : 0 < P.a := lt_trans P.b_pos P.b_lt_a
    have hbM : 0 < P.b * P.M := mul_pos P.b_pos P.M_pos
    have habM : 0 ≤ (P.a - P.b) * P.M :=
      mul_nonneg (sub_nonneg.mpr P.b_lt_a.le) P.M_pos.le
    fin_cases i <;> simp <;> nlinarith
  c_nonneg := by
    intro e
    cases e <;> simp [P.b_pos.le, (lt_trans P.b_pos P.b_lt_a).le]

@[simp] theorem flow_d_zero (P : FamilyParams K) :
    P.flow.d 0 = P.a * P.M := rfl

@[simp] theorem flow_d_one (P : FamilyParams K) :
    P.flow.d 1 = P.b * P.M := rfl

@[simp] theorem flow_d_two (P : FamilyParams K) :
    P.flow.d 2 = P.a * P.M := rfl

@[simp] theorem flow_f_zero (P : FamilyParams K) :
    P.flow.f 0 = (P.a - P.b) * P.M - 1 := rfl

@[simp] theorem flow_f_one (P : FamilyParams K) :
    P.flow.f 1 = (2 * P.b - P.a) * P.M := rfl

@[simp] theorem flow_f_two (P : FamilyParams K) :
    P.flow.f 2 = (P.a - P.b) * P.M - 1 := rfl

theorem flow_dmax (P : FamilyParams K) :
    P.flow.dmax = P.a * P.M := by
  have hba : P.b * P.M ≤ P.a * P.M :=
    mul_le_mul_of_nonneg_right P.b_lt_a.le P.M_pos.le
  change max (P.a * P.M) (max (P.b * P.M) (P.a * P.M)) = P.a * P.M
  rw [max_eq_right hba, max_self]

/-- The only admissible family routings are the empty routing and the three
singletons.-/
theorem flow_admissible_iff (P : FamilyParams ℝ) (S : Finset Terminal) :
    P.flow.Admissible S ↔ S.card ≤ 1 := by
  classical
  have h01 : ¬ P.flow.Admissible {0, 1} := by
    intro h
    rw [FlowInstance.admissible_iff, P.flow_dmax] at h
    have hfirst :
        P.a * P.M + P.b * P.M ≤
          ((P.a - P.b) * P.M - 1) + (2 * P.b - P.a) * P.M +
            P.a * P.M := by
      simpa [flow] using h.1
    nlinarith
  have h02 : ¬ P.flow.Admissible {0, 2} := by
    intro h
    rw [FlowInstance.admissible_iff, P.flow_dmax] at h
    have hmiddle :
        P.a * P.M + P.a * P.M ≤
          ((P.a - P.b) * P.M - 1) + (2 * P.b - P.a) * P.M +
            ((P.a - P.b) * P.M - 1) + P.a * P.M := by
      simpa [flow] using h.2.1
    nlinarith
  have h12 : ¬ P.flow.Admissible {1, 2} := by
    intro h
    rw [FlowInstance.admissible_iff, P.flow_dmax] at h
    have hthird :
        P.b * P.M + P.a * P.M ≤
          (2 * P.b - P.a) * P.M + ((P.a - P.b) * P.M - 1) +
            P.a * P.M := by
      simpa [flow] using h.2.2
    nlinarith
  constructor
  · intro hS
    by_contra hcard
    fin_cases S <;> simp at hcard
    · exact h01 hS
    · exact h02 hS
    · exact h12 hS
    · exact h01 (P.flow.admissible_mono (by decide) hS)
  · intro hcard
    obtain ⟨i, hi⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard
    exact P.flow.admissible_mono hi (P.flow.admissible_singleton i)

@[simp] theorem flow_WZ (P : FamilyParams K) (i : Terminal) :
    P.flow.WZ i = 0 := by
  fin_cases i <;> rw [FlowInstance.WZ, sum_arc] <;> simp [flow, onZ]

@[simp] theorem flow_WE_zero (P : FamilyParams K) :
    P.flow.WE 0 = P.b := by
  rw [FlowInstance.WE, sum_arc]
  simp [flow, onE]

@[simp] theorem flow_WE_one (P : FamilyParams K) :
    P.flow.WE 1 = P.a := by
  rw [FlowInstance.WE, sum_arc]
  simp [flow, onE]

@[simp] theorem flow_WE_two (P : FamilyParams K) :
    P.flow.WE 2 = P.b := by
  rw [FlowInstance.WE, sum_arc]
  simp [flow, onE]

/-- Closed form for the fractional cost of a family member.-/
theorem flow_fcost (P : FamilyParams K) :
    P.flow.fcost =
      (P.a ^ 2 - P.a * P.b + 2 * P.b ^ 2) * P.M + 2 * P.b := by
  rw [FlowInstance.fcost_eq, Fin.sum_univ_three]
  simp
  ring

/-- Closed form for the cost of any routing in the family.-/
theorem flow_ucost (P : FamilyParams K) (S : Finset Terminal) :
    P.flow.ucost S =
      (if 0 ∈ S then 0 else P.a * P.b * P.M) +
      (if 1 ∈ S then 0 else P.a * P.b * P.M) +
      (if 2 ∈ S then 0 else P.a * P.b * P.M) := by
  rw [FlowInstance.ucost_eq, Fin.sum_univ_three]
  simp
  split_ifs <;> ring

theorem flow_fcost_pos (P : FamilyParams ℝ) : 0 < P.flow.fcost := by
  rw [P.flow_fcost]
  have ha : 0 < P.a := lt_trans P.b_pos P.b_lt_a
  have hab : 0 < P.a - P.b := sub_pos.mpr P.b_lt_a
  have hcoef : 0 < P.a * (P.a - P.b) + 2 * P.b ^ 2 := by positivity
  have hrewrite :
      P.a ^ 2 - P.a * P.b + 2 * P.b ^ 2 =
        P.a * (P.a - P.b) + 2 * P.b ^ 2 := by ring
  rw [hrewrite]
  exact add_pos (mul_pos hcoef P.M_pos) (mul_pos (by norm_num) P.b_pos)

theorem flow_ucost_lower (P : FamilyParams ℝ) (S : Finset Terminal)
    (hS : P.flow.Admissible S) :
    2 * P.a * P.b * P.M ≤ P.flow.ucost S := by
  rw [P.flow_admissible_iff] at hS
  rw [P.flow_ucost]
  have hq : 0 ≤ P.a * P.b * P.M :=
    mul_nonneg (mul_nonneg (lt_trans P.b_pos P.b_lt_a).le P.b_pos.le) P.M_pos.le
  fin_cases S <;> simp at hS ⊢ <;> nlinarith

theorem flow_ucost_attained (P : FamilyParams ℝ) :
    P.flow.Admissible {2} ∧ P.flow.ucost {2} = 2 * P.a * P.b * P.M := by
  constructor
  · rw [P.flow_admissible_iff]
    simp
  · rw [P.flow_ucost]
    simp
    ring

/-- Every family member has exact optimum `2abM`.-/
theorem flow_optimalUCost (P : FamilyParams ℝ) :
    P.flow.optimalUCost = 2 * P.a * P.b * P.M := by
  apply le_antisymm
  · exact (P.flow.optimalUCost_le P.flow_ucost_attained.1).trans_eq
      P.flow_ucost_attained.2
  · exact P.flow.le_optimalUCost P.flow_ucost_lower

/-- Exact ratio formula for the symbolic family.-/
theorem flow_ratio (P : FamilyParams ℝ) :
    P.flow.optimalUCost / P.flow.fcost =
      (2 * P.a * P.b * P.M) /
        ((P.a ^ 2 - P.a * P.b + 2 * P.b ^ 2) * P.M + 2 * P.b) := by
  rw [P.flow_optimalUCost, P.flow_fcost]

/-- A symbolic family member in the positive-cost ratio space.-/
noncomputable def positiveFlow (P : FamilyParams ℝ) : PositiveCostInstance :=
  ⟨P.flow, P.flow_fcost_pos⟩

@[simp] theorem positiveFlow_ratio (P : FamilyParams ℝ) :
    P.positiveFlow.ratio =
      (2 * P.a * P.b * P.M) /
        ((P.a ^ 2 - P.a * P.b + 2 * P.b ^ 2) * P.M + 2 * P.b) :=
  P.flow_ratio

/-- Integral parameters automatically satisfy the unit-gap condition once
`a>b` and `M>0`.-/
def ofInt (a b M : ℤ) (hb : 0 < b) (hba : b < a) (hab : a < 2 * b)
    (hM : 0 < M) : FamilyParams ℤ where
  a := a
  b := b
  M := M
  b_pos := hb
  b_lt_a := hba
  a_lt_two_b := hab
  M_pos := hM
  gap := by
    have hprod : 0 < (a - b) * M := mul_pos (sub_pos.mpr hba) hM
    omega

@[simp] theorem ofInt_a (a b M : ℤ) (hb hba hab hM) :
    (ofInt a b M hb hba hab hM).a = a := rfl

@[simp] theorem ofInt_b (a b M : ℤ) (hb hba hab hM) :
    (ofInt a b M hb hba hab hM).b = b := rfl

@[simp] theorem ofInt_M (a b M : ℤ) (hb hba hab hM) :
    (ofInt a b M hb hba hab hM).M = M := rfl

/-- Cast integral family parameters to real parameters.-/
noncomputable def toReal (P : FamilyParams ℤ) : FamilyParams ℝ where
  a := P.a
  b := P.b
  M := P.M
  b_pos := by exact_mod_cast P.b_pos
  b_lt_a := by exact_mod_cast P.b_lt_a
  a_lt_two_b := by exact_mod_cast P.a_lt_two_b
  M_pos := by exact_mod_cast P.M_pos
  gap := by exact_mod_cast P.gap

/-- Building the family commutes with the integer-to-real model bridge.-/
theorem flow_toReal (P : FamilyParams ℤ) :
    P.flow.toReal = P.toReal.flow := by
  rw [FlowInstance.mk.injEq]
  refine ⟨funext ?_, funext ?_, funext ?_⟩
  · intro i
    fin_cases i <;> simp [flow, toReal]
  · intro i
    fin_cases i <;> simp [flow, toReal]
  · intro e
    cases e <;> simp [flow, toReal]

end FamilyParams

/-- The Proposition 4.1 instance with `(a, b, M) = (17, 12, 1000)`:
`d = (17000, 12000, 17000)`, `f = (4999, 7000, 4999)`, costs `(12, 17, 12)`.-/
def family17x12 : FlowInstance ℤ where
  d := ![17000, 12000, 17000]
  f := ![4999, 7000, 4999]
  c a := match a with
    | st1 => 12
    | st2 => 17
    | ut3 => 12
    | _ => 0
  d_pos := by decide
  f_nonneg := by decide
  f_le_d := by decide
  c_nonneg := by decide

/-- The `(17,12,1000)` member: fractional cost `373024`, admissible routings
are exactly `∅` and singletons, minimum admissible cost `408000`;
ratio `408000/373024 ≈ 1.09376`.-/
theorem family17_12_verified :
    family17x12.fcost = 373024 ∧
      (∀ S : Finset Terminal, family17x12.Admissible S ↔ S.card ≤ 1) ∧
      (∀ S : Finset Terminal, family17x12.Admissible S →
        408000 ≤ family17x12.ucost S) ∧
      family17x12.Admissible {2} ∧ family17x12.ucost {2} = 408000 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The Proposition 4.1 instance with `(a, b, M) = (577, 408, 10⁶)`, the Pell
convergent `408/577 ≈ 1/√2`:
`d = (577·10⁶, 408·10⁶, 577·10⁶)`, `f = (169·10⁶ - 1, 239·10⁶, 169·10⁶ - 1)`,
costs `(408, 577, 408)`.-/
def family577x408 : FlowInstance ℤ where
  d := ![577000000, 408000000, 577000000]
  f := ![168999999, 239000000, 168999999]
  c a := match a with
    | st1 => 408
    | st2 => 577
    | ut3 => 408
    | _ => 0
  d_pos := by decide
  f_nonneg := by decide
  f_le_d := by decide
  c_nonneg := by decide

/-- The Pell member `(577, 408, 10⁶)`: ratio
`470832000000 / 430441000816 = 1.09383632087… > 1.0938363`, within `2.1·10⁻⁹`
of `ρ* = 1.09383632135…`. Kernel-checked record: `ρ(H*) > 1.0938363`.-/
theorem family577_408_verified :
    family577x408.fcost = 430441000816 ∧
      (∀ S : Finset Terminal, family577x408.Admissible S →
        470832000000 ≤ family577x408.ucost S) ∧
      family577x408.Admissible {2} ∧
      family577x408.ucost {2} = 470832000000 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Lower-bound record extracted from the Pell member: there is an instance
whose every admissible routing costs more than `1.0938363 = 10938363/10⁷`
times the fractional cost (compare `ρ* ≈ 1.0938363213`, Theorem A).-/
theorem ratio_record :
    ∃ I : FlowInstance ℤ, 0 < I.fcost ∧
      ∀ S : Finset Terminal, I.Admissible S →
        10938363 * I.fcost < 10000000 * I.ucost S :=
  ⟨family577x408, by decide, by decide⟩

end Goemans
