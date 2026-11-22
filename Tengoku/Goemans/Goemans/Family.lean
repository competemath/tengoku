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

/--
@isnad1 id=eq.0h2v.s6.001cfbef157e from=translated src=- shape=6c0b2884 vocab=56b1b5f7
-/
@[simp] theorem flow_d_zero (P : FamilyParams K) :
    P.flow.d 0 = P.a * P.M := rfl

/--
@isnad1 id=eq.0h2v.s6.96972d1c45af from=translated src=- shape=6c0b2884 vocab=289e85c3
-/
@[simp] theorem flow_d_one (P : FamilyParams K) :
    P.flow.d 1 = P.b * P.M := rfl

/--
@isnad1 id=eq.0h2v.s6.ff465f5a477a from=translated src=- shape=6c0b2884 vocab=56b1b5f7
-/
@[simp] theorem flow_d_two (P : FamilyParams K) :
    P.flow.d 2 = P.a * P.M := rfl

/--
@isnad1 id=eq.0h2v.s7.0a1a085d6f79 from=translated src=- shape=835ce18d vocab=f4ea2cc6
-/
@[simp] theorem flow_f_zero (P : FamilyParams K) :
    P.flow.f 0 = (P.a - P.b) * P.M - 1 := rfl

/--
@isnad1 id=eq.0h2v.s7.5fa188a77cc0 from=translated src=- shape=7a9b8d92 vocab=f4ea2cc6
-/
@[simp] theorem flow_f_one (P : FamilyParams K) :
    P.flow.f 1 = (2 * P.b - P.a) * P.M := rfl

/--
@isnad1 id=eq.0h2v.s7.71342b8f6fb9 from=translated src=- shape=835ce18d vocab=f4ea2cc6
-/
@[simp] theorem flow_f_two (P : FamilyParams K) :
    P.flow.f 2 = (P.a - P.b) * P.M - 1 := rfl

/--
@isnad1 id=eq.0h2v.s6.2be69dcd9f0f from=translated src=- shape=46bdd8c6 vocab=170d7e5d
-/
theorem flow_dmax (P : FamilyParams K) :
    P.flow.dmax = P.a * P.M := by
  have hba : P.b * P.M ≤ P.a * P.M :=
    mul_le_mul_of_nonneg_right P.b_lt_a.le P.M_pos.le
  change max (P.a * P.M) (max (P.b * P.M) (P.a * P.M)) = P.a * P.M
  rw [max_eq_right hba, max_self]

/-- The only admissible family routings are the empty routing and the three
singletons.
@isnad1 id=iff.0h2v.s5.a6d582d48968 from=translated src=- shape=3a611f7b vocab=cc3a505b
-/
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

/--
@isnad1 id=eq.0h3v.s5.89f5657925a9 from=translated src=- shape=815dc88d vocab=511d0059
-/
@[simp] theorem flow_WZ (P : FamilyParams K) (i : Terminal) :
    P.flow.WZ i = 0 := by
  fin_cases i <;> rw [FlowInstance.WZ, sum_arc] <;> simp [flow, onZ]

/--
@isnad1 id=eq.0h2v.s5.2bc7ed6b8eb3 from=translated src=- shape=89ca3c07 vocab=3ebf23b0
-/
@[simp] theorem flow_WE_zero (P : FamilyParams K) :
    P.flow.WE 0 = P.b := by
  rw [FlowInstance.WE, sum_arc]
  simp [flow, onE]

/--
@isnad1 id=eq.0h2v.s5.b578f702091a from=translated src=- shape=89ca3c07 vocab=3ca0ce6b
-/
@[simp] theorem flow_WE_one (P : FamilyParams K) :
    P.flow.WE 1 = P.a := by
  rw [FlowInstance.WE, sum_arc]
  simp [flow, onE]

/--
@isnad1 id=eq.0h2v.s5.0b131332cca9 from=translated src=- shape=89ca3c07 vocab=3ebf23b0
-/
@[simp] theorem flow_WE_two (P : FamilyParams K) :
    P.flow.WE 2 = P.b := by
  rw [FlowInstance.WE, sum_arc]
  simp [flow, onE]

/-- Closed form for the fractional cost of a family member.
@isnad1 id=eq.0h2v.s8.deb062cb2838 from=translated src=- shape=1046dae2 vocab=08ca5176
-/
theorem flow_fcost (P : FamilyParams K) :
    P.flow.fcost =
      (P.a ^ 2 - P.a * P.b + 2 * P.b ^ 2) * P.M + 2 * P.b := by
  rw [FlowInstance.fcost_eq, Fin.sum_univ_three]
  simp
  ring

/-- Closed form for the cost of any routing in the family.
@isnad1 id=eq.0h3v.s8.470dfa96cb9d from=translated src=- shape=91e294cd vocab=e159ff07
-/
theorem flow_ucost (P : FamilyParams K) (S : Finset Terminal) :
    P.flow.ucost S =
      (if 0 ∈ S then 0 else P.a * P.b * P.M) +
      (if 1 ∈ S then 0 else P.a * P.b * P.M) +
      (if 2 ∈ S then 0 else P.a * P.b * P.M) := by
  rw [FlowInstance.ucost_eq, Fin.sum_univ_three]
  simp
  split_ifs <;> ring

/--
@isnad1 id=lt.0h1v.s4.0cb28c119677 from=translated src=- shape=2a42b25f vocab=9d6e6c7a
-/
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

/--
@isnad1 id=le.1h2v.s6.8d49db634401 from=translated src=- shape=5dbf3086 vocab=2ff64d51
-/
theorem flow_ucost_lower (P : FamilyParams ℝ) (S : Finset Terminal)
    (hS : P.flow.Admissible S) :
    2 * P.a * P.b * P.M ≤ P.flow.ucost S := by
  rw [P.flow_admissible_iff] at hS
  rw [P.flow_ucost]
  have hq : 0 ≤ P.a * P.b * P.M :=
    mul_nonneg (mul_nonneg (lt_trans P.b_pos P.b_lt_a).le P.b_pos.le) P.M_pos.le
  fin_cases S <;> simp at hS ⊢ <;> nlinarith

/--
@isnad1 id=and.0h1v.s6.5e7aab7c8935 from=translated src=- shape=650311fd vocab=a3ad8b09
-/
theorem flow_ucost_attained (P : FamilyParams ℝ) :
    P.flow.Admissible {2} ∧ P.flow.ucost {2} = 2 * P.a * P.b * P.M := by
  constructor
  · rw [P.flow_admissible_iff]
    simp
  · rw [P.flow_ucost]
    simp
    ring

/-- Every family member has exact optimum `2abM`.
@isnad1 id=eq.0h1v.s5.07d35a423c54 from=translated src=- shape=9e00919c vocab=7b782d7a
-/
theorem flow_optimalUCost (P : FamilyParams ℝ) :
    P.flow.optimalUCost = 2 * P.a * P.b * P.M := by
  apply le_antisymm
  · exact (P.flow.optimalUCost_le P.flow_ucost_attained.1).trans_eq
      P.flow_ucost_attained.2
  · exact P.flow.le_optimalUCost P.flow_ucost_lower

/-- Exact ratio formula for the symbolic family.
@isnad1 id=eq.0h1v.s7.f300876483bc from=translated src=- shape=b8b8955f vocab=9ccf0c56
-/
theorem flow_ratio (P : FamilyParams ℝ) :
    P.flow.optimalUCost / P.flow.fcost =
      (2 * P.a * P.b * P.M) /
        ((P.a ^ 2 - P.a * P.b + 2 * P.b ^ 2) * P.M + 2 * P.b) := by
  rw [P.flow_optimalUCost, P.flow_fcost]

/-- A symbolic family member in the positive-cost ratio space.-/
noncomputable def positiveFlow (P : FamilyParams ℝ) : PositiveCostInstance :=
  ⟨P.flow, P.flow_fcost_pos⟩

/--
@isnad1 id=eq.0h1v.s7.5f7ef96650a6 from=translated src=- shape=bb187424 vocab=056e872a
-/
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

/--
@isnad1 id=eq.4h3v.s6.2a51efb861bf from=translated src=- shape=26e0dfb4 vocab=008c7069
-/
@[simp] theorem ofInt_a (a b M : ℤ) (hb hba hab hM) :
    (ofInt a b M hb hba hab hM).a = a := rfl

/--
@isnad1 id=eq.4h3v.s6.df536856ef6a from=translated src=- shape=ac4d191b vocab=c3c2a003
-/
@[simp] theorem ofInt_b (a b M : ℤ) (hb hba hab hM) :
    (ofInt a b M hb hba hab hM).b = b := rfl

/--
@isnad1 id=eq.4h3v.s6.cc3929be352f from=translated src=- shape=6d89db53 vocab=db06fde4
-/
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

/-- Building the family commutes with the integer-to-real model bridge.
@isnad1 id=eq.0h1v.s4.1e47e8655ee7 from=translated src=- shape=c841f62f vocab=39a3a2c0
-/
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
ratio `408000/373024 ≈ 1.09376`.
@isnad1 id=and.0h0v.s6.28d23471175f from=translated src=- shape=9800fc1f vocab=a545ea52
-/
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
of `ρ* = 1.09383632135…`. Kernel-checked record: `ρ(H*) > 1.0938363`.
@isnad1 id=and.0h0v.s6.1dfe93b05fef from=translated src=- shape=1fe42a12 vocab=99184a87
-/
theorem family577_408_verified :
    family577x408.fcost = 430441000816 ∧
      (∀ S : Finset Terminal, family577x408.Admissible S →
        470832000000 ≤ family577x408.ucost S) ∧
      family577x408.Admissible {2} ∧
      family577x408.ucost {2} = 470832000000 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Lower-bound record extracted from the Pell member: there is an instance
whose every admissible routing costs more than `1.0938363 = 10938363/10⁷`
times the fractional cost (compare `ρ* ≈ 1.0938363213`, Theorem A).
@isnad1 id=ex.0h0v.s6.f476e88e3c85 from=translated src=- shape=5cb5f1b1 vocab=9e915b3b
-/
theorem ratio_record :
    ∃ I : FlowInstance ℤ, 0 < I.fcost ∧
      ∀ S : Finset Terminal, I.Admissible S →
        10938363 * I.fcost < 10000000 * I.ucost S :=
  ⟨family577x408, by decide, by decide⟩

end Goemans
