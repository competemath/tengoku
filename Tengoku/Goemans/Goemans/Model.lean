/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: Weaver (exploration and formalization); GPT-5.6 Sol (review).

Formalization of the paper "How Far Can Goemans's Cost Conjecture Fail?"
(July 2026). This file contains the model used in Section 2.
-/
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Algebra.Order.Ring.Defs
import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# The Rybin digraph `H*` and its SSUF path/routing model

A single-source unsplittable flow (SSUF) instance on the Rybin digraph `H*`
(vertices `s, u, v, w, t₁, t₂, t₃`, nine arcs). Each terminal `tᵢ` has exactly
two `s → tᵢ` paths (proved from the arc endpoint structure in
`Goemans.Digraph`, `walk_s_terminal_iff`; independently re-enumerated by
`src/goemans_gap/verify_goemans.py`):

* `E₁ = s→t₁`,      `Z₁ = s→u→v→t₁`
* `E₂ = s→t₂`,      `Z₂ = s→u→v→w→t₂`
* `E₃ = s→u→t₃`,    `Z₃ = s→u→v→w→t₃`

Hence a fractional flow is determined by demands `d` and cheap-path splits `f`
(`f i` routed on `Z i`, the rest on `E i`), and an unsplittable flow is a set
`S ⊆ {0,1,2}` of terminals routed on their `Z`-path. That the parametrization
loses nothing is itself proved: `Goemans.FlowDecomposition` shows every
conservation-law commodity flow splits this way
(`IsCommodityFlow.exists_split`), and `Goemans.GraphTheoremA` restates
Theorem A over the unparametrized instance space (`theoremA_graph`).

Admissibility is the Dinitz–Garg–Goemans capacity bound `y_a ≤ x_a + D` on
every arc, where `D = max_i d_i`.

The definitions are generic over a linearly ordered commutative ring `K`:
instantiated at `ℚ` everything is decidable (`decide`-checkable), and at `ℝ`
we prove Theorem A.
-/

namespace Goemans

/-- The nine arcs of the Rybin digraph `H*`.-/
inductive Arc : Type
  | st1  -- s → t₁
  | st2  -- s → t₂
  | su   -- s → u
  | ut3  -- u → t₃
  | uv   -- u → v
  | vt1  -- v → t₁
  | vw   -- v → w
  | wt2  -- w → t₂
  | wt3  -- w → t₃
  deriving DecidableEq, Repr

namespace Arc

instance instFintype : Fintype Arc where
  elems := ⟨[st1, st2, su, ut3, uv, vt1, vw, wt2, wt3], by decide⟩
  complete a := by cases a <;> decide

end Arc

/-- Terminals `0, 1, 2`, standing for `t₁, t₂, t₃`.-/
abbrev Terminal : Type := Fin 3

open Arc

/-- `onZ i a`: arc `a` lies on the cheap path `Z i`.-/
def onZ (i : Terminal) (a : Arc) : Bool :=
  match i.val, a with
  | 0, su | 0, uv | 0, vt1 => true
  | 1, su | 1, uv | 1, vw | 1, wt2 => true
  | 2, su | 2, uv | 2, vw | 2, wt3 => true
  | _, _ => false

/-- `onE i a`: arc `a` lies on the expensive path `E i`.-/
def onE (i : Terminal) (a : Arc) : Bool :=
  match i.val, a with
  | 0, st1 => true
  | 1, st2 => true
  | 2, su | 2, ut3 => true
  | _, _ => false

variable (K : Type*) [CommRing K] [LinearOrder K]

/-- An SSUF instance `(d, f, c)` on `H*`: demands `d i > 0`, cheap-path split
amounts `0 ≤ f i ≤ d i` (the fractional flow routes `f i` on `Z i` and
`d i - f i` on `E i`), and per-unit arc costs `c a ≥ 0`.-/
structure FlowInstance where
  /-- demand of terminal `i`-/
  d : Terminal → K
  /-- amount of demand `i` routed on the cheap path `Z i`-/
  f : Terminal → K
  /-- per-unit arc costs-/
  c : Arc → K
  d_pos : ∀ i, 0 < d i
  f_nonneg : ∀ i, 0 ≤ f i
  f_le_d : ∀ i, f i ≤ d i
  c_nonneg : ∀ a, 0 ≤ c a

namespace FlowInstance

variable {K} (I : FlowInstance K)

/-- `D = max_i d i`.-/
def dmax : K := max (I.d 0) (max (I.d 1) (I.d 2))

/-- The fractional flow on arc `a` induced by the splits.-/
def x (a : Arc) : K :=
  ∑ i, ((if onZ i a then I.f i else 0) + (if onE i a then I.d i - I.f i else 0))

/-- The load on arc `a` of the unsplittable routing `S` (the set of terminals
routed on their cheap path `Z`; terminals outside `S` take `E`).-/
def load (S : Finset Terminal) (a : Arc) : K :=
  ∑ i, if i ∈ S then (if onZ i a then I.d i else 0) else (if onE i a then I.d i else 0)

/-- Admissibility: the Dinitz–Garg–Goemans bound `y_a ≤ x_a + D` on every arc.-/
def Admissible (S : Finset Terminal) : Prop :=
  ∀ a, I.load S a ≤ I.x a + I.dmax

instance decidableAdmissible [DecidableLE K] (S : Finset Terminal) :
    Decidable (I.Admissible S) :=
  inferInstanceAs (Decidable (∀ a, I.load S a ≤ I.x a + I.dmax))

/-- Cost of the unsplittable routing `S`.-/
def ucost (S : Finset Terminal) : K := ∑ a, I.c a * I.load S a

/-- Cost of the fractional flow.-/
def fcost : K := ∑ a, I.c a * I.x a

/-! ### Nonnegativity -/

/-- Every fractional arc load is nonnegative. This needs only monotonicity of
addition, beyond the ordered commutative-ring structure carried by the model.-/
theorem x_nonneg [AddLeftMono K] (a : Arc) : 0 ≤ I.x a := by
  rw [x]
  apply Finset.sum_nonneg
  intro i _
  apply add_nonneg
  · split <;> simp [I.f_nonneg]
  · split <;> simp [sub_nonneg.mpr (I.f_le_d i)]

/-- Every unsplittable routing load is nonnegative on every arc.-/
theorem load_nonneg [AddLeftMono K] (S : Finset Terminal) (a : Arc) :
    0 ≤ I.load S a := by
  rw [load]
  apply Finset.sum_nonneg
  intro i _
  split
  · split <;> simp [(I.d_pos i).le]
  · split <;> simp [(I.d_pos i).le]

/-- Every unsplittable routing has nonnegative cost.-/
theorem ucost_nonneg [AddLeftMono K] [PosMulMono K] (S : Finset Terminal) :
    0 ≤ I.ucost S := by
  rw [ucost]
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (I.c_nonneg a) (I.load_nonneg S a)

/-- The fractional flow has nonnegative cost.-/
theorem fcost_nonneg [AddLeftMono K] [PosMulMono K] :
    0 ≤ I.fcost := by
  rw [fcost]
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (I.c_nonneg a) (I.x_nonneg a)

/-! ### Demands are bounded by `dmax` -/

theorem d_le_dmax (i : Terminal) : I.d i ≤ I.dmax := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem dmax_pos : 0 < I.dmax := lt_of_lt_of_le (I.d_pos 0) (I.d_le_dmax 0)

/-! ### Per-arc values of the fractional flow

The nine evaluation lemmas below unfold `x` on each arc.  These are the
identities used silently throughout Section 3 of the paper. -/

theorem x_st1 : I.x st1 = I.d 0 - I.f 0 := by
  simp [x, Fin.sum_univ_three, onZ, onE]
theorem x_st2 : I.x st2 = I.d 1 - I.f 1 := by
  simp [x, Fin.sum_univ_three, onZ, onE]
theorem x_su : I.x su = I.f 0 + I.f 1 + I.d 2 := by
  simp [x, Fin.sum_univ_three, onZ, onE]
theorem x_ut3 : I.x ut3 = I.d 2 - I.f 2 := by
  simp [x, Fin.sum_univ_three, onZ, onE]
theorem x_uv : I.x uv = I.f 0 + I.f 1 + I.f 2 := by
  simp [x, Fin.sum_univ_three, onZ, onE]
theorem x_vt1 : I.x vt1 = I.f 0 := by
  simp [x, Fin.sum_univ_three, onZ, onE]
theorem x_vw : I.x vw = I.f 1 + I.f 2 := by
  simp [x, Fin.sum_univ_three, onZ, onE]
theorem x_wt2 : I.x wt2 = I.f 1 := by
  simp [x, Fin.sum_univ_three, onZ, onE]
theorem x_wt3 : I.x wt3 = I.f 2 := by
  simp [x, Fin.sum_univ_three, onZ, onE]

/-! ### Per-arc loads of a routing -/

variable (S : Finset Terminal)

theorem load_st1 : I.load S st1 = if 0 ∈ S then 0 else I.d 0 := by
  simp only [load, Fin.sum_univ_three]
  simp [onZ, onE]
theorem load_st2 : I.load S st2 = if 1 ∈ S then 0 else I.d 1 := by
  simp only [load, Fin.sum_univ_three]
  simp [onZ, onE]
theorem load_su :
    I.load S su =
      (if 0 ∈ S then I.d 0 else 0) + (if 1 ∈ S then I.d 1 else 0) + I.d 2 := by
  simp only [load, Fin.sum_univ_three]
  simp [onZ, onE]
theorem load_ut3 : I.load S ut3 = if 2 ∈ S then 0 else I.d 2 := by
  simp only [load, Fin.sum_univ_three]
  simp [onZ, onE]
theorem load_uv :
    I.load S uv =
      (if 0 ∈ S then I.d 0 else 0) + (if 1 ∈ S then I.d 1 else 0) +
        (if 2 ∈ S then I.d 2 else 0) := by
  simp only [load, Fin.sum_univ_three]
  simp [onZ, onE]
theorem load_vt1 : I.load S vt1 = if 0 ∈ S then I.d 0 else 0 := by
  simp only [load, Fin.sum_univ_three]
  simp [onZ, onE]
theorem load_vw :
    I.load S vw = (if 1 ∈ S then I.d 1 else 0) + (if 2 ∈ S then I.d 2 else 0) := by
  simp only [load, Fin.sum_univ_three]
  simp [onZ, onE]
theorem load_wt2 : I.load S wt2 = if 1 ∈ S then I.d 1 else 0 := by
  simp only [load, Fin.sum_univ_three]
  simp [onZ, onE]
theorem load_wt3 : I.load S wt3 = if 2 ∈ S then I.d 2 else 0 := by
  simp only [load, Fin.sum_univ_three]
  simp [onZ, onE]

/-! ### Casting integral instances to the real model -/

/-- Regard an integral instance as a real instance. This is the bridge used
by the exact integer examples and the real-valued extremal theorem.-/
noncomputable def toReal (I : FlowInstance ℤ) : FlowInstance ℝ where
  d i := I.d i
  f i := I.f i
  c a := I.c a
  d_pos i := by exact_mod_cast I.d_pos i
  f_nonneg i := by exact_mod_cast I.f_nonneg i
  f_le_d i := by exact_mod_cast I.f_le_d i
  c_nonneg a := by exact_mod_cast I.c_nonneg a

@[simp] theorem toReal_d (I : FlowInstance ℤ) (i : Terminal) :
    I.toReal.d i = (I.d i : ℝ) := rfl

@[simp] theorem toReal_f (I : FlowInstance ℤ) (i : Terminal) :
    I.toReal.f i = (I.f i : ℝ) := rfl

@[simp] theorem toReal_c (I : FlowInstance ℤ) (a : Arc) :
    I.toReal.c a = (I.c a : ℝ) := rfl

@[simp] theorem toReal_dmax (I : FlowInstance ℤ) :
    I.toReal.dmax = (I.dmax : ℝ) := by
  simp [dmax, toReal]

@[simp] theorem toReal_x (I : FlowInstance ℤ) (a : Arc) :
    I.toReal.x a = (I.x a : ℝ) := by
  simp [x, toReal]

@[simp] theorem toReal_load (I : FlowInstance ℤ) (S : Finset Terminal) (a : Arc) :
    I.toReal.load S a = (I.load S a : ℝ) := by
  simp [load, toReal]

@[simp] theorem toReal_admissible (I : FlowInstance ℤ) (S : Finset Terminal) :
    I.toReal.Admissible S ↔ I.Admissible S := by
  simp only [Admissible, toReal_load, toReal_x, toReal_dmax]
  constructor
  · intro h a
    exact_mod_cast h a
  · intro h a
    exact_mod_cast h a

@[simp] theorem toReal_ucost (I : FlowInstance ℤ) (S : Finset Terminal) :
    I.toReal.ucost S = (I.ucost S : ℝ) := by
  change (∑ a, I.toReal.c a * I.toReal.load S a) =
    ((∑ a, I.c a * I.load S a : ℤ) : ℝ)
  simp

@[simp] theorem toReal_fcost (I : FlowInstance ℤ) :
    I.toReal.fcost = (I.fcost : ℝ) := by
  change (∑ a, I.toReal.c a * I.toReal.x a) =
    ((∑ a, I.c a * I.x a : ℤ) : ℝ)
  simp

end FlowInstance

end Goemans
