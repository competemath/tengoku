/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Config.Psi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The soundness witness table

The explicit witness of blueprint table 7.1: given five algebraically
independent elements `a, b, c, d, x`, the twenty-one points of the
`Q`-configuration are the principal closures of rational monomial
expressions in them. This file provides the *entry kit*: every table
entry is transcendental over the base (hence a point of the geometry),
via the uniform recovery principle `notMem_bot_of_recover` — if some
element recoverable from `z` and a side set `S` is not algebraic over
`S` alone, then `z` is transcendental.

The witness structure itself and the verification of the Ψ clauses
build on this kit (blueprint Thm q-correct, soundness direction).

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4, checklist G3 soundness).
-/

namespace AclGeom

noncomputable section

variable {k : Type*} {K : Type*} [Field k] [Field K] [Algebra k K]

section Recovery

/-- The recovery principle: if `w` is algebraic over `S` together with
`z` but not over `S` alone, then `z` is transcendental over the base.-/
theorem notMem_bot_of_recover {z : K} (S : Set K) {w : K}
    (hrec : w ∈ racl k (insert z S)) (hw : w ∉ racl k S) :
    z ∉ (⊥ : ClosedIF k K) := by
  intro hz
  have hz' : z ∈ racl k S := by
    have h0 : z ∈ racl k (∅ : Set K) :=
      mem_racl_empty_of_isAlgebraic (ClosedIF.mem_bot_iff.1 hz)
    exact racl_mono (Set.empty_subset _) h0
  rw [racl_insert_of_mem hz'] at hrec
  exact hw hrec

/-- Transcendental elements are nonzero, in lattice form.-/
theorem ne_zero_of_notMem_bot {z : K} (hz : z ∉ (⊥ : ClosedIF k K)) :
    z ≠ 0 := by
  intro h0
  refine hz ?_
  rw [h0]
  exact ClosedIF.mem_bot_iff.2 isAlgebraic_zero

end Recovery

section QTable

variable {a b c d x : K} (hind : AlgebraicIndependent k ![a, b, c, d, x])

/-! ### Independence projections

Named projections of the five-tuple independence, in the pair and side-set
forms consumed by the entry kit. -/

include hind

theorem qtable_a_notMem_bot : a ∉ (⊥ : ClosedIF k K) := fun h ↦
  hind.transcendental 0 (ClosedIF.mem_bot_iff.1 h)

theorem qtable_b_notMem_bot : b ∉ (⊥ : ClosedIF k K) := fun h ↦
  hind.transcendental 1 (ClosedIF.mem_bot_iff.1 h)

theorem qtable_c_notMem_bot : c ∉ (⊥ : ClosedIF k K) := fun h ↦
  hind.transcendental 2 (ClosedIF.mem_bot_iff.1 h)

theorem qtable_d_notMem_bot : d ∉ (⊥ : ClosedIF k K) := fun h ↦
  hind.transcendental 3 (ClosedIF.mem_bot_iff.1 h)

theorem qtable_x_notMem_bot : x ∉ (⊥ : ClosedIF k K) := fun h ↦
  hind.transcendental 4 (ClosedIF.mem_bot_iff.1 h)

theorem qtable_a_ne_zero : a ≠ 0 :=
  ne_zero_of_notMem_bot (qtable_a_notMem_bot hind)

theorem qtable_b_ne_zero : b ≠ 0 :=
  ne_zero_of_notMem_bot (qtable_b_notMem_bot hind)

theorem qtable_c_ne_zero : c ≠ 0 :=
  ne_zero_of_notMem_bot (qtable_c_notMem_bot hind)

theorem qtable_c_notMem_a : c ∉ racl k ({a} : Set K) := by
  have h : AlgebraicIndependent k ![c, a] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 2) (j := 0) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair' h

theorem qtable_x_notMem_a : x ∉ racl k ({a} : Set K) := by
  have h : AlgebraicIndependent k ![x, a] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 4) (j := 0) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair' h

theorem qtable_c_notMem_b : c ∉ racl k ({b} : Set K) := by
  have h : AlgebraicIndependent k ![c, b] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 2) (j := 1) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair' h

theorem qtable_a_notMem_b : a ∉ racl k ({b} : Set K) := by
  have h : AlgebraicIndependent k ![a, b] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 0) (j := 1) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair' h

theorem qtable_b_notMem_c : b ∉ racl k ({c} : Set K) := by
  have h : AlgebraicIndependent k ![b, c] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 1) (j := 2) (by decide)
  exact AlgebraicIndependent.notMem_racl_pair' h

theorem qtable_d_notMem_bc : d ∉ racl k ({b, c} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {1, 2}) (i := 3) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_b_notMem_ax : b ∉ racl k ({a, x} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 4}) (i := 1) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_x_notMem_ab : x ∉ racl k ({a, b} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 1}) (i := 4) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_x_notMem_ac : x ∉ racl k ({a, c} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 2}) (i := 4) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_b_notMem_ac : b ∉ racl k ({a, c} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 2}) (i := 1) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_c_notMem_abx : c ∉ racl k ({a, b, x} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 1, 4}) (i := 2) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_d_notMem_abcx : d ∉ racl k ({a, b, c, x} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 1, 2, 4}) (i := 3) (by decide)
  simpa [Set.image_insert_eq] using h

theorem qtable_x_notMem_abcd : x ∉ racl k ({a, b, c, d} : Set K) := by
  have h := AlgebraicIndependent.notMem_racl_image hind
    (S := {0, 1, 2, 3}) (i := 4) (by decide)
  simpa [Set.image_insert_eq] using h

/-- The point `Y = [ax+b]` is generic over the configuration base: `b` and
`a` recover `x` from it.-/
theorem qtable_Y_notMem_abcd :
    a * x + b ∉ racl k ({a, b, c, d} : Set K) := by
  intro hY
  have ha : a ∈ racl k ({a, b, c, d} : Set K) :=
    subset_racl k _ (by simp)
  have hb : b ∈ racl k ({a, b, c, d} : Set K) :=
    subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem (inv_mem ha) (sub_mem hY hb)
  rw [add_sub_cancel_right,
    inv_mul_cancel_left₀ (qtable_a_ne_zero hind)] at h
  exact qtable_x_notMem_abcd hind h

/-- The point `Z = [c(ax+b)+d]` is generic over the configuration base.-/
theorem qtable_Z_notMem_abcd :
    c * (a * x + b) + d ∉ racl k ({a, b, c, d} : Set K) := by
  intro hZ
  have hc : c ∈ racl k ({a, b, c, d} : Set K) :=
    subset_racl k _ (by simp)
  have hd : d ∈ racl k ({a, b, c, d} : Set K) :=
    subset_racl k _ (by simp)
  have h := MulMemClass.mul_mem (inv_mem hc) (sub_mem hZ hd)
  rw [add_sub_cancel_right,
    inv_mul_cancel_left₀ (qtable_c_ne_zero hind)] at h
  exact qtable_Y_notMem_abcd hind h

/-! ### Transcendence of the table entries

Each composite entry of table 7.1 is transcendental over the base, by the
recovery principle: dividing or subtracting away the side factors recovers
a generator not algebraic over the side set. -/

/-- The entry `C₁ = [ac]`.-/
theorem qtable_mul_ac_notMem_bot : a * c ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a} ?_ (qtable_c_notMem_a hind)
  have hac : a * c ∈ racl k (insert (a * c) ({a} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k (insert (a * c) ({a} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have h := MulMemClass.mul_mem (inv_mem ha) hac
  rwa [inv_mul_cancel_left₀ (qtable_a_ne_zero hind)] at h

/-- The entry `D = [ax]`.-/
theorem qtable_mul_ax_notMem_bot : a * x ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a} ?_ (qtable_x_notMem_a hind)
  have hax : a * x ∈ racl k (insert (a * x) ({a} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k (insert (a * x) ({a} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have h := MulMemClass.mul_mem (inv_mem ha) hax
  rwa [inv_mul_cancel_left₀ (qtable_a_ne_zero hind)] at h

/-- The entry `G = [bc]`.-/
theorem qtable_mul_bc_notMem_bot : b * c ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {b} ?_ (qtable_c_notMem_b hind)
  have hbc : b * c ∈ racl k (insert (b * c) ({b} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hb : b ∈ racl k (insert (b * c) ({b} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have h := MulMemClass.mul_mem (inv_mem hb) hbc
  rwa [inv_mul_cancel_left₀ (qtable_b_ne_zero hind)] at h

/-- The entry `U' = [cb]`.-/
theorem qtable_mul_cb_notMem_bot : c * b ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {c} ?_ (qtable_b_notMem_c hind)
  have hcb : c * b ∈ racl k (insert (c * b) ({c} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hc : c ∈ racl k (insert (c * b) ({c} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have h := MulMemClass.mul_mem (inv_mem hc) hcb
  rwa [inv_mul_cancel_left₀ (qtable_c_ne_zero hind)] at h

/-- The entry `H = [a/b]`.-/
theorem qtable_div_ab_notMem_bot : a / b ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {b} ?_ (qtable_a_notMem_b hind)
  have hq : a / b ∈ racl k (insert (a / b) ({b} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hb : b ∈ racl k (insert (a / b) ({b} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have h := MulMemClass.mul_mem hq hb
  rwa [div_mul_cancel₀ a (qtable_b_ne_zero hind)] at h

/-- The entry `C₂ = [bc + d]`.-/
theorem qtable_bcd_notMem_bot : b * c + d ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {b, c} ?_ (qtable_d_notMem_bc hind)
  have hbcd : b * c + d ∈ racl k (insert (b * c + d) ({b, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hb : b ∈ racl k (insert (b * c + d) ({b, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hc : c ∈ racl k (insert (b * c + d) ({b, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have h := sub_mem hbcd (MulMemClass.mul_mem hb hc)
  rwa [add_sub_cancel_left] at h

/-- The entry `Y = [ax + b]`.-/
theorem qtable_Y_notMem_bot : a * x + b ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a, x} ?_ (qtable_b_notMem_ax hind)
  have hY : a * x + b ∈ racl k (insert (a * x + b) ({a, x} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k (insert (a * x + b) ({a, x} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hx : x ∈ racl k (insert (a * x + b) ({a, x} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have h := sub_mem hY (MulMemClass.mul_mem ha hx)
  rwa [add_sub_cancel_left] at h

/-- The entry `I = [ax/b]`.-/
theorem qtable_axb_notMem_bot : a * x / b ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a, b} ?_ (qtable_x_notMem_ab hind)
  have hI : a * x / b ∈ racl k (insert (a * x / b) ({a, b} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k (insert (a * x / b) ({a, b} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hb : b ∈ racl k (insert (a * x / b) ({a, b} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have h := MulMemClass.mul_mem (inv_mem ha) (MulMemClass.mul_mem hI hb)
  have harith : a⁻¹ * (a * x / b * b) = x := by
    rw [div_mul_cancel₀ _ (qtable_b_ne_zero hind),
      inv_mul_cancel_left₀ (qtable_a_ne_zero hind)]
  rwa [harith] at h

/-- The entry `F = [acx]`.-/
theorem qtable_acx_notMem_bot : a * c * x ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a, c} ?_ (qtable_x_notMem_ac hind)
  have hF : a * c * x ∈ racl k (insert (a * c * x) ({a, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k (insert (a * c * x) ({a, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hc : c ∈ racl k (insert (a * c * x) ({a, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have h := MulMemClass.mul_mem
    (inv_mem (MulMemClass.mul_mem ha hc)) hF
  have harith : (a * c)⁻¹ * (a * c * x) = x :=
    inv_mul_cancel_left₀
      (mul_ne_zero (qtable_a_ne_zero hind) (qtable_c_ne_zero hind)) x
  rwa [harith] at h

/-- The entry `T' = [acb]`.-/
theorem qtable_acb_notMem_bot : a * c * b ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a, c} ?_ (qtable_b_notMem_ac hind)
  have hT : a * c * b ∈ racl k (insert (a * c * b) ({a, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k (insert (a * c * b) ({a, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hc : c ∈ racl k (insert (a * c * b) ({a, c} : Set K)) :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have h := MulMemClass.mul_mem
    (inv_mem (MulMemClass.mul_mem ha hc)) hT
  have harith : (a * c)⁻¹ * (a * c * b) = b :=
    inv_mul_cancel_left₀
      (mul_ne_zero (qtable_a_ne_zero hind) (qtable_c_ne_zero hind)) b
  rwa [harith] at h

/-- The entry `E = [c(ax + b)]`.-/
theorem qtable_E_notMem_bot : c * (a * x + b) ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a, b, x} ?_ (qtable_c_notMem_abx hind)
  set S : Set K := insert (c * (a * x + b)) {a, b, x} with hS
  have hE : c * (a * x + b) ∈ racl k S := subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k S :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hb : b ∈ racl k S := subset_racl k _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hx : x ∈ racl k S := subset_racl k _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ rfl)))
  have hY : a * x + b ∈ racl k S :=
    add_mem (MulMemClass.mul_mem ha hx) hb
  have hY0 : a * x + b ≠ 0 :=
    ne_zero_of_notMem_bot (qtable_Y_notMem_bot hind)
  have h := MulMemClass.mul_mem hE (inv_mem hY)
  rwa [mul_inv_cancel_right₀ hY0] at h

/-- The entry `Z = [c(ax + b) + d]`.-/
theorem qtable_Z_notMem_bot :
    c * (a * x + b) + d ∉ (⊥ : ClosedIF k K) := by
  refine notMem_bot_of_recover {a, b, c, x} ?_ (qtable_d_notMem_abcx hind)
  set S : Set K := insert (c * (a * x + b) + d) {a, b, c, x} with hS
  have hZ : c * (a * x + b) + d ∈ racl k S :=
    subset_racl k _ (Set.mem_insert _ _)
  have ha : a ∈ racl k S :=
    subset_racl k _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hb : b ∈ racl k S := subset_racl k _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hc : c ∈ racl k S := subset_racl k _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  have hx : x ∈ racl k S := subset_racl k _
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))))
  have h := sub_mem hZ (MulMemClass.mul_mem hc
    (add_mem (MulMemClass.mul_mem ha hx) hb))
  rwa [add_sub_cancel_left] at h

/-! ### The witness

The twenty-one points of blueprint table 7.1, assembled. -/

/-- The soundness witness of blueprint table 7.1: the twenty-one points of
the `Q`-configuration as principal closures of rational expressions in the
independent generators `a, b, c, d, x` (with `u = b`, `v = ax`).-/
def qWitness : QWitness k K where
  A₁ := Point.mk' k a (qtable_a_notMem_bot hind)
  A₂ := Point.mk' k b (qtable_b_notMem_bot hind)
  B₁ := Point.mk' k c (qtable_c_notMem_bot hind)
  B₂ := Point.mk' k d (qtable_d_notMem_bot hind)
  C₁ := Point.mk' k (a * c) (qtable_mul_ac_notMem_bot hind)
  C₂ := Point.mk' k (b * c + d) (qtable_bcd_notMem_bot hind)
  D := Point.mk' k (a * x) (qtable_mul_ax_notMem_bot hind)
  E := Point.mk' k (c * (a * x + b)) (qtable_E_notMem_bot hind)
  F := Point.mk' k (a * c * x) (qtable_acx_notMem_bot hind)
  G := Point.mk' k (b * c) (qtable_mul_bc_notMem_bot hind)
  H := Point.mk' k (a / b) (qtable_div_ab_notMem_bot hind)
  I := Point.mk' k (a * x / b) (qtable_axb_notMem_bot hind)
  P := Point.mk' k b (qtable_b_notMem_bot hind)
  Q := Point.mk' k d (qtable_d_notMem_bot hind)
  R := Point.mk' k (b * c + d) (qtable_bcd_notMem_bot hind)
  S := Point.mk' k a (qtable_a_notMem_bot hind)
  T := Point.mk' k c (qtable_c_notMem_bot hind)
  U := Point.mk' k (a * c) (qtable_mul_ac_notMem_bot hind)
  X := Point.mk' k x (qtable_x_notMem_bot hind)
  Y := Point.mk' k (a * x + b) (qtable_Y_notMem_bot hind)
  Z := Point.mk' k (c * (a * x + b) + d) (qtable_Z_notMem_bot hind)

/-! ### Clause (v): the dependent triple sits inside `A, B, C` -/

theorem qWitness_S_le : (qWitness hind).S.1 ≤ (qWitness hind).A :=
  le_sup_left

theorem qWitness_T_le : (qWitness hind).T.1 ≤ (qWitness hind).B :=
  le_sup_left

theorem qWitness_U_le : (qWitness hind).U.1 ≤ (qWitness hind).C :=
  le_sup_left

/-- Clause (v), rank part: the triple `([a], [c], [ac])` is dependent.-/
theorem qWitness_rank_STU :
    RankEq 2 ((qWitness hind).S.1 ⊔
      ((qWitness hind).T.1 ⊔ (qWitness hind).U.1)) := by
  have hac : AlgebraicIndependent k ![a, c] := by
    simpa using AlgebraicIndependent.comp_pair hind
      (i := 0) (j := 2) (by decide)
  refine rankEq_of_coe_eq_racl hac ?_
  show ((ClosedIF.point k a ⊔ (ClosedIF.point k c ⊔
    ClosedIF.point k (a * c))).1 : IntermediateField k K) = _
  rw [ClosedIF.coe_sup]
  simp only [ClosedIF.coe_set_sup, ClosedIF.coe_set_point]
  have hrange : Set.range ![a, c] = {a, c} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty]
    simp only [Set.union_empty, Set.union_singleton]
    exact Set.pair_comm c a
  rw [hrange]
  have ha : a ∈ racl k ({a, c} : Set K) :=
    subset_racl k _ (Set.mem_insert _ _)
  have hc : c ∈ racl k ({a, c} : Set K) :=
    subset_racl k _ (Set.mem_insert_of_mem _ rfl)
  have hacm : a * c ∈ racl k ({a, c} : Set K) :=
    MulMemClass.mul_mem ha hc
  refine racl_congr_of_subset_racl ?_ ?_
  · rintro z (hz | hz)
    · exact racl_le_of_subset_racl (Set.singleton_subset_iff.2 ha) hz
    · have hle : racl k ((racl k {c} : Set K) ∪
          (racl k {a * c} : Set K)) ≤ racl k ({a, c} : Set K) := by
        refine racl_le_of_subset_racl (Set.union_subset ?_ ?_)
        · exact fun w hw ↦
            racl_le_of_subset_racl (Set.singleton_subset_iff.2 hc) hw
        · exact fun w hw ↦
            racl_le_of_subset_racl (Set.singleton_subset_iff.2 hacm) hw
      exact hle hz
  · rintro z (rfl | rfl)
    · refine subset_racl k _ ?_
      refine Set.mem_union_left _ ?_
      exact subset_racl k _ rfl
    · refine subset_racl k _ ?_
      refine Set.mem_union_right _ ?_
      refine subset_racl k _ ?_
      refine Set.mem_union_left _ ?_
      exact subset_racl k _ rfl

/-! ### Clause (ii): the incidences of `X` and `Z` -/

/-- Clause (ii), first part: `X ≤ A ∨ Y`, because `x = ((ax+b) - b)/a`.-/
theorem qWitness_X_le :
    (qWitness hind).X.1 ≤ (qWitness hind).A ⊔ (qWitness hind).Y.1 := by
  refine ClosedIF.point_le_iff.2 ?_
  rw [ClosedIF.mem_sup_iff]
  have ha : a ∈ racl k (((qWitness hind).A : Set K) ∪
      ((qWitness hind).Y.1 : Set K)) := by
    refine subset_racl k _ (Set.mem_union_left _ ?_)
    exact (ClosedIF.le_iff.1 le_sup_left) (ClosedIF.mem_point_self a)
  have hb : b ∈ racl k (((qWitness hind).A : Set K) ∪
      ((qWitness hind).Y.1 : Set K)) := by
    refine subset_racl k _ (Set.mem_union_left _ ?_)
    exact (ClosedIF.le_iff.1 le_sup_right) (ClosedIF.mem_point_self b)
  have hY : a * x + b ∈ racl k (((qWitness hind).A : Set K) ∪
      ((qWitness hind).Y.1 : Set K)) := by
    refine subset_racl k _ (Set.mem_union_right _ ?_)
    exact ClosedIF.mem_point_self _
  have h := MulMemClass.mul_mem (inv_mem ha) (sub_mem hY hb)
  have harith : a⁻¹ * (a * x + b - b) = x := by
    rw [add_sub_cancel_right, inv_mul_cancel_left₀ (qtable_a_ne_zero hind)]
  rwa [harith] at h

/-- Clause (ii), second part: `Z ≤ (B ∨ Y) ∧ (C ∨ X)`, because
`z = cY + d = (ac)x + (bc+d)`.-/
theorem qWitness_Z_le :
    (qWitness hind).Z.1 ≤
      ((qWitness hind).B ⊔ (qWitness hind).Y.1) ⊓
        ((qWitness hind).C ⊔ (qWitness hind).X.1) := by
  refine le_inf ?_ ?_
  · refine ClosedIF.point_le_iff.2 ?_
    rw [ClosedIF.mem_sup_iff]
    have hc : c ∈ racl k (((qWitness hind).B : Set K) ∪
        ((qWitness hind).Y.1 : Set K)) := by
      refine subset_racl k _ (Set.mem_union_left _ ?_)
      exact (ClosedIF.le_iff.1 le_sup_left) (ClosedIF.mem_point_self c)
    have hd : d ∈ racl k (((qWitness hind).B : Set K) ∪
        ((qWitness hind).Y.1 : Set K)) := by
      refine subset_racl k _ (Set.mem_union_left _ ?_)
      exact (ClosedIF.le_iff.1 le_sup_right) (ClosedIF.mem_point_self d)
    have hY : a * x + b ∈ racl k (((qWitness hind).B : Set K) ∪
        ((qWitness hind).Y.1 : Set K)) := by
      refine subset_racl k _ (Set.mem_union_right _ ?_)
      exact ClosedIF.mem_point_self _
    exact add_mem (MulMemClass.mul_mem hc hY) hd
  · refine ClosedIF.point_le_iff.2 ?_
    rw [ClosedIF.mem_sup_iff]
    have hac : a * c ∈ racl k (((qWitness hind).C : Set K) ∪
        ((qWitness hind).X.1 : Set K)) := by
      refine subset_racl k _ (Set.mem_union_left _ ?_)
      exact (ClosedIF.le_iff.1 le_sup_left) (ClosedIF.mem_point_self _)
    have hbcd : b * c + d ∈ racl k (((qWitness hind).C : Set K) ∪
        ((qWitness hind).X.1 : Set K)) := by
      refine subset_racl k _ (Set.mem_union_left _ ?_)
      exact (ClosedIF.le_iff.1 le_sup_right) (ClosedIF.mem_point_self _)
    have hx : x ∈ racl k (((qWitness hind).C : Set K) ∪
        ((qWitness hind).X.1 : Set K)) := by
      refine subset_racl k _ (Set.mem_union_right _ ?_)
      exact ClosedIF.mem_point_self _
    have h := add_mem (MulMemClass.mul_mem hac hx) hbcd
    have harith : a * c * x + (b * c + d) = c * (a * x + b) + d := by
      ring
    rwa [harith] at h

/-! ### Clause (iii): genericity of `X, Y, Z` over `A ∨ B ∨ C` -/

/-- The join `A ∨ B ∨ C` is bounded by the closure of the four
generators (the entries `ac` and `bc+d` are absorbed).-/
theorem qWitness_ABC_le :
    (qWitness hind).A ⊔ (qWitness hind).B ⊔ (qWitness hind).C ≤
      ⟨racl k ({a, b, c, d} : Set K), isRAC_racl _⟩ := by
  have ha : a ∈ racl k ({a, b, c, d} : Set K) :=
    subset_racl k _ (by simp)
  have hb : b ∈ racl k ({a, b, c, d} : Set K) :=
    subset_racl k _ (by simp)
  have hc : c ∈ racl k ({a, b, c, d} : Set K) :=
    subset_racl k _ (by simp)
  have hd : d ∈ racl k ({a, b, c, d} : Set K) :=
    subset_racl k _ (by simp)
  have hacm : a * c ∈ racl k ({a, b, c, d} : Set K) :=
    MulMemClass.mul_mem ha hc
  have hbcd : b * c + d ∈ racl k ({a, b, c, d} : Set K) :=
    add_mem (MulMemClass.mul_mem hb hc) hd
  refine sup_le (sup_le ?_ ?_) ?_
  · exact sup_le (ClosedIF.point_le_iff.2 ha) (ClosedIF.point_le_iff.2 hb)
  · exact sup_le (ClosedIF.point_le_iff.2 hc) (ClosedIF.point_le_iff.2 hd)
  · exact sup_le (ClosedIF.point_le_iff.2 hacm)
      (ClosedIF.point_le_iff.2 hbcd)

theorem qWitness_X_notLe :
    ¬ (qWitness hind).X.1 ≤
      (qWitness hind).A ⊔ (qWitness hind).B ⊔ (qWitness hind).C := by
  intro hle
  exact qtable_x_notMem_abcd hind
    (ClosedIF.point_le_iff.1 (hle.trans (qWitness_ABC_le hind)))

theorem qWitness_Y_notLe :
    ¬ (qWitness hind).Y.1 ≤
      (qWitness hind).A ⊔ (qWitness hind).B ⊔ (qWitness hind).C := by
  intro hle
  exact qtable_Y_notMem_abcd hind
    (ClosedIF.point_le_iff.1 (hle.trans (qWitness_ABC_le hind)))

theorem qWitness_Z_notLe :
    ¬ (qWitness hind).Z.1 ≤
      (qWitness hind).A ⊔ (qWitness hind).B ⊔ (qWitness hind).C := by
  intro hle
  exact qtable_Z_notMem_abcd hind
    (ClosedIF.point_le_iff.1 (hle.trans (qWitness_ABC_le hind)))

/-! ### Clause (i): the four rank-four joins

All four joins `A∨B∨C`, `A∨B`, `B∨C`, `A∨C` have underlying field
`racl k {a, b, c, d}` — the birational changes
`(a,b,c,d) ↔ (c,d,ac,bc+d)` and `(a,b,c,d) ↔ (a,b,ac,bc+d)` recover the
generators — so each has rank four by the rank bridge. -/

theorem qtable_indep_abcd : AlgebraicIndependent k ![a, b, c, d] := by
  have h := AlgebraicIndependent.comp hind
    (Fin.castLE (by norm_num : (4 : ℕ) ≤ 5))
    (Fin.strictMono_castLE _).injective
  have heq : (![a, b, c, d, x] ∘ Fin.castLE (by norm_num : (4 : ℕ) ≤ 5)) =
      ![a, b, c, d] := by
    funext i
    fin_cases i <;> rfl
  rwa [heq] at h

/-- The generator range, normalized.-/
theorem qtable_range_abcd :
    Set.range ![a, b, c, d] = ({a, b, c, d} : Set K) := by
  ext z
  simp [Matrix.range_cons, Matrix.range_empty]
  tauto

/-- Clause (i), total join: `rk(A ∨ B ∨ C) = 4`.-/
theorem qWitness_rank_ABC :
    RankEq 4 ((qWitness hind).A ⊔ (qWitness hind).B ⊔ (qWitness hind).C) := by
  refine rankEq_of_coe_eq_racl (qtable_indep_abcd hind) ?_
  rw [qtable_range_abcd hind]
  refine ClosedIF.coe_eq_racl_of_le (qWitness_ABC_le hind) ?_
  rintro z (rfl | rfl | rfl | rfl)
  · exact (ClosedIF.le_iff.1 (le_sup_left.trans le_sup_left))
      ((ClosedIF.le_iff.1 le_sup_left) (ClosedIF.mem_point_self z))
  · exact (ClosedIF.le_iff.1 (le_sup_left.trans le_sup_left))
      ((ClosedIF.le_iff.1 le_sup_right) (ClosedIF.mem_point_self z))
  · exact (ClosedIF.le_iff.1 (le_sup_right.trans le_sup_left))
      ((ClosedIF.le_iff.1 le_sup_left) (ClosedIF.mem_point_self z))
  · exact (ClosedIF.le_iff.1 (le_sup_right.trans le_sup_left))
      ((ClosedIF.le_iff.1 le_sup_right) (ClosedIF.mem_point_self z))

/-- Clause (i): `rk(A ∨ B) = 4`.-/
theorem qWitness_rank_AB :
    RankEq 4 ((qWitness hind).A ⊔ (qWitness hind).B) := by
  refine rankEq_of_coe_eq_racl (qtable_indep_abcd hind) ?_
  rw [qtable_range_abcd hind]
  have ha : a ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
  have hb : b ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
  have hc : c ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
  have hd : d ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
  refine ClosedIF.coe_eq_racl_of_le ?_ ?_
  · refine sup_le ?_ ?_
    · exact sup_le (ClosedIF.point_le_iff.2 ha) (ClosedIF.point_le_iff.2 hb)
    · exact sup_le (ClosedIF.point_le_iff.2 hc) (ClosedIF.point_le_iff.2 hd)
  · rintro z (rfl | rfl | rfl | rfl)
    · exact (ClosedIF.le_iff.1 le_sup_left)
        ((ClosedIF.le_iff.1 le_sup_left) (ClosedIF.mem_point_self z))
    · exact (ClosedIF.le_iff.1 le_sup_left)
        ((ClosedIF.le_iff.1 le_sup_right) (ClosedIF.mem_point_self z))
    · exact (ClosedIF.le_iff.1 le_sup_right)
        ((ClosedIF.le_iff.1 le_sup_left) (ClosedIF.mem_point_self z))
    · exact (ClosedIF.le_iff.1 le_sup_right)
        ((ClosedIF.le_iff.1 le_sup_right) (ClosedIF.mem_point_self z))

/-- Clause (i): `rk(B ∨ C) = 4` — the generators are recovered by
`a = (ac)/c` and `b = ((bc+d)-d)/c`.-/
theorem qWitness_rank_BC :
    RankEq 4 ((qWitness hind).B ⊔ (qWitness hind).C) := by
  refine rankEq_of_coe_eq_racl (qtable_indep_abcd hind) ?_
  rw [qtable_range_abcd hind]
  have ha : a ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
  have hb : b ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
  have hc : c ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
  have hd : d ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
  have hacm : a * c ∈ racl k ({a, b, c, d} : Set K) :=
    MulMemClass.mul_mem ha hc
  have hbcd : b * c + d ∈ racl k ({a, b, c, d} : Set K) :=
    add_mem (MulMemClass.mul_mem hb hc) hd
  set E := (qWitness hind).B ⊔ (qWitness hind).C with hE
  have hcE : c ∈ (E.1 : IntermediateField k K) :=
    (ClosedIF.le_iff.1 le_sup_left)
      ((ClosedIF.le_iff.1 le_sup_left) (ClosedIF.mem_point_self c))
  have hdE : d ∈ (E.1 : IntermediateField k K) :=
    (ClosedIF.le_iff.1 le_sup_left)
      ((ClosedIF.le_iff.1 le_sup_right) (ClosedIF.mem_point_self d))
  have hacE : a * c ∈ (E.1 : IntermediateField k K) :=
    (ClosedIF.le_iff.1 le_sup_right)
      ((ClosedIF.le_iff.1 le_sup_left) (ClosedIF.mem_point_self _))
  have hbcdE : b * c + d ∈ (E.1 : IntermediateField k K) :=
    (ClosedIF.le_iff.1 le_sup_right)
      ((ClosedIF.le_iff.1 le_sup_right) (ClosedIF.mem_point_self _))
  have haE : a ∈ (E.1 : IntermediateField k K) := by
    have h := MulMemClass.mul_mem hacE (inv_mem hcE)
    rwa [mul_inv_cancel_right₀ (qtable_c_ne_zero hind)] at h
  have hbE : b ∈ (E.1 : IntermediateField k K) := by
    have h := MulMemClass.mul_mem (sub_mem hbcdE hdE) (inv_mem hcE)
    rwa [add_sub_cancel_right, mul_inv_cancel_right₀
      (qtable_c_ne_zero hind)] at h
  refine ClosedIF.coe_eq_racl_of_le ?_ ?_
  · refine sup_le ?_ ?_
    · exact sup_le (ClosedIF.point_le_iff.2 hc) (ClosedIF.point_le_iff.2 hd)
    · exact sup_le (ClosedIF.point_le_iff.2 hacm)
        (ClosedIF.point_le_iff.2 hbcd)
  · rintro z (rfl | rfl | rfl | rfl)
    · exact haE
    · exact hbE
    · exact hcE
    · exact hdE

/-- Clause (i): `rk(A ∨ C) = 4` — the generators are recovered by
`c = (ac)/a` and `d = (bc+d) - bc`.-/
theorem qWitness_rank_AC :
    RankEq 4 ((qWitness hind).A ⊔ (qWitness hind).C) := by
  refine rankEq_of_coe_eq_racl (qtable_indep_abcd hind) ?_
  rw [qtable_range_abcd hind]
  have ha : a ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
  have hb : b ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
  have hc : c ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
  have hd : d ∈ racl k ({a, b, c, d} : Set K) := subset_racl k _ (by simp)
  have hacm : a * c ∈ racl k ({a, b, c, d} : Set K) :=
    MulMemClass.mul_mem ha hc
  have hbcd : b * c + d ∈ racl k ({a, b, c, d} : Set K) :=
    add_mem (MulMemClass.mul_mem hb hc) hd
  set E := (qWitness hind).A ⊔ (qWitness hind).C with hE
  have haE : a ∈ (E.1 : IntermediateField k K) :=
    (ClosedIF.le_iff.1 le_sup_left)
      ((ClosedIF.le_iff.1 le_sup_left) (ClosedIF.mem_point_self a))
  have hbe : b ∈ (E.1 : IntermediateField k K) :=
    (ClosedIF.le_iff.1 le_sup_left)
      ((ClosedIF.le_iff.1 le_sup_right) (ClosedIF.mem_point_self b))
  have hacE : a * c ∈ (E.1 : IntermediateField k K) :=
    (ClosedIF.le_iff.1 le_sup_right)
      ((ClosedIF.le_iff.1 le_sup_left) (ClosedIF.mem_point_self _))
  have hbcdE : b * c + d ∈ (E.1 : IntermediateField k K) :=
    (ClosedIF.le_iff.1 le_sup_right)
      ((ClosedIF.le_iff.1 le_sup_right) (ClosedIF.mem_point_self _))
  have hcE : c ∈ (E.1 : IntermediateField k K) := by
    have h := MulMemClass.mul_mem (inv_mem haE) hacE
    rwa [inv_mul_cancel_left₀ (qtable_a_ne_zero hind)] at h
  have hdE : d ∈ (E.1 : IntermediateField k K) := by
    have h := sub_mem hbcdE (MulMemClass.mul_mem hbe hcE)
    rwa [add_sub_cancel_left] at h
  refine ClosedIF.coe_eq_racl_of_le ?_ ?_
  · refine sup_le ?_ ?_
    · exact sup_le (ClosedIF.point_le_iff.2 ha) (ClosedIF.point_le_iff.2 hb)
    · exact sup_le (ClosedIF.point_le_iff.2 hacm)
        (ClosedIF.point_le_iff.2 hbcd)
  · rintro z (rfl | rfl | rfl | rfl)
    · exact haE
    · exact hbe
    · exact hcE
    · exact hdE

end QTable

end

end AclGeom
