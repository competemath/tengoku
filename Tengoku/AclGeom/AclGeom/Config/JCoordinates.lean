/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Config.Semantic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The semantic `j`-tuple `j(x, a)` as points

The five-tuple of points `j(x, a) = ([x], [x+a], [xa], [x+xa], [a])` of an independent pair
(`jTupleOf`), the transcendence of its coordinates (`jCoordinates_notMem_bot`), its simp API, and
the fact that it is a semantic `j`-tuple (`jSem_jTupleOf`).  Moved unchanged from
`AclGeom.Counterexamples.GenericArithmetic`, which now imports it.

Two normalizations are new.  A five-tuple with the coordinate equations of `JSem` is literally a
`jTupleOf` (`eq_jTupleOf`).  Raising both entries to the same power of the characteristic exponent
does not move any point (`jTupleOf_pow_expChar_pow`): `j(x^{q^n}, a^{q^n}) = j(x, a)`.  The second
needs only positive powers, so no perfection or inverse Frobenius.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** complete.
-/

namespace AclGeom

noncomputable section

open ClosedIF

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section JTuples

/-- If `x` is transcendental over `a` and algebraic over `{z, a}`, then `z`
is transcendental.
@isnad1 id=not.2h5v.s7.a5a577c7ec25 from=translated src=- shape=5c2c47d8 vocab=2fa0be38
-/
theorem notMem_bot_of_mem_racl_pair {x a z : K} (hx : x ∉ racl k ({a} : Set K))
    (h : x ∈ racl k ({z, a} : Set K)) : z ∉ (⊥ : ClosedIF k K) := by
  intro hz
  apply hx
  refine racl_le_of_subset_racl ?_ h
  rintro w (rfl | rfl)
  · exact racl_mono (Set.empty_subset _)
      (mem_racl_empty_of_isAlgebraic (ClosedIF.mem_bot_iff.1 hz))
  · exact subset_racl k _ rfl

variable {x a : K}

private theorem mem_pair_left {z w : K} : z ∈ racl k ({z, w} : Set K) :=
  subset_racl k _ (Set.mem_insert _ _)

private theorem mem_pair_right {z w : K} : w ∈ racl k ({z, w} : Set K) :=
  subset_racl k _ (Set.mem_insert_of_mem _ rfl)

/-- The five coordinates of `j(x, a)` are transcendental.
@isnad1 id=and.1h4v.s9.be910bb512ee from=translated src=- shape=27172dab vocab=5c23bb63
-/
theorem jCoordinates_notMem_bot (hind : AlgebraicIndependent k ![x, a]) :
    x ∉ (⊥ : ClosedIF k K) ∧ x + a ∉ (⊥ : ClosedIF k K) ∧
      x * a ∉ (⊥ : ClosedIF k K) ∧ x + x * a ∉ (⊥ : ClosedIF k K) ∧
      a ∉ (⊥ : ClosedIF k K) := by
  have hx := AlgebraicIndependent.notMem_racl_pair' hind
  have ha0 : a ≠ 0 := fun h ↦ hind.transcendental 1 (by
    change IsAlgebraic k a
    rw [h]
    exact isAlgebraic_zero)
  have ha1 : 1 + a ≠ 0 := fun h ↦ hind.transcendental 1 (by
    rw [show (![x, a] : Fin 2 → K) 1 = algebraMap k K (-1) by
      simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, map_neg, map_one]
      linear_combination h]
    exact isAlgebraic_algebraMap _)
  refine ⟨fun h ↦ hx (racl_mono (Set.empty_subset _)
      (mem_racl_empty_of_isAlgebraic (ClosedIF.mem_bot_iff.1 h))), ?_, ?_, ?_,
    fun h ↦ AlgebraicIndependent.notMem_racl_pair hind (racl_mono (Set.empty_subset _)
      (mem_racl_empty_of_isAlgebraic (ClosedIF.mem_bot_iff.1 h)))⟩
  · refine notMem_bot_of_mem_racl_pair hx ?_
    simpa using sub_mem (mem_pair_left (k := k) (z := x + a) (w := a))
      (mem_pair_right (k := k) (z := x + a) (w := a))
  · refine notMem_bot_of_mem_racl_pair hx ?_
    have := mul_mem (mem_pair_left (k := k) (z := x * a) (w := a))
      (inv_mem (mem_pair_right (k := k) (z := x * a) (w := a)))
    rwa [mul_inv_cancel_right₀ ha0] at this
  · refine notMem_bot_of_mem_racl_pair hx ?_
    have h1 : 1 + a ∈ racl k ({x + x * a, a} : Set K) :=
      add_mem (one_mem _) (mem_pair_right (k := k) (z := x + x * a) (w := a))
    have := mul_mem (mem_pair_left (k := k) (z := x + x * a) (w := a)) (inv_mem h1)
    have key : (x + x * a) * (1 + a)⁻¹ = x := by
      rw [show x + x * a = x * (1 + a) by ring, mul_inv_cancel_right₀ ha1]
    rwa [key] at this

/-- The semantic `j`-tuple `j(x, a) = ([x], [x+a], [xa], [x+xa], [a])` as a
five-tuple of points.-/
def jTupleOf (x a : K) (hind : AlgebraicIndependent k ![x, a]) : Fin 5 → Point k K :=
  ![Point.mk' k x (jCoordinates_notMem_bot hind).1,
    Point.mk' k (x + a) (jCoordinates_notMem_bot hind).2.1,
    Point.mk' k (x * a) (jCoordinates_notMem_bot hind).2.2.1,
    Point.mk' k (x + x * a) (jCoordinates_notMem_bot hind).2.2.2.1,
    Point.mk' k a (jCoordinates_notMem_bot hind).2.2.2.2]

/--
@isnad1 id=eq.1h4v.s7.9e8f3d592528 from=translated src=- shape=534af5c6 vocab=16510fca
-/
@[simp] theorem jTupleOf_zero (hind : AlgebraicIndependent k ![x, a]) :
    (jTupleOf x a hind 0).1 = point k x := rfl

/--
@isnad1 id=eq.1h4v.s7.639157fef213 from=translated src=- shape=eace4065 vocab=a3fadb1e
-/
@[simp] theorem jTupleOf_one (hind : AlgebraicIndependent k ![x, a]) :
    (jTupleOf x a hind 1).1 = point k (x + a) := rfl

/--
@isnad1 id=eq.1h4v.s7.7291ea32ec1c from=translated src=- shape=eace4065 vocab=a20f3a51
-/
@[simp] theorem jTupleOf_two (hind : AlgebraicIndependent k ![x, a]) :
    (jTupleOf x a hind 2).1 = point k (x * a) := rfl

/--
@isnad1 id=eq.1h4v.s7.66976c659f34 from=translated src=- shape=ce7ecac3 vocab=abb5ced0
-/
@[simp] theorem jTupleOf_three (hind : AlgebraicIndependent k ![x, a]) :
    (jTupleOf x a hind 3).1 = point k (x + x * a) := rfl

/--
@isnad1 id=eq.1h4v.s7.a16d1d40b5a0 from=translated src=- shape=d41a76f2 vocab=16510fca
-/
@[simp] theorem jTupleOf_four (hind : AlgebraicIndependent k ![x, a]) :
    (jTupleOf x a hind 4).1 = point k a := rfl

/-- Two `j`-tuples with the same parameter share their parameter point.
@isnad1 id=eq.2h5v.s7.2eef0fd8c270 from=translated src=- shape=0cc55cad vocab=9ab97e8f
-/
theorem jTupleOf_four_eq {x' : K} (hind : AlgebraicIndependent k ![x, a])
    (hind' : AlgebraicIndependent k ![x', a]) :
    jTupleOf x a hind 4 = jTupleOf x' a hind' 4 :=
  Subtype.ext ((jTupleOf_four hind).trans (jTupleOf_four hind').symm)

/-- `jTupleOf x a` is a semantic `j`-tuple.
@isnad1 id=jsem.1h4v.s6.7d0fe652eeb2 from=translated src=- shape=8e67d3e1 vocab=0dba6fcb
-/
theorem jSem_jTupleOf (hind : AlgebraicIndependent k ![x, a]) :
    JSem (jTupleOf x a hind) :=
  ⟨x, a, hind, rfl, rfl, rfl, rfl, rfl⟩

end JTuples

section Normalization

variable {x a : K}

end Normalization

end

end AclGeom
