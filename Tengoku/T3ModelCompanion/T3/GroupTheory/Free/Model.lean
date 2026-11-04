/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Tengoku.Seed.Algebra.Group.Commutator
public import Tengoku.Seed.Algebra.Group.MinimalAxioms
public import Tengoku.Seed.Data.ZMod.Basic
public import Tengoku.Seed.Tactic.LinearCombination
public import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A coordinate model for the Levi–van der Waerden normal form

Levi and van der Waerden (1933), pp. 155–156, use generators `aᵢ`, commutators
`aᵢ,ⱼ = ⁅aᵢ, aⱼ⁆`, and triple commutators `aᵢ,ⱼ,ₖ = ⁅⁅aᵢ, aⱼ⁆, aₖ⁆`.
Their composition law (9) on p. 156 gives the multiplication below. Its group axioms,
inverse formula, and cube identity are verified directly over `ZMod 3`.

`LvdW I` has coordinates at every pair and triple of indices. The same polynomial formulas
work without an order on `I`; when the indices are ordered, restriction to increasing
coordinates recovers the formulas of the source. This larger coordinate group is a comparison
model, not a definition of the free group or a claim that the free group fills all coordinates.
It supplies the coordinate calculations used in proving the paper's normal form.

## Main definitions

* `T3.LvdW`: the coordinate systems, with the group structure given by law (9).
* `T3.LvdW.of`: the element corresponding to a generator.

## Main results

* `T3.LvdW.pow_three`: every model element has cube one.
* `T3.LvdW.commutator_pair`: the degree-two coordinate is a `2 × 2` determinant.
* `T3.LvdW.triple_commutator_triple`: the degree-three coordinate of a triple commutator
  is a `3 × 3` determinant.
* `T3.LvdW.triple_commutator_of_ne_one`: three distinct indices give a nontrivial
  triple commutator.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
Primary source: Levi–van der Waerden (1933), pp. 155–156, equations (5)–(9).
-/

@[expose] public section

namespace T3

open scoped commutatorElement

/--
A coordinate system over `ZMod 3`, with arbitrary generator, pair, and triple coordinates.
This is an auxiliary comparison model for the normal form.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.-/
@[ext]
structure LvdW (I : Type*) where
  /-- The exponent `cⁱ` of the generator `aᵢ`.-/
  gen : I → ZMod 3
  /-- The exponent `cⁱ'ʲ` of the double commutator `aᵢ,ⱼ`.-/
  pair : I → I → ZMod 3
  /-- The exponent `cⁱ'ʲ'ᵏ` of the triple commutator `aᵢ,ⱼ,ₖ`.-/
  triple : I → I → I → ZMod 3

namespace LvdW

variable {I : Type*}

/-- The characteristic of the coefficient ring, which every law below is only valid modulo.
@isnad1 id=eq.0h0v.s6.2fbb535c49ec from=translated src=- shape=f9dc6c31 vocab=c87b9854
-/
protected theorem three_eq_zero : (3 : ZMod 3) = 0 := by decide

/-- Law (9) of Levi–van der Waerden (1933), p. 156, applied to all index tuples.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.-/
instance : Mul (LvdW I) where
  mul x y :=
    { gen := fun i => x.gen i + y.gen i
      pair := fun i j => x.pair i j + y.pair i j - x.gen j * y.gen i
      triple := fun i j k =>
        x.triple i j k + y.triple i j k + x.pair i j * y.gen k - x.pair i k * y.gen j
          + (x.pair j k - x.gen j * x.gen k - x.gen j * y.gen k + x.gen k * y.gen j) * y.gen i }

/--
@isnad1 id=eq.0h4v.s6.0e1e3f9166a0 from=translated src=- shape=836b8217 vocab=6d387d53
-/
@[simp]
theorem mul_gen (x y : LvdW I) (i : I) : (x * y).gen i = x.gen i + y.gen i := rfl

/--
@isnad1 id=eq.0h5v.s7.c1d986220cc8 from=translated src=- shape=6bcba905 vocab=0b30d821
-/
@[simp]
theorem mul_pair (x y : LvdW I) (i j : I) :
    (x * y).pair i j = x.pair i j + y.pair i j - x.gen j * y.gen i := rfl

/--
@isnad1 id=eq.0h6v.s9.6c2693d7985a from=translated src=- shape=1c66fe74 vocab=c7b283fd
-/
@[simp]
theorem mul_triple (x y : LvdW I) (i j k : I) :
    (x * y).triple i j k =
      x.triple i j k + y.triple i j k + x.pair i j * y.gen k - x.pair i k * y.gen j
        + (x.pair j k - x.gen j * x.gen k - x.gen j * y.gen k + x.gen k * y.gen j) * y.gen i :=
  rfl

/-- The empty exponent system.-/
instance : One (LvdW I) where
  one := { gen := fun _ => 0, pair := fun _ _ => 0, triple := fun _ _ _ => 0 }

/--
@isnad1 id=eq.0h2v.s6.310ef7746e73 from=translated src=- shape=e6fa87ec vocab=0562f58a
-/
@[simp] theorem one_gen (i : I) : (1 : LvdW I).gen i = 0 := rfl

/--
@isnad1 id=eq.0h3v.s6.eebd59747b19 from=translated src=- shape=ebf9e7f7 vocab=6bbcf9e3
-/
@[simp] theorem one_pair (i j : I) : (1 : LvdW I).pair i j = 0 := rfl

/--
@isnad1 id=eq.0h4v.s6.1616a025d43f from=translated src=- shape=8dc2cd70 vocab=ea0d032e
-/
@[simp] theorem one_triple (i j k : I) : (1 : LvdW I).triple i j k = 0 := rfl

/-- The inverse formula of Levi–van der Waerden (1933), p. 156, below law (9).

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.-/
instance : Inv (LvdW I) where
  inv x :=
    { gen := fun i => -x.gen i
      pair := fun i j => -x.pair i j - x.gen i * x.gen j
      triple := fun i j k =>
        -x.triple i j k + x.pair i j * x.gen k - x.pair i k * x.gen j + x.pair j k * x.gen i
          - x.gen i * x.gen j * x.gen k }

/--
@isnad1 id=eq.0h3v.s6.fdef9f661468 from=translated src=- shape=082e4434 vocab=c596564b
-/
@[simp] theorem inv_gen (x : LvdW I) (i : I) : x⁻¹.gen i = -x.gen i := rfl

/--
@isnad1 id=eq.0h4v.s7.5a95ee6cf4a4 from=translated src=- shape=9800ef31 vocab=039d32f2
-/
@[simp]
theorem inv_pair (x : LvdW I) (i j : I) : x⁻¹.pair i j = -x.pair i j - x.gen i * x.gen j := rfl

/--
@isnad1 id=eq.0h5v.s9.ebe1a2f53da8 from=translated src=- shape=c5600f88 vocab=345a2f5e
-/
@[simp]
theorem inv_triple (x : LvdW I) (i j k : I) :
    x⁻¹.triple i j k =
      -x.triple i j k + x.pair i j * x.gen k - x.pair i k * x.gen j + x.pair j k * x.gen i
        - x.gen i * x.gen j * x.gen k :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.8f4f0257c0df from=translated src=- shape=580dae18 vocab=c9cdd342
-/
protected theorem mul_assoc' (x y z : LvdW I) : x * y * z = x * (y * z) := by
  refine LvdW.ext (funext fun i => ?_) (funext fun i => funext fun j => ?_)
    (funext fun i => funext fun j => funext fun k => ?_)
  · simp only [mul_gen]; ring
  · simp only [mul_gen, mul_pair]; ring
  · simp only [mul_gen, mul_pair, mul_triple]
    linear_combination (-(x.gen k * y.gen j * z.gen i)) * LvdW.three_eq_zero

/--
@isnad1 id=eq.0h2v.s4.716f5086954f from=translated src=- shape=95f936d5 vocab=c9cdd342
-/
protected theorem one_mul' (x : LvdW I) : 1 * x = x := by
  refine LvdW.ext (funext fun i => ?_) (funext fun i => funext fun j => ?_)
    (funext fun i => funext fun j => funext fun k => ?_)
  · simp only [mul_gen, one_gen]; ring
  · simp only [mul_pair, one_gen, one_pair]; ring
  · simp only [mul_triple, one_gen, one_pair, one_triple]; ring

/--
@isnad1 id=eq.0h2v.s5.e174d1cb1ea5 from=translated src=- shape=4e969cce vocab=81f10049
-/
protected theorem inv_mul_cancel' (x : LvdW I) : x⁻¹ * x = 1 := by
  refine LvdW.ext (funext fun i => ?_) (funext fun i => funext fun j => ?_)
    (funext fun i => funext fun j => funext fun k => ?_)
  · simp only [mul_gen, inv_gen, one_gen]; ring
  · simp only [mul_pair, inv_gen, inv_pair, one_pair]; ring
  · simp only [mul_triple, inv_gen, inv_pair, inv_triple, one_triple]
    linear_combination (-(x.gen i * x.gen j * x.gen k)) * LvdW.three_eq_zero

instance : Group (LvdW I) := Group.ofLeftAxioms LvdW.mul_assoc' LvdW.one_mul' LvdW.inv_mul_cancel'

/-- Every model element has cube one, as in Levi–van der Waerden (1933), p. 156.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
@isnad1 id=eq.0h2v.s5.110e55fd4f4e from=translated src=- shape=9aeecc42 vocab=1d37b55b
-/
theorem pow_three (x : LvdW I) : x ^ 3 = 1 := by
  rw [pow_succ, pow_succ, pow_one]
  refine LvdW.ext (funext fun i => ?_) (funext fun i => funext fun j => ?_)
    (funext fun i => funext fun j => funext fun k => ?_)
  · simp only [mul_gen, one_gen]
    linear_combination (x.gen i) * LvdW.three_eq_zero
  · simp only [mul_gen, mul_pair, one_pair]
    linear_combination (x.pair i j - x.gen i * x.gen j) * LvdW.three_eq_zero
  · simp only [mul_gen, mul_pair, mul_triple, one_triple]
    linear_combination (x.triple i j k + x.gen i * x.pair j k - x.gen j * x.pair i k
      + x.gen k * x.pair i j - 2 * (x.gen i * x.gen j * x.gen k)) * LvdW.three_eq_zero

/-! ### Commutators

A commutator has degree-two coordinates given by `2 × 2` determinants of generator
coordinates. A triple commutator has zero coordinates in degrees one and two, and its degree-three
coordinates are `3 × 3` determinants. These calculations will distinguish the commutator
coefficients in the free group's collected normal form.
-/

/--
@isnad1 id=eq.0h4v.s6.ce317f91c5d6 from=translated src=- shape=bd62f56e vocab=da110e82
-/
@[simp]
theorem commutator_gen (x y : LvdW I) (i : I) : ⁅x, y⁆.gen i = 0 := by
  simp only [commutatorElement_def, mul_gen, inv_gen]; ring

/-- The pair coordinate of a commutator is the determinant of its generator coordinates.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
@isnad1 id=eq.0h5v.s7.4324a5c38604 from=translated src=- shape=649b87a7 vocab=020975f9
-/
theorem commutator_pair (x y : LvdW I) (i j : I) :
    ⁅x, y⁆.pair i j = x.gen i * y.gen j - x.gen j * y.gen i := by
  simp only [commutatorElement_def, mul_gen, mul_pair, inv_gen, inv_pair]; ring

/--
@isnad1 id=eq.0h5v.s6.941255449ac4 from=translated src=- shape=596eaae9 vocab=da110e82
-/
theorem triple_commutator_gen (x y z : LvdW I) (i : I) : ⁅⁅x, y⁆, z⁆.gen i = 0 :=
  commutator_gen _ z i

/--
@isnad1 id=eq.0h6v.s6.a970c3bc3ab8 from=translated src=- shape=02f337a3 vocab=c7c27de3
-/
theorem triple_commutator_pair (x y z : LvdW I) (i j : I) : ⁅⁅x, y⁆, z⁆.pair i j = 0 := by
  rw [commutator_pair, commutator_gen, commutator_gen]; ring

/--
The triple coordinate of a triple commutator is the determinant of the generator coordinates.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
@isnad1 id=eq.0h7v.s9.f5a61e48f675 from=translated src=- shape=191077b7 vocab=26f55345
-/
theorem triple_commutator_triple (x y z : LvdW I) (i j k : I) :
    ⁅⁅x, y⁆, z⁆.triple i j k =
      x.gen i * (y.gen j * z.gen k - y.gen k * z.gen j)
        - x.gen j * (y.gen i * z.gen k - y.gen k * z.gen i)
        + x.gen k * (y.gen i * z.gen j - y.gen j * z.gen i) := by
  simp only [commutatorElement_def, mul_gen, mul_pair, mul_triple, inv_gen, inv_pair, inv_triple]
  ring

/-! ### Generators -/

variable [DecidableEq I]

/-- The model element corresponding to a free generator.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.-/
def of (i : I) : LvdW I where
  gen j := if j = i then 1 else 0
  pair _ _ := 0
  triple _ _ _ := 0

/--
@isnad1 id=eq.0h3v.s7.b9893b29f312 from=translated src=- shape=6bc4173f vocab=8ccbba14
-/
theorem of_gen (i j : I) : (of i).gen j = if j = i then 1 else 0 := rfl

/--
@isnad1 id=eq.0h2v.s6.4ee42b1f1c22 from=translated src=- shape=60341fee vocab=58d7a60e
-/
@[simp] theorem of_gen_self (i : I) : (of i).gen i = 1 := ite_eq_left rfl

/--
@isnad1 id=eq.1h3v.s6.7434b94cd8e0 from=translated src=- shape=63b10539 vocab=58d7a60e
-/
theorem of_gen_of_ne {i j : I} (h : j ≠ i) : (of i).gen j = 0 := ite_eq_right h

/--
@isnad1 id=eq.0h4v.s6.8f6542e88114 from=translated src=- shape=fbfc142d vocab=5e6c4839
-/
@[simp] theorem of_pair (i j k : I) : (of i).pair j k = 0 := rfl

/--
@isnad1 id=eq.0h5v.s6.9e3decefe6c9 from=translated src=- shape=5fc174db vocab=a3a004fe
-/
@[simp] theorem of_triple (i j k l : I) : (of i).triple j k l = 0 := rfl

/-- Three distinct generator elements have a triple commutator with triple coordinate `1`.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
@isnad1 id=eq.3h4v.s6.142af8747ff9 from=translated src=- shape=1b172bae vocab=86e7b0c7
-/
theorem triple_commutator_of_triple {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅⁅of i, of j⁆, of k⁆.triple i j k = 1 := by
  rw [triple_commutator_triple, of_gen_self, of_gen_self, of_gen_self,
    of_gen_of_ne hij.symm, of_gen_of_ne hik.symm, of_gen_of_ne hij, of_gen_of_ne hjk.symm,
    of_gen_of_ne hik, of_gen_of_ne hjk]
  ring

/--
Three distinct generator elements have a nontrivial triple commutator.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
@isnad1 id=ne.3h4v.s6.a9d783d1f020 from=translated src=- shape=d3350a19 vocab=60969a42
-/
theorem triple_commutator_of_ne_one {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅⁅of i, of j⁆, of k⁆ ≠ 1 := by
  intro h
  have := triple_commutator_of_triple hij hik hjk
  rw [h, one_triple] at this
  exact zero_ne_one this

end LvdW

end T3
