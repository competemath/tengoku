/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Tengoku.FormalConjectures.FormalConjecturesForMathlib.RingTheory.Ideal.Defs
public import Tengoku

/-!
# Right ideals

This file gives the basic API for right ideals.
-/

@[expose] public section
namespace Tengoku.FormalConjectures end Tengoku.FormalConjectures open Tengoku.FormalConjectures 
universe u

namespace Tengoku.FormalConjectures.RightIdeal

section Semiring

variable {R : Type u} [Semiring R]

/--
@isnad1 id=eq.1h3v.s6.6806bdf01447 from=translated src=- shape=b6dfcf64 vocab=970cc19b
-/
@[ext]
theorem ext {I J : RightIdeal R} (h : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
  Submodule.ext h

/-- A right ideal is closed under multiplication on the right.
@isnad1 id=mem.1h4v.s6.35c7bda5ed93 from=translated src=- shape=b7677467 vocab=b3a77433
-/
theorem mul_mem_right (I : RightIdeal R) {a : R} (b : R) (ha : a ∈ I) : a * b ∈ I :=
  I.smul_mem (MulOpposite.op b) ha

end Semiring

section CommSemiring

variable {R : Type u} [CommSemiring R]

/-- A right ideal in a commutative semiring, regarded as an ideal.-/
def toIdeal (I : RightIdeal R) : Ideal R where
  carrier := (I : Set R)
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' := by
    intro r x hx
    rw [smul_eq_mul, mul_comm]
    exact I.mul_mem_right r hx

/--
@isnad1 id=iff.0h3v.s6.887fc3ff43b6 from=translated src=- shape=51b12b4b vocab=c3dfa646
-/
@[simp]
theorem mem_toIdeal {I : RightIdeal R} {x : R} : x ∈ I.toIdeal ↔ x ∈ I :=
  Iff.rfl

/-- An ideal in a commutative semiring, regarded as a right ideal.-/
def _root_.Ideal.toRightIdeal (I : Ideal R) : RightIdeal R where
  carrier := (I : Set R)
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' := by
    intro r x hx
    rw [MulOpposite.smul_eq_mul_unop, mul_comm]
    exact I.mul_mem_left r.unop hx

/--
@isnad1 id=iff.0h3v.s6.47bae9e4decc from=translated src=- shape=51b12b4b vocab=7aca53e7
-/
@[simp]
theorem _root_.Ideal.mem_toRightIdeal {I : Ideal R} {x : R} :
    x ∈ I.toRightIdeal ↔ x ∈ I :=
  Iff.rfl

/--
@isnad1 id=eq.0h2v.s4.7e6a94fe7918 from=translated src=- shape=2896fe98 vocab=27f61754
-/
@[simp]
theorem toIdeal_toRightIdeal (I : RightIdeal R) : I.toIdeal.toRightIdeal = I :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.b3cf363eb16d from=translated src=- shape=2896fe98 vocab=37c6ef0e
-/
@[simp]
theorem _root_.Ideal.toRightIdeal_toIdeal (I : Ideal R) : I.toRightIdeal.toIdeal = I :=
  rfl

/-- Over a commutative semiring, right ideals and ideals are order isomorphic.-/
def orderIsoIdeal (R : Type u) [CommSemiring R] : RightIdeal R ≃o Ideal R where
  toFun := toIdeal
  invFun := Ideal.toRightIdeal
  left_inv := toIdeal_toRightIdeal
  right_inv := Ideal.toRightIdeal_toIdeal
  map_rel_iff' := Iff.rfl

end CommSemiring

end Tengoku.FormalConjectures.RightIdeal
-- Tengoku: root names of this library moved to Tengoku.FormalConjectures so they do not collide with other libraries (generated)
