/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Tengoku.T3ModelCompanion.T3.GroupTheory.Free.Basic
public import Tengoku.T3ModelCompanion.T3.GroupTheory.Free.Model
public import Tengoku.Seed.GroupTheory.Nilpotent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Comparing the free exponent-three group with the coordinate model

The universal property of `T3.Free I` gives a homomorphism to `T3.LvdW I` sending each
free generator to its coordinate vector. Pulling back the coordinate calculations proves
that two distinct generators do not commute and that three distinct generators have a
nontrivial triple commutator.

These are separation results used in the proof of the paper's finite normal form. They do not
identify the free group with the full coordinate model, or establish the normal form by themselves.

## Main definitions

* `T3.Free.toLvdW`: the comparison homomorphism `T3.Free I →* T3.LvdW I`.

## Main results

* `T3.Free.commutator_of_ne_one`: two distinct free generators do not commute.
* `T3.Free.triple_commutator_of_ne_one`: three distinct free generators have a nontrivial
  triple commutator.
* `T3.Free.lowerCentralSeries_two_ne_bot`: the third lower central term is nontrivial
  when three distinct generators are available.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
Primary source: Levi–van der Waerden (1933), p. 156, equations (8)–(9) and Satz 1.
-/

@[expose] public section

namespace T3

open scoped commutatorElement

namespace Free

variable {I : Type*}

section DecidableEq

variable [DecidableEq I]

/-- The comparison map, sending each free generator to its model element.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.-/
def toLvdW : Free I →* LvdW I :=
  Free.lift LvdW.pow_three LvdW.of

/-- The comparison map sends a free generator to the corresponding coordinate vector.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
@isnad1 id=eq.0h2v.s6.23a924d0b98e from=translated src=- shape=a3711954 vocab=359bc907
-/
@[simp]
theorem toLvdW_of (i : I) : toLvdW (Free.of i) = LvdW.of i :=
  Free.lift_of _ _ i

end DecidableEq

/-- Two distinct generators of the free exponent-three group do not commute.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
@isnad1 id=ne.1h3v.s6.4710c1a0291f from=translated src=- shape=d8354b5d vocab=7ec0042d
-/
theorem commutator_of_ne_one {i j : I} (hij : i ≠ j) :
    ⁅Free.of i, Free.of j⁆ ≠ (1 : Free I) := by
  classical
  intro h
  have hmap : ⁅LvdW.of i, LvdW.of j⁆ = (1 : LvdW I) := by
    rw [← toLvdW_of i, ← toLvdW_of j, ← map_commutatorElement, h, map_one]
  have hcoord := LvdW.commutator_pair (LvdW.of i) (LvdW.of j) i j
  rw [hmap, LvdW.one_pair, LvdW.of_gen_self, LvdW.of_gen_self, LvdW.of_gen_of_ne hij,
    LvdW.of_gen_of_ne hij.symm] at hcoord
  exact zero_ne_one (by linear_combination hcoord)

/--
Three distinct free generators have a nontrivial triple commutator.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
@isnad1 id=ne.3h4v.s6.e1ae5d47d3a1 from=translated src=- shape=99f14a57 vocab=7ec0042d
-/
theorem triple_commutator_of_ne_one {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅⁅Free.of i, Free.of j⁆, Free.of k⁆ ≠ (1 : Free I) := by
  classical
  intro h
  refine LvdW.triple_commutator_of_ne_one hij hik hjk ?_
  rw [← toLvdW_of i, ← toLvdW_of j, ← toLvdW_of k, ← map_commutatorElement,
    ← map_commutatorElement, h, map_one]

/--
With three distinct generators available, the third lower central term is nontrivial.
Mathlib numbers this term by `2`, whereas the paper denotes it by `γ₃`.

Paper-ID: preliminaries.finite_normal_form
TeX: T3_modelcompanion_v9.tex, `fact:Levi and van der Waerden`, v9 Fact 2.27.
@isnad1 id=ne.3h4v.s7.b9f2dcf7a123 from=translated src=- shape=b969cd80 vocab=3db818b0
-/
theorem lowerCentralSeries_two_ne_bot {i j k : I} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (⊤ : Subgroup (Free I)).lowerCentralSeries 2 ≠ ⊥ := by
  intro h
  refine triple_commutator_of_ne_one hij hik hjk ?_
  rw [← Subgroup.mem_bot, ← h]
  simp only [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
  exact Subgroup.commutator_mem_commutator
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    (Subgroup.mem_top _)

end Free

end T3
