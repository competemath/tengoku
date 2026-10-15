/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku

/-!
# Boolean Function Definitions

Core definitions for Boolean functions on the hypercube `Fin n → Bool`,
including bit flips, sensitivity, and local sensitivity.

## Main definitions

* `LeanPoolSensitivity.BoolFun` — a Boolean function on `n` variables.
* `LeanPoolSensitivity.flipBit` — flip the `i`-th coordinate of an input.
* `LeanPoolSensitivity.BoolFun.sensitiveAt` — predicate: `f` changes value when
  flipping coordinate `i` at input `x`.
* `LeanPoolSensitivity.BoolFun.localSensitivity` — the number of sensitive
  coordinates of `f` at a given input.
* `LeanPoolSensitivity.BoolFun.sensitivity` — the maximum local sensitivity
  over all inputs.
* `LeanPoolSensitivity.flipCoords` — flip all bits inside a finite set of
  coordinates simultaneously.
-/

@[expose] public section

namespace LeanPoolSensitivity

/-- A Boolean function on `n` variables, viewed as a map
`(Fin n → Bool) → Bool`. -/
abbrev BoolFun (n : ℕ) := (Fin n → Bool) → Bool

variable {n : ℕ}

/-- Flip the `i`-th bit of an input `x : Fin n → Bool`, leaving all other
coordinates fixed. -/
def flipBit (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

/--
@isnad1 id=eq.0h3v.s4.5107958ebeb7 from=translated src=- shape=a8b1eedc vocab=33643103
-/
@[simp]
theorem flipBit_apply_same (x : Fin n → Bool) (i : Fin n) :
    flipBit x i i = !x i := by
  simp [flipBit]

/--
@isnad1 id=eq.1h4v.s4.5a04f88746e5 from=translated src=- shape=097cc06a vocab=95b77be5
-/
@[simp]
theorem flipBit_apply_ne (x : Fin n → Bool) (i : Fin n) {j : Fin n} (h : j ≠ i) :
    flipBit x i j = x j := by
  simp [flipBit, Function.update_of_ne h]

/--
@isnad1 id=eq.0h3v.s4.3d24a9fe071e from=translated src=- shape=79a02409 vocab=95b77be5
-/
@[simp]
theorem flipBit_flipBit_same (x : Fin n → Bool) (i : Fin n) :
    flipBit (flipBit x i) i = x := by
  ext j
  by_cases h : j = i <;> simp [flipBit, Function.update_of_ne, h, Bool.not_not]

/-- `flipBit x i` is never equal to `x` itself: the `i`-th coordinate
differs.
@isnad1 id=ne.0h3v.s4.c0de1e842181 from=translated src=- shape=8e4cf841 vocab=95b77be5
-/
theorem flipBit_ne_self (x : Fin n → Bool) (i : Fin n) :
    flipBit x i ≠ x := by
  intro h; simp [flipBit] at h

/-- Different coordinates produce different bit flips of `x`.
@isnad1 id=injectiv.0h2v.s4.0abfac5a07f5 from=translated src=- shape=909fc5d6 vocab=b99a6745
-/
theorem flipBit_injective (x : Fin n → Bool) : Function.Injective (flipBit x) := by
  intro i j hij
  by_contra h
  have h1 := flipBit_apply_same x i
  rw [congr_fun hij i, flipBit_apply_ne x j h] at h1
  simp at h1

namespace BoolFun

/-- `f` is sensitive at input `x` in coordinate `i` when flipping bit `i`
changes the value of `f`. -/
def sensitiveAt (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) : Prop :=
  f (flipBit x i) ≠ f x

instance (f : BoolFun n) (x : Fin n → Bool) (i : Fin n) :
    Decidable (f.sensitiveAt x i) :=
  inferInstanceAs (Decidable (f (flipBit x i) ≠ f x))

/-- The local sensitivity of `f` at input `x`: number of coordinates `i` at
which `f` is sensitive. -/
def localSensitivity (f : BoolFun n) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => f.sensitiveAt x i).card

/-- The sensitivity of `f`: the maximum of `f.localSensitivity x` over all
inputs `x`. -/
noncomputable def sensitivity (f : BoolFun n) : ℕ :=
  Finset.univ.sup (fun x => f.localSensitivity x)

/-- The sensitivity of any Boolean function on `n` variables is at most `n`.
@isnad1 id=le.0h2v.s3.738196088548 from=translated src=- shape=26d77ceb vocab=78a2fe6f
-/
theorem sensitivity_le (f : BoolFun n) : f.sensitivity ≤ n := by
  apply Finset.sup_le
  intro x _
  unfold localSensitivity
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The local sensitivity at any specific input is bounded above by the
sensitivity of `f`.
@isnad1 id=le.0h3v.s4.70a79cb16a46 from=translated src=- shape=376878f3 vocab=fb89701c
-/
theorem localSensitivity_le_sensitivity (f : BoolFun n) (x : Fin n → Bool) :
    f.localSensitivity x ≤ f.sensitivity := by
  exact Finset.le_sup (f := fun x => f.localSensitivity x) (Finset.mem_univ x)

end BoolFun

/-- Flip all bits whose index lies in the finite set `S`, leaving the
remaining coordinates fixed. -/
def flipCoords (x : Fin n → Bool) (S : Finset (Fin n)) : Fin n → Bool :=
  fun j => if j ∈ S then !x j else x j

end LeanPoolSensitivity
