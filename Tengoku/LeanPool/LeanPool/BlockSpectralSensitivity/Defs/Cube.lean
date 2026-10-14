/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import Tengoku

/-!
# The Boolean cube

An *input* on a finite coordinate set `V` is a map `V → Bool`.  For `A : Finset V`
we write `flipSet x A` for the input `x^A` of Section 1 of `bs_lambda.txt`, obtained by
flipping every coordinate of `A`.

Hamming distance is taken from Mathlib (`hammingDist`).

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

@[expose] public section

/-- The symmetric difference of two distinct singletons is the corresponding pair.  This is a
general `Finset` fact, stated here because Mathlib does not have it.
@isnad1 id=eq.1h3v.s5.d8b44d4ca250 from=translated src=- shape=e2b9e2d9 vocab=beaa6940
-/
theorem Finset.symmDiff_singleton_singleton {α : Type*} [DecidableEq α] {p q : α} (hpq : p ≠ q) :
    symmDiff ({p} : Finset α) {q} = {p, q} := by
  ext v
  by_cases h1 : v = p <;> by_cases h2 : v = q <;> simp_all [Finset.mem_symmDiff]

namespace BSLambda

/-- An input to a Boolean function on the coordinate set `V`. -/
abbrev Input (V : Type*) : Type _ := V → Bool

/-- The all-zero input, written `0^V` in `bs_lambda.txt`. -/
def zeroInput (V : Type*) : Input V := fun _ ↦ false

/--
@isnad1 id=eq.0h2v.s3.15814083a948 from=translated src=- shape=d08a88ea vocab=70f64658
-/
@[simp] lemma zeroInput_apply {V : Type*} (v : V) : zeroInput V v = false := rfl

variable {V : Type*}

section DecEq
variable [DecidableEq V]

/-- `flipSet x A` is the input written `x^A` in the source document: it flips every
coordinate lying in `A` and leaves all other coordinates unchanged. -/
def flipSet (x : Input V) (A : Finset V) : Input V := fun v ↦ if v ∈ A then !x v else x v

/--
@isnad1 id=eq.1h4v.s5.db8159714173 from=translated src=- shape=2071d718 vocab=41d468ca
-/
@[simp] lemma flipSet_apply_of_mem {x : Input V} {A : Finset V} {v : V} (hv : v ∈ A) :
    flipSet x A v = !x v := by simp [flipSet, hv]

/--
@isnad1 id=eq.1h4v.s5.c5c287ee0cb8 from=translated src=- shape=ff53519a vocab=c0891521
-/
@[simp] lemma flipSet_apply_of_notMem {x : Input V} {A : Finset V} {v : V} (hv : v ∉ A) :
    flipSet x A v = x v := by simp [flipSet, hv]

/-- A coordinate survives `flipSet` exactly when it lies outside the flipped set.
@isnad1 id=iff.0h4v.s5.fe389983a1e1 from=translated src=- shape=50d02a76 vocab=c0891521
-/
@[simp] lemma flipSet_apply_eq_self_iff {x : Input V} {A : Finset V} {v : V} :
    flipSet x A v = x v ↔ v ∉ A := by
  by_cases hv : v ∈ A <;> simp [flipSet, hv]

/-- A coordinate is changed by `flipSet` exactly when it lies in the flipped set.
@isnad1 id=iff.0h4v.s5.da76d2f1eebe from=translated src=- shape=45a5d38a vocab=c0891521
-/
lemma flipSet_apply_ne_self_iff {x : Input V} {A : Finset V} {v : V} :
    flipSet x A v ≠ x v ↔ v ∈ A := by
  simp

/-- An input differs from its flip at every flipped coordinate.
@isnad1 id=ne.1h4v.s5.ea735c5b592b from=translated src=- shape=c64fa118 vocab=c0891521
-/
lemma ne_flipSet_apply {x : Input V} {A : Finset V} {v : V} (hv : v ∈ A) :
    x v ≠ flipSet x A v := (flipSet_apply_ne_self_iff.2 hv).symm

/--
@isnad1 id=eq.0h2v.s4.be9d52abd1e8 from=translated src=- shape=2e10b822 vocab=11151f91
-/
@[simp] lemma flipSet_empty (x : Input V) : flipSet x ∅ = x := by
  funext v
  simp [flipSet]

/-- Flipping `A` and then `B` flips exactly the coordinates of the symmetric difference.
@isnad1 id=eq.0h4v.s5.fc9741debc2d from=translated src=- shape=3a910230 vocab=f87829b4
-/
lemma flipSet_flipSet_symmDiff (x : Input V) (A B : Finset V) :
    flipSet (flipSet x A) B = flipSet x (symmDiff A B) := by
  funext v
  by_cases hA : v ∈ A <;> by_cases hB : v ∈ B <;> simp [flipSet, hA, hB, Finset.mem_symmDiff]

/--
@isnad1 id=eq.0h3v.s4.d4498d62c775 from=translated src=- shape=edce711b vocab=8af13b2c
-/
@[simp] lemma flipSet_flipSet (x : Input V) (A : Finset V) : flipSet (flipSet x A) A = x := by
  rw [flipSet_flipSet_symmDiff, symmDiff_self, Finset.bot_eq_empty, flipSet_empty]

/-- Flipping two distinct coordinates one after the other is the same as flipping the pair
at once.
@isnad1 id=eq.1h4v.s5.b418b3abf40e from=translated src=- shape=1c88182f vocab=94bd7306
-/
lemma flipSet_singleton_flipSet_singleton (x : Input V) {p q : V} (hpq : p ≠ q) :
    flipSet (flipSet x {p}) {q} = flipSet x {p, q} := by
  rw [flipSet_flipSet_symmDiff, Finset.symmDiff_singleton_singleton hpq]

/-- Undoing one half of a pair flip leaves the single flip at the other coordinate: this is
the "other midpoint" identity behind every two-midpoint argument.
@isnad1 id=eq.1h4v.s5.87dc03818508 from=translated src=- shape=f63b0359 vocab=94bd7306
-/
lemma flipSet_pair_flipSet_singleton (x : Input V) {p q : V} (hpq : p ≠ q) :
    flipSet (flipSet x {p, q}) {q} = flipSet x {p} := by
  rw [← flipSet_singleton_flipSet_singleton x hpq, flipSet_flipSet]

/-- Flipping a fixed set of coordinates is injective in the input.
@isnad1 id=injectiv.0h2v.s4.d0e126ee3388 from=translated src=- shape=50ce28c2 vocab=fadd34ca
-/
lemma flipSet_left_injective (A : Finset V) : Function.Injective (flipSet · A) := by
  intro x y h
  simpa using congrArg (flipSet · A) h

/--
@isnad1 id=iff.0h4v.s5.95c040ee9984 from=translated src=- shape=de5704cc vocab=8af13b2c
-/
@[simp] lemma flipSet_left_inj {x y : Input V} {A : Finset V} :
    flipSet x A = flipSet y A ↔ x = y :=
  (flipSet_left_injective A).eq_iff

/-- Distinct coordinates give distinct single-coordinate flips of a fixed input.
@isnad1 id=injectiv.0h2v.s4.b9615f2fa932 from=translated src=- shape=67b3db2e vocab=1a96dd6c
-/
lemma flipSet_singleton_injective (x : Input V) :
    Function.Injective fun v : V ↦ flipSet x {v} := fun v w h ↦ by
  by_contra hvw
  simpa [hvw] using congrFun h v

/-- The flipped coordinate of a single-coordinate flip.
@isnad1 id=eq.0h3v.s4.0bd97b681e03 from=translated src=- shape=014c1ca0 vocab=20097c48
-/
lemma flipSet_singleton_self (x : Input V) (v : V) : flipSet x {v} v = !x v := by
  simp

/-- Flipping a set of coordinates of the all-zero input yields its indicator function.
@isnad1 id=eq.0h3v.s5.41e750d54c1c from=translated src=- shape=00c53435 vocab=fb3957d1
-/
@[simp] lemma flipSet_zeroInput_apply (A : Finset V) (v : V) :
    flipSet (zeroInput V) A v = decide (v ∈ A) := by
  simp [flipSet]

end DecEq

section Fintype
variable [Fintype V] [DecidableEq V]

/-- The Hamming distance from `x` to `x^A` is exactly `A.card`.
@isnad1 id=eq.0h3v.s5.09a493c4b19d from=translated src=- shape=e67ab9b4 vocab=b7ad067b
-/
@[simp] lemma hammingDist_flipSet (x : Input V) (A : Finset V) :
    hammingDist x (flipSet x A) = A.card := by
  simp only [hammingDist, ne_comm (a := x _), flipSet_apply_ne_self_iff,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- Two flips of the same input differ exactly on the symmetric difference of the flipped
sets.
@isnad1 id=eq.0h4v.s5.a033f765134d from=translated src=- shape=67408d90 vocab=2965fbdb
-/
lemma hammingDist_flipSet_flipSet (x : Input V) (A B : Finset V) :
    hammingDist (flipSet x A) (flipSet x B) = (symmDiff A B).card := by
  have h : flipSet x B = flipSet (flipSet x A) (symmDiff A B) := by
    rw [flipSet_flipSet_symmDiff, symmDiff_symmDiff_cancel_left]
  rw [h, hammingDist_flipSet]

/-- Every input is a flip of every other, at the set of coordinates where they differ.
@isnad1 id=eq.0h3v.s5.f279426e12ed from=translated src=- shape=2285195c vocab=0c18a4b1
-/
lemma flipSet_filter_ne (x y : Input V) :
    flipSet x (Finset.univ.filter fun v ↦ x v ≠ y v) = y := by
  funext v
  by_cases h : x v = y v <;> simp [flipSet, h, Bool.eq_not_iff]

/-- Two inputs at Hamming distance `1` differ in exactly one coordinate.
@isnad1 id=ex.1h3v.s5.d408c642a3a0 from=translated src=- shape=2ef476da vocab=3ab0443e
-/
lemma exists_eq_flipSet_singleton_of_hammingDist_eq_one {x y : Input V}
    (h : hammingDist x y = 1) : ∃ v, y = flipSet x {v} := by
  obtain ⟨v, hv⟩ := Finset.card_eq_one.1 h
  exact ⟨v, (hv ▸ flipSet_filter_ne x y).symm⟩

/--
@isnad1 id=eq.0h3v.s5.0907e42e23d1 from=translated src=- shape=0199afcf vocab=3ab0443e
-/
lemma hammingDist_flipSet_singleton (x : Input V) (v : V) : hammingDist x (flipSet x {v}) = 1 := by
  simp

end Fintype

end BSLambda
