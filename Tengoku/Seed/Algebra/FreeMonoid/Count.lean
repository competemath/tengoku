/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.FreeMonoid.Basic
public import Tengoku.Seed.Algebra.Group.TypeTags.Basic

/-!
# `List.count` as a bundled homomorphism

In this file we define `FreeMonoid.countP`, `FreeMonoid.count`, `FreeAddMonoid.countP`, and
`FreeAddMonoid.count`. These are `List.countP` and `List.count` bundled as multiplicative and
additive homomorphisms from `FreeMonoid` and `FreeAddMonoid`.

We do not use `to_additive` too much because it can't map `Multiplicative ℕ` to `ℕ`.
-/

@[expose] public section

variable {α : Type*} (p : α → Prop) [DecidablePred p]

namespace FreeMonoid
/-- `List.countP` lifted to free monoids -/
@[to_additive /-- `List.countP` lifted to free additive monoids -/]
def countP' (l : FreeMonoid α) : ℕ := l.toList.countP p

/--
@isnad1 id=eq.0h2v.s5.6047066f818c from=seed src=0 shape=42d19a8a vocab=978db06d
-/
@[to_additive]
lemma countP'_one : (1 : FreeMonoid α).countP' p = 0 := rfl

/--
@isnad1 id=eq.0h4v.s6.aa4c32d5635a from=seed src=0 shape=7070ced8 vocab=ff0aeee4
-/
@[to_additive]
lemma countP'_mul (l₁ l₂ : FreeMonoid α) : (l₁ * l₂).countP' p = l₁.countP' p + l₂.countP' p := by
  dsimp [countP']
  simp only [List.countP_append]

/-- `List.countP` as a bundled multiplicative monoid homomorphism. -/
def countP : FreeMonoid α →* Multiplicative ℕ where
  toFun := .ofAdd ∘ FreeMonoid.countP' p
  map_one' := by
    simp [countP'_one p]
  map_mul' x y := by
    simp [countP'_mul p]

/--
@isnad1 id=eq.0h3v.s7.4fdc42a1ac80 from=seed src=0 shape=7b814587 vocab=260590ce
-/
theorem countP_apply (l : FreeMonoid α) : l.countP p = .ofAdd (l.toList.countP p) := rfl

/--
@isnad1 id=eq.0h3v.s7.d3c5a74700d9 from=seed src=0 shape=0d96e766 vocab=f1426f82
-/
lemma countP_of (x : α) : (of x).countP p =
    if p x then Multiplicative.ofAdd 1 else Multiplicative.ofAdd 0 := by
  rw [countP_apply, toList_of, List.countP_singleton, apply_ite (Multiplicative.ofAdd)]
  simp only [decide_eq_true_eq]


/-- `List.count` as a bundled additive monoid homomorphism. -/
def count [DecidableEq α] (x : α) : FreeMonoid α →* Multiplicative ℕ := countP (· = x)

/--
@isnad1 id=eq.0h3v.s7.7da202b4baf7 from=seed src=0 shape=d5009abb vocab=af9eda42
-/
theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) :
    count x l = Multiplicative.ofAdd (l.toList.count x) := rfl

/--
@isnad1 id=eq.0h3v.s7.65bf3b8cf02d from=seed src=0 shape=b4cdbbb1 vocab=9c6b7bb7
-/
theorem count_of [DecidableEq α] (x y : α) :
    count x (of y) = Pi.mulSingle (M := fun _ ↦ Multiplicative ℕ) x (Multiplicative.ofAdd 1) y := by
  simp [count, countP_of, Pi.mulSingle_apply]

end FreeMonoid

namespace FreeAddMonoid

/-- `List.countP` as a bundled additive monoid homomorphism. -/
def countP : FreeAddMonoid α →+ ℕ where
  toFun := FreeAddMonoid.countP' p
  map_zero' := countP'_zero p
  map_add' := countP'_add p

/--
@isnad1 id=eq.0h3v.s6.c8ae0e5ff7bb from=seed src=0 shape=0bb5275d vocab=59490163
-/
theorem countP_apply (l : FreeAddMonoid α) : l.countP p = l.toList.countP p := rfl

/--
@isnad1 id=eq.0h3v.s6.6bc986d384b8 from=seed src=0 shape=e04f193d vocab=89131f74
-/
theorem countP_of (x : α) : countP p (of x) = if p x then 1 else 0 := by
  rw [countP_apply, toList_of, List.countP_singleton]
  simp only [decide_eq_true_eq]

/-- `List.count` as a bundled additive monoid homomorphism. -/
-- Porting note: was (x = ·)
def count [DecidableEq α] (x : α) : FreeAddMonoid α →+ ℕ := countP (· = x)

/--
@isnad1 id=eq.0h3v.s6.cc0c5ce22763 from=seed src=0 shape=05b8b05d vocab=67eca597
-/
lemma count_of [DecidableEq α] (x y : α) : count x (of y) = (Pi.single x 1 : α → ℕ) y := by
  dsimp [count]
  rw [countP_of]
  simp [Pi.single, Function.update]

/--
@isnad1 id=eq.0h3v.s6.c380241fa076 from=seed src=0 shape=aafeeb22 vocab=c850aecc
-/
theorem count_apply [DecidableEq α] (x : α) (l : FreeAddMonoid α) : l.count x = l.toList.count x :=
  rfl

end FreeAddMonoid
