/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Module.LocalizedModule.Basic

/-!
# API for localized modules away from an element

We provide some specialized API for the localization of a module away from an element.
-/

public section

namespace IsLocalizedModule.Away

variable {R : Type*} [CommSemiring R] {M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module R N] {f : M →ₗ[R] N} {r : R}

/--
@isnad1 id=away.3h5v.s9.ea7e692198b7 from=seed src=0 shape=3ed2b0de vocab=2da239f2
-/
lemma mk (h₁ : IsUnit (algebraMap R (Module.End R N) r))
    (h₂ : ∀ (x : N), ∃ (n : ℕ) (y : M), r ^ n • x = f y)
    (h₃ : ∀ (x y : M), f x = f y → ∃ (n : ℕ), r ^ n • x = r ^ n • y) :
    IsLocalizedModule.Away r f where
  map_units := fun ⟨_, ⟨n, rfl⟩⟩ ↦ by simp [h₁.pow]
  surj x := by
    obtain ⟨n, y, hy⟩ := h₂ x
    use ⟨y, ⟨_, n, rfl⟩⟩, hy
  exists_of_eq {x y} hxy := by
    obtain ⟨n, hn⟩ := h₃ _ _ hxy
    use ⟨_, n, rfl⟩, hn

/--
@isnad1 id=away.3h5v.s9.df3a8ffe7bf2 from=seed src=0 shape=88c225ed vocab=c52d8833
-/
lemma mk_of_addCommGroup {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {f : M →ₗ[R] N} {r : R} (h₁ : IsUnit (algebraMap R (Module.End R N) r))
    (h₂ : ∀ (x : N), ∃ (n : ℕ) (y : M), r ^ n • x = f y)
    (h₃ : ∀ (x : M), f x = 0 → ∃ (n : ℕ), r ^ n • x = 0) :
    IsLocalizedModule.Away r f := by
  refine IsLocalizedModule.Away.mk h₁ h₂ fun x y hxy ↦ ?_
  have : f (x - y) = 0 := by simp [hxy]
  obtain ⟨n, hn⟩ := h₃ _ this
  use n
  simpa [smul_sub, sub_eq_zero] using hn

variable (r) [IsLocalizedModule.Away r f]

variable (f) in
include f in
/--
@isnad1 id=isunit.0h5v.s7.9d5914a1483a from=seed src=0 shape=a29a976a vocab=855f971b
-/
lemma isUnit_algebraMap : IsUnit (algebraMap R (Module.End R N) r) :=
  IsLocalizedModule.map_units (S := .powers r) f ⟨_, 1, by simp⟩

/--
@isnad1 id=ex.1h7v.s8.226947e08485 from=seed src=0 shape=b8d56a24 vocab=c2bf2708
-/
lemma exists_of_eq {x y : M} (h : f x = f y) : ∃ (n : ℕ), r ^ n • x = r ^ n • y := by
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalizedModule.exists_of_eq (S := .powers r) h
  use n, hn

variable (f) in
/--
@isnad1 id=ex.0h6v.s7.2a9211d7faf5 from=seed src=0 shape=3e00a119 vocab=c2bf2708
-/
lemma surj (y : N) : ∃ (n : ℕ) (x : M), r ^ n • y = f x := by
  obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalizedModule.surj (S := .powers r) f y
  use n, x, h

/--
@isnad1 id=away.1h6v.s6.21d3e69d697c from=seed src=0 shape=aaf57d60 vocab=6607bc4f
-/
lemma of_associated {r r' : R} (h : Associated r r') [IsLocalizedModule.Away r f] :
    IsLocalizedModule.Away r' f := by
  obtain ⟨u, rfl⟩ := h
  rw [mul_comm]
  refine .mk ?_ ?_ ?_
  · simp [IsUnit.mul, isUnit_algebraMap f r, u.isUnit.map _]
  · intro y
    obtain ⟨n, x, hx⟩ := surj f r y
    use n, (u ^ n) • x
    simp [mul_pow, ← hx, mul_smul, Units.smul_def]
  · intro x y hxy
    obtain ⟨n, hn⟩ := exists_of_eq r hxy
    use n
    simp [mul_pow, mul_smul, hn]

/--
@isnad1 id=iff.1h6v.s6.68bb185d57dd from=seed src=0 shape=ca84d60d vocab=6607bc4f
-/
lemma iff_of_associated {r r' : R} (h : Associated r r') :
    IsLocalizedModule.Away r f ↔ IsLocalizedModule.Away r' f :=
  ⟨fun _ ↦ .of_associated h, fun _ ↦ .of_associated h.symm⟩

end IsLocalizedModule.Away
