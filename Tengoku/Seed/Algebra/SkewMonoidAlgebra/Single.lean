/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos Fernández, Xavier Généreux
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.SkewMonoidAlgebra.Basic
/-!
# Modifying skew monoid algebra at exactly one point

This file contains basic results on updating/erasing an element of a skew monoid algebra using
one point of the domain.
-/

@[expose] public section

noncomputable section

namespace SkewMonoidAlgebra

variable {k G H : Type*}

section erase

variable {M α : Type*} [AddCommMonoid M] (a a' : α) (b : M) (f : SkewMonoidAlgebra M α)

/--
Given an element `f` of a skew monoid algebra, `erase a f` is an element with the same coefficients
as `f` except at `a` where the coefficient is `0`.
If `a` is not in the support of `f` then `erase a f = f`. -/
@[simps] def erase : SkewMonoidAlgebra M α →+ SkewMonoidAlgebra M α where
  toFun f := ⟨f.coeff.erase a⟩
  map_zero' := by simp
  map_add' := by simp

/--
@isnad1 id=eq.0h4v.s8.a8882d45148e from=seed src=0 shape=3a97f859 vocab=38e437b5
-/
@[deprecated (since := "2026-07-04")] alias erase_apply_toFinsupp := coeff_erase_apply

/--
@isnad1 id=eq.0h4v.s8.e9658fa81395 from=seed src=0 shape=67b4688f vocab=4b9bf19b
-/
@[simp]
theorem support_erase [DecidableEq α] : (f.erase a).support = f.support.erase a := by
  ext; simp [erase]

/--
@isnad1 id=eq.0h4v.s8.2b2486c3494c from=seed src=0 shape=e81b8c5c vocab=2e0578a9
-/
@[deprecated Finsupp.erase_same (since := "2026-07-04")]
theorem coeff_erase_same : (f.erase a).coeff a = 0 := by
  simp [erase]

variable {a a'} in
/--
@isnad1 id=eq.1h5v.s8.ac5ac3672adf from=seed src=0 shape=390ccef8 vocab=2e0578a9
-/
@[deprecated Finsupp.erase_ne (since := "2026-07-04")]
theorem coeff_erase_ne (h : a' ≠ a) : (f.erase a).coeff a' = f.coeff a' := by
  simp [erase, h]

/--
@isnad1 id=eq.0h4v.s8.b31698978a7b from=seed src=0 shape=60a221a9 vocab=f1921cbe
-/
@[simp]
theorem erase_single : erase a (single a b) = 0 := by
  simp [erase]

/--
@isnad1 id=eq.0h4v.s8.29a112d066ca from=seed src=0 shape=ccaf899a vocab=b8c50b30
-/
theorem single_add_erase (a : α) (f : SkewMonoidAlgebra M α) :
    single a (f.coeff a) + f.erase a = f := by
  ext; simp [ coeff_add, Finsupp.single_add_erase]

/--
@isnad1 id=var.0h6v.s7.46d44371f56f from=seed src=0 shape=3f917f4f vocab=8fae6aa6
-/
@[elab_as_elim]
theorem induction {p : SkewMonoidAlgebra M α → Prop} (f : SkewMonoidAlgebra M α) (h0 : p 0)
    (ha : ∀ (a b) (f : SkewMonoidAlgebra M α), a ∉ f.support → b ≠ 0 → p f → p (single a b + f)) :
    p f :=
  suffices ∀ (s) (f : SkewMonoidAlgebra M α), f.support = s → p f from this _ _ rfl
  fun s ↦
  Finset.cons_induction_on s (fun f hf ↦ by rwa [support_eq_empty.1 hf]) fun a s has ih f hf ↦ by
    suffices p (single a (f.coeff a) + f.erase a) by rwa [single_add_erase] at this
    classical
    apply ha
    · rw [support_erase, Finset.mem_erase]
      exact fun H ↦ H.1 rfl
    · simp only [← mem_support_iff, hf, Finset.mem_cons_self]
    · apply ih
      rw [support_erase, hf, Finset.erase_cons]

end erase

section update

variable {M α : Type*} [AddCommMonoid M] (f : SkewMonoidAlgebra M α) (a a' : α) (b : M)

/-- Replace the coefficient of an element `f` of a skew monoid algebra at a given point `a : α` by
a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the support of `f`.
Otherwise, if `a` was not in the `support` of `f`, it is added to it. -/
@[simps coeff] def update : SkewMonoidAlgebra M α :=
  ⟨f.coeff.update a b⟩

/--
@isnad1 id=eq.0h5v.s6.235a01254908 from=seed src=0 shape=a22ac971 vocab=21c927dd
-/
@[deprecated (since := "2026-07-04")] alias update_toFinsupp := coeff_update

/--
@isnad1 id=eq.0h4v.s6.485ff6990b94 from=seed src=0 shape=3c5e1bfa vocab=3489a50a
-/
@[simp]
theorem update_self : f.update a (f.coeff a) = f := by ext; simp

/--
@isnad1 id=eq.0h4v.s6.03081791a412 from=seed src=0 shape=b740cb87 vocab=128261fb
-/
@[simp]
theorem zero_update : update 0 a b = single a b := by
  simp [update]

/--
@isnad1 id=eq.0h5v.s6.3da6e2f36757 from=seed src=0 shape=9fcf4d84 vocab=10e81f8e
-/
theorem support_update [DecidableEq α] [DecidableEq M] :
    support (f.update a b) = if b = 0 then f.support.erase a else insert a f.support := by
  aesop (add norm [update, Finsupp.support_update_ne_zero])

/--
@isnad1 id=eq.0h6v.s7.33deaca97168 from=seed src=0 shape=1ac5f9bb vocab=4d34b39f
-/
@[deprecated Finsupp.update_apply (since := "2026-07-04")]
theorem coeff_update_apply [DecidableEq α] :
    (f.update a b).coeff a' = if a' = a then b else f.coeff a' := by
  simp [coeff_update, Function.update_apply]

/--
@isnad1 id=eq.0h5v.s6.16bc183c28f9 from=seed src=0 shape=80821179 vocab=3489a50a
-/
@[deprecated Finsupp.update_apply (since := "2026-07-04")]
theorem coeff_update_same : (f.update a b).coeff a = b := by
  classical
  rw [f.coeff_update_apply, ite_eq_left rfl]

variable {a a'} in
/--
@isnad1 id=eq.1h6v.s6.d0b873593a2a from=seed src=0 shape=55dad791 vocab=3489a50a
-/
@[deprecated Finsupp.update_apply (since := "2026-07-04")]
theorem coeff_update_ne (h : a' ≠ a) : (f.update a b).coeff a' = f.coeff a' := by
  classical
  rw [f.coeff_update_apply, ite_eq_right h]

/--
@isnad1 id=eq.0h5v.s8.e37f54b20d91 from=seed src=0 shape=d41a71a0 vocab=f698f63a
-/
theorem update_eq_erase_add_single : f.update a b = f.erase a + single a b := by
  classical ext x; by_cases hx : x = a <;> aesop (add norm coeff_single_apply)

/--
@isnad1 id=eq.0h4v.s8.c76a2287b1fd from=seed src=0 shape=99076f36 vocab=4f18bbc9
-/
@[simp]
theorem update_zero_eq_erase : f.update a 0 = f.erase a := by
  classical ext; simp [coeff_erase_apply, Finsupp.erase_apply, Function.update_apply]

end update

end SkewMonoidAlgebra
