/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Action.Faithful
public import Tengoku.Seed.Algebra.Order.Group.End
public import Tengoku.Seed.Order.RelIso.Basic

/-!
# Tautological action by relation automorphisms
-/

public section

assert_not_exists MonoidWithZero

namespace RelHom
variable {α : Type*} {r : α → α → Prop}

/-- The tautological action by `r →r r` on `α`. -/
instance applyMulAction : MulAction (r →r r) α where
  smul := (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/--
@isnad1 id=eq.0h4v.s6.54b01772e207 from=seed src=0 shape=ce8eebc6 vocab=e5d9f8c7
-/
@[simp] lemma smul_def (f : r →r r) (a : α) : f • a = f a := rfl

/--
@isnad1 id=faithful.0h2v.s5.76b1af6e1a5f from=seed src=0 shape=3f58bd30 vocab=d63a4cf2
-/
instance apply_faithfulSMul : FaithfulSMul (r →r r) α where eq_of_smul_eq_smul h := RelHom.ext h

end RelHom

namespace RelEmbedding
variable {α : Type*} {r : α → α → Prop}

/-- The tautological action by `r ↪r r` on `α`. -/
instance applyMulAction : MulAction (r ↪r r) α where
  smul := (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/--
@isnad1 id=eq.0h4v.s6.bf4cd77da8e7 from=seed src=0 shape=ce8eebc6 vocab=eb3fedf0
-/
@[simp] lemma smul_def (f : r ↪r r) (a : α) : f • a = f a := rfl

/--
@isnad1 id=faithful.0h2v.s5.d736e32e74de from=seed src=0 shape=3f58bd30 vocab=596fd252
-/
instance apply_faithfulSMul : FaithfulSMul (r ↪r r) α where eq_of_smul_eq_smul h := ext h

end RelEmbedding

namespace RelIso
variable {α : Type*} {r : α → α → Prop}

/-- The tautological action by `r ≃r r` on `α`. -/
instance applyMulAction : MulAction (r ≃r r) α where
  smul := (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/--
@isnad1 id=eq.0h4v.s6.1fd84da4ff88 from=seed src=0 shape=ce8eebc6 vocab=e9f232bc
-/
@[simp] lemma smul_def (f : r ≃r r) (a : α) : f • a = f a := rfl

/--
@isnad1 id=faithful.0h2v.s6.f899ba3e4fed from=seed src=0 shape=3f58bd30 vocab=7699d938
-/
instance apply_faithfulSMul : FaithfulSMul (r ≃r r) α where eq_of_smul_eq_smul h := RelIso.ext h

end RelIso
