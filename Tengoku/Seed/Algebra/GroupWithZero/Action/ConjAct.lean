/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.GroupWithZero.Basic
public import Tengoku.Seed.GroupTheory.GroupAction.ConjAct

/-!
# Conjugation action of a group with zero on itself
-/

public section

assert_not_exists Ring

variable {α G₀ : Type*}

namespace ConjAct
variable [GroupWithZero G₀]

instance : GroupWithZero (ConjAct G₀) := inferInstanceAs <| GroupWithZero G₀

/--
@isnad1 id=eq.0h1v.s7.cbe923b22098 from=seed src=0 shape=5a2d305d vocab=26f163bb
-/
@[simp] lemma ofConjAct_zero : ofConjAct 0 = (0 : G₀) := rfl
/--
@isnad1 id=eq.0h1v.s7.ed218b2cb1d2 from=seed src=0 shape=759a5eb9 vocab=acf34539
-/
@[simp] lemma toConjAct_zero : toConjAct (0 : G₀) = 0 := rfl

instance mulAction₀ : MulAction (ConjAct G₀) G₀ where
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]

/--
@isnad1 id=smulcomm.0h2v.s5.20f73311271b from=seed src=0 shape=cf9d7ef0 vocab=fedc1f16
-/
instance smulCommClass₀ [SMul α G₀] [SMulCommClass α G₀ G₀] [IsScalarTower α G₀ G₀] :
    SMulCommClass α (ConjAct G₀) G₀ where
  smul_comm a ug g := by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]

/--
@isnad1 id=smulcomm.0h2v.s5.aaed1ebabdd0 from=seed src=0 shape=4d631776 vocab=fedc1f16
-/
instance smulCommClass₀' [SMul α G₀] [SMulCommClass G₀ α G₀] [IsScalarTower α G₀ G₀] :
    SMulCommClass (ConjAct G₀) α G₀ :=
  haveI := SMulCommClass.symm G₀ α G₀
  .symm ..

end ConjAct
