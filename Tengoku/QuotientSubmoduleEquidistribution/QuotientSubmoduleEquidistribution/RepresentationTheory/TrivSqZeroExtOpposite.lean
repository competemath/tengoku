import Tengoku.Seed.Algebra.Module.MinimalAxioms
import Tengoku.Seed.Algebra.TrivSqZeroExt.Basic
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationTheory.MoritaRestriction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Opposites of trivial square-zero extensions

Right modules over a trivial square-zero extension are left modules over its
opposite ring.  When the base ring is commutative, that opposite is again a
trivial square-zero extension after exchanging the left and right actions on
the bimodule.  This file records the exchange and the resulting ring
equivalence explicitly.
-/

set_option autoImplicit false

noncomputable section

namespace QuotientSubmoduleEquidistribution.TrivSqZeroExtOpposite

universe u v

/-- A tagged copy of a bimodule with its left and right actions exchanged.-/
structure ReversedBimodule (R : Type u) (M : Type v) where
  val : M

namespace ReversedBimodule

variable {R : Type u} {M : Type v}

/-- Forget the tag on the reversed bimodule.-/
def equiv : ReversedBimodule R M ≃ M where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

/--
@isnad1 id=eq.1h4v.s4.9360fe6bc329 from=translated src=- shape=4037c558 vocab=b4ea4f09
-/
theorem ext' {x y : ReversedBimodule R M} (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

instance [AddCommGroup M] : AddCommGroup (ReversedBimodule R M) :=
  (equiv (R := R) (M := M)).addCommGroup

instance [CommRing R] [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    SMul R (ReversedBimodule R M) where
  smul r x := ⟨MulOpposite.op r • x.val⟩

instance [CommRing R] [AddCommGroup M] [Module Rᵐᵒᵖ M] :
    Module R (ReversedBimodule R M) :=
  Module.ofMinimalAxioms
    (by
      intro r x y
      apply ext'
      exact smul_add (MulOpposite.op r) x.val y.val)
    (by
      intro r s x
      apply ext'
      change MulOpposite.op (r + s) • x.val =
        MulOpposite.op r • x.val + MulOpposite.op s • x.val
      rw [MulOpposite.op_add, add_smul])
    (by
      intro r s x
      apply ext'
      change MulOpposite.op (r * s) • x.val =
        MulOpposite.op r • (MulOpposite.op s • x.val)
      rw [mul_comm r s, MulOpposite.op_mul, mul_smul])
    (by
      intro x
      apply ext'
      exact one_smul Rᵐᵒᵖ x.val)

instance [CommRing R] [AddCommGroup M] [Module R M] :
    SMul Rᵐᵒᵖ (ReversedBimodule R M) where
  smul r x := ⟨MulOpposite.unop r • x.val⟩

instance [CommRing R] [AddCommGroup M] [Module R M] :
    Module Rᵐᵒᵖ (ReversedBimodule R M) :=
  Module.ofMinimalAxioms
    (by
      intro r x y
      apply ext'
      exact smul_add (MulOpposite.unop r) x.val y.val)
    (by
      intro r s x
      apply ext'
      change MulOpposite.unop (r + s) • x.val =
        MulOpposite.unop r • x.val + MulOpposite.unop s • x.val
      rw [MulOpposite.unop_add, add_smul])
    (by
      intro r s x
      apply ext'
      change MulOpposite.unop (r * s) • x.val =
        MulOpposite.unop r • (MulOpposite.unop s • x.val)
      rw [MulOpposite.unop_mul, mul_comm, mul_smul])
    (by
      intro x
      apply ext'
      exact one_smul R x.val)

instance [CommRing R] [AddCommGroup M]
    [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] :
    SMulCommClass R Rᵐᵒᵖ (ReversedBimodule R M) where
  smul_comm r s x := by
    apply ext'
    exact (smul_comm (MulOpposite.unop s) (MulOpposite.op r) x.val).symm

end ReversedBimodule

variable {R : Type u} {M : Type v}
variable [CommRing R] [AddCommGroup M]
variable [Module R M] [Module Rᵐᵒᵖ M]
variable [SMulCommClass R Rᵐᵒᵖ M]

/-- The opposite of a trivial square-zero extension is the trivial extension
by the bimodule with exchanged actions.-/
def oppositeRingEquiv :
    (TrivSqZeroExt R M)ᵐᵒᵖ ≃+*
      TrivSqZeroExt R (ReversedBimodule R M) where
  toFun x :=
    ((MulOpposite.unop x).1,
      ReversedBimodule.mk (MulOpposite.unop x).2)
  invFun x := MulOpposite.op (x.1, x.2.val)
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl
  map_mul' := by
    rintro ⟨⟨r, m⟩⟩ ⟨⟨s, n⟩⟩
    apply TrivSqZeroExt.ext
    · exact mul_comm s r
    · apply ReversedBimodule.ext'
      exact add_comm _ _
  map_add' := by
    rintro ⟨⟨r, m⟩⟩ ⟨⟨s, n⟩⟩
    rfl

/-- The corresponding equivalence of all left-module categories.-/
def moduleEquivalence :
    ModuleCat.{max u v} (TrivSqZeroExt R M)ᵐᵒᵖ ≌
      ModuleCat.{max u v}
        (TrivSqZeroExt R (ReversedBimodule R M)) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (oppositeRingEquiv (R := R) (M := M)).symm

omit [SMulCommClass R Rᵐᵒᵖ M] in
/--
@isnad1 id=eq.0h3v.s9.33c190b63642 from=translated src=- shape=9883af1f vocab=7434fec0
-/
@[simp]
theorem oppositeRingEquiv_apply (x : TrivSqZeroExt R M) :
    oppositeRingEquiv (R := R) (M := M) (MulOpposite.op x) =
      (x.1, ReversedBimodule.mk x.2) :=
  rfl

omit [SMulCommClass R Rᵐᵒᵖ M] in
/--
@isnad1 id=eq.0h3v.s10.2dbd2e09b71f from=translated src=- shape=1c556c38 vocab=fd7133ed
-/
@[simp]
theorem oppositeRingEquiv_symm_apply
    (x : TrivSqZeroExt R (ReversedBimodule R M)) :
    (oppositeRingEquiv (R := R) (M := M)).symm x =
      MulOpposite.op (x.1, x.2.val) :=
  rfl

end QuotientSubmoduleEquidistribution.TrivSqZeroExtOpposite
