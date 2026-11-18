import Tengoku.Brauerinduction.BrauerInduction.Cyclotomic.CharacterAlgebra
import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.IntegralLattice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The integral cyclotomic character ring

This file packages the global character system

`Q(G) = R_Λ(G) ∩ C_Z(G)`

as a subring of the cyclotomic character algebra.
-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u

namespace Tengoku.Brauerinduction.ClassFun

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/--
The ring of integer-valued elements of the cyclotomic character algebra.

Its elements are the functions in `R_Lambda.top k G` whose values lie in the
image of `ℤ → k`. This is the global Bernstein character ring `Q(G)`.-/
def IntegralCyclotomicCharacterRing :
    Subring (CyclotomicCharacterAlgebra (k := k) (G := G)) where
  carrier :=
    {f |
      (f : ClassFun k G) ∈ C_Z k G}
  zero_mem' := by
    change (0 : ClassFun k G) ∈ C_Z k G
    exact C_Z.zero_mem
  one_mem' := by
    change (1 : ClassFun k G) ∈ C_Z k G
    exact C_Z.one_mem
  add_mem' := by
    intro f g hf hg
    change
      (f : ClassFun k G) + (g : ClassFun k G) ∈ C_Z k G
    exact C_Z.add_mem hf hg
  mul_mem' := by
    intro f g hf hg
    change
      (f : ClassFun k G) * (g : ClassFun k G) ∈ C_Z k G
    exact C_Z.mul_mem hf hg
  neg_mem' := by
    intro f hf
    change -(f : ClassFun k G) ∈ C_Z k G
    exact C_Z.neg_mem hf

namespace IntegralCyclotomicCharacterRing

/--
@isnad1 id=iff.0h3v.s12.b9aede918c35 from=translated src=- shape=cffd88cd vocab=0dc15a20
-/
@[simp]
lemma mem_iff
    {f : CyclotomicCharacterAlgebra (k := k) (G := G)} :
    f ∈ IntegralCyclotomicCharacterRing (k := k) (G := G) ↔
      (f : ClassFun k G) ∈ C_Z k G :=
  Iff.rfl

/-- The underlying class function belongs to the global `R_Λ` span.
@isnad1 id=mem.0h3v.s13.34b5f6b686a7 from=translated src=- shape=fc630af3 vocab=05118bd4
-/
lemma rLambda_mem
    (f : IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    (f : ClassFun k G) ∈ R_Lambda.top k G :=
  f.1.property

/-- The underlying class function is integer-valued.
@isnad1 id=mem.0h3v.s13.f4655ff9e9e1 from=translated src=- shape=9739baf5 vocab=0dc15a20
-/
lemma intValued_mem
    (f : IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    (f : ClassFun k G) ∈ C_Z k G :=
  f.property

/--
Restricting a global integral cyclotomic character to a subgroup produces an
element of the subgroup-indexed character system `Q`.
@isnad1 id=mem.0h4v.s13.af2d746c8a7a from=translated src=- shape=563083b4 vocab=206a84ce
-/
lemma res_mem_Q_sys
    (H : Subgroup G)
    (f : IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    ClassFun.res H (f : ClassFun k G) ∈
      ClassFun.Q_sys k G H := by
  constructor
  · exact R_Lambda.top_res_to_subgroup H f.1.property
  · exact C_Z.res f.property

/--
Restriction to the top subgroup produces an element of `Q_sys(G)`.
@isnad1 id=mem.0h3v.s13.5dc90519b69f from=translated src=- shape=e1f345c1 vocab=da911814
-/
lemma res_top_mem_Q_sys
    (f : IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    ClassFun.res (⊤ : Subgroup G) (f : ClassFun k G) ∈
      ClassFun.Q_sys k G (⊤ : Subgroup G) :=
  res_mem_Q_sys ⊤ f

/--
The inclusion of integral cyclotomic characters into all integer-valued class
functions.-/
def toIntegerValuedClassFun :
    IntegralCyclotomicCharacterRing (k := k) (G := G) →+*
      IntegerValued (k := k) (G := G) where
  toFun f := ⟨(f : ClassFun k G), f.property⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/--
@isnad1 id=eq.0h3v.s16.0d5910ba5296 from=translated src=- shape=4473b5a4 vocab=4da43ca3
-/
@[simp]
lemma coe_toIntegerValuedClassFun
    (f : IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    (toIntegerValuedClassFun f : ClassFun k G) =
      (f : ClassFun k G) :=
  rfl

/--
@isnad1 id=injectiv.0h2v.s16.aa8b3dd36e36 from=translated src=- shape=f85eb06f vocab=9ce50806
-/
lemma toIntegerValuedClassFun_injective :
    Function.Injective
      (toIntegerValuedClassFun (k := k) (G := G)) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun q :
      IntegerValued (k := k) (G := G) =>
        (q : ClassFun k G))  h

/--
The inclusion of integral cyclotomic characters into the integer-valued
class-function lattice, as a `ℤ`-linear map.-/
def toIntegerValuedClassFunLinear :
    IntegralCyclotomicCharacterRing (k := k) (G := G) →ₗ[ℤ]
      IntegerValued (k := k) (G := G) where
  toFun := toIntegerValuedClassFun
  map_add' _ _ := rfl
  map_smul' n f := by
    apply Subtype.ext
    rfl

/--
@isnad1 id=eq.0h3v.s17.d64a24fce5dd from=translated src=- shape=ad8fd9de vocab=d5a59623
-/
@[simp]
lemma toIntegerValuedClassFunLinear_apply
    (f : IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    toIntegerValuedClassFunLinear f =
      toIntegerValuedClassFun f :=
  rfl

end IntegralCyclotomicCharacterRing

end Tengoku.Brauerinduction.ClassFun
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
