import Tengoku.StringDiagramsLean.StringDiagrams.Biadjunction.Cyclic
import Tengoku.Seed.CategoryTheory.Linear.Basic
import Tengoku.Seed.Algebra.Module.Submodule.Defs
import Tengoku.Seed.Algebra.Group.Subgroup.Defs
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Mates and cyclicity in locally linear bicategories

Mathlib (at the pinned version) has no notion of a bicategory enriched in abelian groups or
modules. We introduce two `Prop`-valued classes on a bicategory whose hom categories are
preadditive (resp. `R`-linear), in the style of Mathlib's `MonoidalPreadditive` and
`MonoidalLinear`:

* `LocallyPreadditive B`: whiskering is additive;
* `LocallyLinear R B`: whiskering is `R`-linear.

Under these hypotheses the mates are additive (resp. `R`-linear) equivalences
(`Biadjunction.rightMateAddEquiv`, `Biadjunction.rightMateLinearEquiv`, and the left
versions), the cyclic 2-morphisms form a submodule (`Biadjunction.cyclicSubmodule`,
`IsCyclic.add`, `IsCyclic.smul`, ...), and the traces are additive and linear
(`rightTrace_add`, `rightTrace_smul`, ...).
-/

namespace StringDiagrams

open CategoryTheory Bicategory

universe w v u u'

variable {B : Type u} [Bicategory.{w, v} B]

/-- A bicategory with preadditive hom categories in which whiskering is additive.-/
class LocallyPreadditive (B : Type u) [Bicategory.{w, v} B]
    [∀ a b : B, Preadditive (a ⟶ b)] : Prop where
  whiskerLeft_add : ∀ {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η θ : g ⟶ h),
    f ◁ (η + θ) = f ◁ η + f ◁ θ
  add_whiskerRight : ∀ {a b c : B} {f g : a ⟶ b} (η θ : f ⟶ g) (h : b ⟶ c),
    (η + θ) ▷ h = η ▷ h + θ ▷ h

/-- A bicategory with `R`-linear hom categories in which whiskering is `R`-linear.-/
class LocallyLinear (R : Type u') [Semiring R] (B : Type u) [Bicategory.{w, v} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] : Prop where
  whiskerLeft_smul : ∀ {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (r : R) (η : g ⟶ h),
    f ◁ (r • η) = r • (f ◁ η)
  smul_whiskerRight : ∀ {a b c : B} {f g : a ⟶ b} (r : R) (η : f ⟶ g) (h : b ⟶ c),
    (r • η) ▷ h = r • (η ▷ h)

attribute [simp] LocallyPreadditive.whiskerLeft_add LocallyPreadditive.add_whiskerRight
attribute [simp] LocallyLinear.whiskerLeft_smul LocallyLinear.smul_whiskerRight

section Preadditive

variable [∀ a b : B, Preadditive (a ⟶ b)] [LocallyPreadditive B]

/-- Left whiskering as an additive map.-/
@[simps!]
def whiskerLeftAddHom {a b c : B} (f : a ⟶ b) (g h : b ⟶ c) : (g ⟶ h) →+ (f ≫ g ⟶ f ≫ h) :=
  AddMonoidHom.mk' (f ◁ ·) (LocallyPreadditive.whiskerLeft_add f)

/-- Right whiskering as an additive map.-/
@[simps!]
def whiskerRightAddHom {a b c : B} (f g : a ⟶ b) (h : b ⟶ c) : (f ⟶ g) →+ (f ≫ h ⟶ g ≫ h) :=
  AddMonoidHom.mk' (· ▷ h) (fun η θ => LocallyPreadditive.add_whiskerRight η θ h)

/--
@isnad1 id=eq.0h7v.s8.3f961abf1e9f from=translated src=- shape=90e73a8b vocab=64f3a6a7
-/
@[simp]
theorem whiskerLeft_zero' {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} : f ◁ (0 : g ⟶ h) = 0 :=
  (whiskerLeftAddHom f g h).map_zero

/--
@isnad1 id=eq.0h7v.s8.171f687d023b from=translated src=- shape=7a99e96a vocab=a389fe95
-/
@[simp]
theorem zero_whiskerRight' {a b c : B} {f g : a ⟶ b} (h : b ⟶ c) : (0 : f ⟶ g) ▷ h = 0 :=
  (whiskerRightAddHom f g h).map_zero

/--
@isnad1 id=eq.0h8v.s9.a1d85a53f2d0 from=translated src=- shape=5bf7c421 vocab=39e1bbcb
-/
@[simp]
theorem whiskerLeft_neg' {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    f ◁ (-η) = -(f ◁ η) :=
  (whiskerLeftAddHom f g h).map_neg η

/--
@isnad1 id=eq.0h8v.s9.e64e84616507 from=translated src=- shape=60ca4d88 vocab=9e9847be
-/
@[simp]
theorem neg_whiskerRight' {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (-η) ▷ h = -(η ▷ h) :=
  (whiskerRightAddHom f g h).map_neg η

namespace Biadjunction

variable {a b : B} {f f' : a ⟶ b} {g g' : b ⟶ a}

/--
@isnad1 id=eq.0h11v.s11.ef9605fc1b40 from=translated src=- shape=b41600ba vocab=90bbbe8a
-/
theorem rightMate_add (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α β : f ⟶ f') :
    rightMate P P' (α + β) = rightMate P P' α + rightMate P P' β := by
  simp only [rightMate_apply, LocallyPreadditive.whiskerLeft_add,
    LocallyPreadditive.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

/--
@isnad1 id=eq.0h11v.s11.8c1de81dae7e from=translated src=- shape=b41600ba vocab=7056a06f
-/
theorem leftMate_add (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α β : f ⟶ f') :
    leftMate P P' (α + β) = leftMate P P' α + leftMate P P' β := by
  simp only [leftMate_apply, LocallyPreadditive.whiskerLeft_add,
    LocallyPreadditive.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

/-- The right mate as an additive equivalence.-/
def rightMateAddEquiv (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : (f ⟶ f') ≃+ (g' ⟶ g) :=
  { rightMate P P' with map_add' := rightMate_add P P' }

/-- The left mate as an additive equivalence.-/
def leftMateAddEquiv (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : (f ⟶ f') ≃+ (g' ⟶ g) :=
  { leftMate P P' with map_add' := leftMate_add P P' }

/--
@isnad1 id=eq.0h10v.s11.a83ddd727595 from=translated src=- shape=8cc682ac vocab=780c0def
-/
@[simp]
theorem rightMateAddEquiv_apply (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    rightMateAddEquiv P P' α = rightMate P P' α := rfl

/--
@isnad1 id=eq.0h10v.s11.ce3b5905a314 from=translated src=- shape=8cc682ac vocab=ca302cac
-/
@[simp]
theorem leftMateAddEquiv_apply (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    leftMateAddEquiv P P' α = leftMate P P' α := rfl

/--
@isnad1 id=eq.0h9v.s9.0ddd8092b048 from=translated src=- shape=7dd5203b vocab=52ab0ee2
-/
@[simp]
theorem rightMate_zero (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : rightMate P P' 0 = 0 :=
  (rightMateAddEquiv P P').map_zero

/--
@isnad1 id=eq.0h9v.s9.eef64cd2f522 from=translated src=- shape=7dd5203b vocab=bf704294
-/
@[simp]
theorem leftMate_zero (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : leftMate P P' 0 = 0 :=
  (leftMateAddEquiv P P').map_zero

/--
@isnad1 id=eq.0h10v.s10.ce899b6727df from=translated src=- shape=a7c78340 vocab=e94b2847
-/
theorem rightMate_neg (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    rightMate P P' (-α) = -rightMate P P' α :=
  (rightMateAddEquiv P P').map_neg α

/--
@isnad1 id=eq.0h10v.s10.0ad9c171077f from=translated src=- shape=a7c78340 vocab=99830a3f
-/
theorem leftMate_neg (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    leftMate P P' (-α) = -leftMate P P' α :=
  (leftMateAddEquiv P P').map_neg α

/--
@isnad1 id=eq.0h11v.s11.ab61450fb435 from=translated src=- shape=b41600ba vocab=12a60f3c
-/
theorem rightMate_sub (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α β : f ⟶ f') :
    rightMate P P' (α - β) = rightMate P P' α - rightMate P P' β :=
  (rightMateAddEquiv P P').map_sub α β

/--
@isnad1 id=eq.0h11v.s11.dad408bfe20e from=translated src=- shape=b41600ba vocab=4260d8c9
-/
theorem leftMate_sub (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α β : f ⟶ f') :
    leftMate P P' (α - β) = leftMate P P' α - leftMate P P' β :=
  (leftMateAddEquiv P P').map_sub α β

/--
@isnad1 id=eq.0h12v.s10.514b1f98e3b2 from=translated src=- shape=245ede6f vocab=1d572507
-/
theorem rightMate_sum {ι : Type*} (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (s : Finset ι)
    (α : ι → (f ⟶ f')) : rightMate P P' (∑ i ∈ s, α i) = ∑ i ∈ s, rightMate P P' (α i) :=
  map_sum (rightMateAddEquiv P P') α s

/--
@isnad1 id=eq.0h12v.s10.4924d8ce801d from=translated src=- shape=245ede6f vocab=6a224c38
-/
theorem leftMate_sum {ι : Type*} (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (s : Finset ι)
    (α : ι → (f ⟶ f')) : leftMate P P' (∑ i ∈ s, α i) = ∑ i ∈ s, leftMate P P' (α i) :=
  map_sum (leftMateAddEquiv P P') α s

/--
@isnad1 id=iscyclic.0h9v.s7.f00c4aa5cf66 from=translated src=- shape=feb4e4fb vocab=1e093d38
-/
theorem isCyclic_zero (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : IsCyclic P P' 0 := by
  rw [IsCyclic, rightMate_zero, leftMate_zero]

/--
@isnad1 id=iscyclic.2h11v.s9.caad6c00221b from=translated src=- shape=3618a9e3 vocab=22f459db
-/
theorem IsCyclic.add {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α β : f ⟶ f'} (hα : IsCyclic P P' α)
    (hβ : IsCyclic P P' β) : IsCyclic P P' (α + β) := by
  rw [IsCyclic, rightMate_add, leftMate_add, hα.eq, hβ.eq]

/--
@isnad1 id=iscyclic.1h10v.s8.28996257a9d6 from=translated src=- shape=6c441427 vocab=9c434261
-/
theorem IsCyclic.neg {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'} (hα : IsCyclic P P' α) :
    IsCyclic P P' (-α) := by
  rw [IsCyclic, rightMate_neg, leftMate_neg, hα.eq]

/--
@isnad1 id=iscyclic.2h11v.s8.07a8a5b52777 from=translated src=- shape=3618a9e3 vocab=e933ae90
-/
theorem IsCyclic.sub {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α β : f ⟶ f'} (hα : IsCyclic P P' α)
    (hβ : IsCyclic P P' β) : IsCyclic P P' (α - β) := by
  rw [IsCyclic, rightMate_sub, leftMate_sub, hα.eq, hβ.eq]

/--
@isnad1 id=iscyclic.1h12v.s8.7f95ef3c5f52 from=translated src=- shape=8725f654 vocab=82785273
-/
theorem IsCyclic.sum {ι : Type*} {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} (s : Finset ι)
    {α : ι → (f ⟶ f')} (h : ∀ i ∈ s, IsCyclic P P' (α i)) :
    IsCyclic P P' (∑ i ∈ s, α i) := by
  rw [IsCyclic, rightMate_sum, leftMate_sum]
  exact Finset.sum_congr rfl fun i hi => (h i hi).eq

/-- The cyclic 2-morphisms form an additive subgroup.-/
def cyclicAddSubgroup (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : AddSubgroup (f ⟶ f') where
  carrier := {α | IsCyclic P P' α}
  add_mem' := IsCyclic.add
  zero_mem' := isCyclic_zero P P'
  neg_mem' := IsCyclic.neg

/--
@isnad1 id=iff.0h10v.s9.e94b16453bb1 from=translated src=- shape=e3ab9189 vocab=dcc89de3
-/
@[simp]
theorem mem_cyclicAddSubgroup (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    α ∈ cyclicAddSubgroup P P' ↔ IsCyclic P P' α := Iff.rfl

/--
@isnad1 id=eq.0h8v.s9.3de0f3a6cee2 from=translated src=- shape=7e243580 vocab=9d9d9bd8
-/
theorem rightTrace_add (P : f ⊣⊢ g) (α β : f ⟶ f) :
    rightTrace P (α + β) = rightTrace P α + rightTrace P β := by
  simp only [rightTrace, LocallyPreadditive.add_whiskerRight, Preadditive.add_comp,
    Preadditive.comp_add]

/--
@isnad1 id=eq.0h8v.s9.3c286b01d6e5 from=translated src=- shape=7466364b vocab=5114e69b
-/
theorem leftTrace_add (P : f ⊣⊢ g) (α β : f ⟶ f) :
    leftTrace P (α + β) = leftTrace P α + leftTrace P β := by
  simp only [leftTrace, LocallyPreadditive.whiskerLeft_add, Preadditive.add_comp,
    Preadditive.comp_add]

/-- The right trace as an additive map.-/
@[simps!]
def rightTraceAddHom (P : f ⊣⊢ g) : (f ⟶ f) →+ (𝟙 a ⟶ 𝟙 a) :=
  AddMonoidHom.mk' (rightTrace P) (rightTrace_add P)

/-- The left trace as an additive map.-/
@[simps!]
def leftTraceAddHom (P : f ⊣⊢ g) : (f ⟶ f) →+ (𝟙 b ⟶ 𝟙 b) :=
  AddMonoidHom.mk' (leftTrace P) (leftTrace_add P)

end Biadjunction

end Preadditive

section Linear

variable (R : Type u') [Semiring R] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, Linear R (a ⟶ b)] [LocallyPreadditive B] [LocallyLinear R B]

namespace Biadjunction

variable {R} {a b : B} {f f' : a ⟶ b} {g g' : b ⟶ a}

omit [LocallyPreadditive B] in
/--
@isnad1 id=eq.0h12v.s11.1155bcda4a3c from=translated src=- shape=4043504b vocab=6423cb21
-/
theorem rightMate_smul (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (r : R) (α : f ⟶ f') :
    rightMate P P' (r • α) = r • rightMate P P' α := by
  simp only [rightMate_apply, LocallyLinear.whiskerLeft_smul, LocallyLinear.smul_whiskerRight,
    Linear.smul_comp, Linear.comp_smul]

omit [LocallyPreadditive B] in
/--
@isnad1 id=eq.0h12v.s11.7c7249a4535a from=translated src=- shape=4043504b vocab=890da275
-/
theorem leftMate_smul (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (r : R) (α : f ⟶ f') :
    leftMate P P' (r • α) = r • leftMate P P' α := by
  simp only [leftMate_apply, LocallyLinear.whiskerLeft_smul, LocallyLinear.smul_whiskerRight,
    Linear.smul_comp, Linear.comp_smul]

variable (R)

/-- The right mate as an `R`-linear equivalence.-/
def rightMateLinearEquiv (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : (f ⟶ f') ≃ₗ[R] (g' ⟶ g) :=
  { rightMate P P' with
    map_add' := rightMate_add P P'
    map_smul' := rightMate_smul P P' }

/-- The left mate as an `R`-linear equivalence.-/
def leftMateLinearEquiv (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : (f ⟶ f') ≃ₗ[R] (g' ⟶ g) :=
  { leftMate P P' with
    map_add' := leftMate_add P P'
    map_smul' := leftMate_smul P P' }

/--
@isnad1 id=eq.0h11v.s10.ad4d37c28635 from=translated src=- shape=74717837 vocab=b6b1f22d
-/
@[simp]
theorem rightMateLinearEquiv_apply (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    rightMateLinearEquiv R P P' α = rightMate P P' α := rfl

/--
@isnad1 id=eq.0h11v.s10.43d72563013d from=translated src=- shape=74717837 vocab=a80d8e4a
-/
@[simp]
theorem leftMateLinearEquiv_apply (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    leftMateLinearEquiv R P P' α = leftMate P P' α := rfl

variable {R}

omit [LocallyPreadditive B] in
/--
@isnad1 id=iscyclic.1h12v.s10.ece32538d85e from=translated src=- shape=e5944b18 vocab=6dba3aa9
-/
theorem IsCyclic.smul {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'} (hα : IsCyclic P P' α)
    (r : R) : IsCyclic P P' (r • α) := by
  rw [IsCyclic, rightMate_smul, leftMate_smul, hα.eq]

variable (R) in
/-- The cyclic 2-morphisms form an `R`-submodule.-/
def cyclicSubmodule (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : Submodule R (f ⟶ f') where
  carrier := {α | IsCyclic P P' α}
  add_mem' := IsCyclic.add
  zero_mem' := isCyclic_zero P P'
  smul_mem' r _ h := IsCyclic.smul h r

/--
@isnad1 id=iff.0h11v.s9.684e5c1dd40b from=translated src=- shape=80e8a769 vocab=ccbd86f8
-/
@[simp]
theorem mem_cyclicSubmodule (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    α ∈ cyclicSubmodule R P P' ↔ IsCyclic P P' α := Iff.rfl

omit [LocallyPreadditive B] in
/--
@isnad1 id=eq.0h9v.s11.83b10afe1c89 from=translated src=- shape=cd23edf5 vocab=31df59a8
-/
theorem rightTrace_smul (P : f ⊣⊢ g) (r : R) (α : f ⟶ f) :
    rightTrace P (r • α) = r • rightTrace P α := by
  simp only [rightTrace, LocallyLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]

omit [LocallyPreadditive B] in
/--
@isnad1 id=eq.0h9v.s11.5d2b2cd3daef from=translated src=- shape=ea532416 vocab=a20fffd5
-/
theorem leftTrace_smul (P : f ⊣⊢ g) (r : R) (α : f ⟶ f) :
    leftTrace P (r • α) = r • leftTrace P α := by
  simp only [leftTrace, LocallyLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul]

variable (R)

/-- The right trace as an `R`-linear map.-/
def rightTraceLinearMap (P : f ⊣⊢ g) : (f ⟶ f) →ₗ[R] (𝟙 a ⟶ 𝟙 a) where
  toFun := rightTrace P
  map_add' := rightTrace_add P
  map_smul' := rightTrace_smul P

/-- The left trace as an `R`-linear map.-/
def leftTraceLinearMap (P : f ⊣⊢ g) : (f ⟶ f) →ₗ[R] (𝟙 b ⟶ 𝟙 b) where
  toFun := leftTrace P
  map_add' := leftTrace_add P
  map_smul' := leftTrace_smul P

end Biadjunction

end Linear

end StringDiagrams
