import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.Character.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The character ring

This file packages virtual characters as a subring of the ring of class
functions.

* `ClassFun.characterSet k G` is the set of characters of finite-dimensional
  representations of `G`;
* `ClassFun.characterSpan k G` is their integral span;
* `ClassFun.CharacterRing k G` is the corresponding subring of
  `ClassFun k G`, with multiplication induced by tensor product;
* `ClassFun.CharacterRing.character` regards a representation character as an
  element of the character ring.

This is an image-level character ring inside `ClassFun k G`. It is deliberately
not defined as a Grothendieck group or as the full Green ring of
representations.
-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u

namespace Tengoku.Brauerinduction.ClassFun

section Span

variable {k G : Type u} [Field k] [Group G]

/--
Characters of finite-dimensional representations of `G`.-/
def characterSet
    (k : Type u) [Field k]
    (G : Type u) [Group G] :
    Set (ClassFun k G) :=
  {χ |
    ∃ V : FDRep k G,
      χ = ClassFun.character V}

/--
The integral span of characters of finite-dimensional representations.-/
def characterSpan
    (k : Type u) [Field k]
    (G : Type u) [Group G] :
    Submodule ℤ (ClassFun k G) :=
  Submodule.span ℤ (characterSet k G)

namespace characterSpan

/--
@isnad1 id=mem.0h3v.s7.e82559ddf9be from=translated src=- shape=39ce8ab6 vocab=4e99f741
-/
lemma character_mem
    (V : FDRep k G) :
    ClassFun.character V ∈ characterSpan k G :=
  Submodule.subset_span ⟨V, rfl⟩

/--
@isnad1 id=mem.0h2v.s7.57142b54c667 from=translated src=- shape=6d7c0ddc vocab=151ed15b
-/
lemma one_mem :
    (1 : ClassFun k G) ∈ characterSpan k G := by
  rw [← ClassFun.char_trivial (k := k) (G := G)]
  exact character_mem (FDRep.trivial k G)

/--
@isnad1 id=mem.1h4v.s8.4446b70605b0 from=translated src=- shape=2df5a15e vocab=1b6f944a
-/
lemma character_mul_mem
    (V : FDRep k G)
    {f : ClassFun k G}
    (hf : f ∈ characterSpan k G) :
    ClassFun.character V * f ∈ characterSpan k G := by
  refine Submodule.span_induction
    (p := fun f _ =>
      ClassFun.character V * f ∈ characterSpan k G)
    ?gen ?zero ?add ?smul hf
  · rintro _ ⟨W, rfl⟩
    rw [← ClassFun.char_tensor]
    exact character_mem (FDRep.tensor V W)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro n x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ n hx

/--
@isnad1 id=mem.2h4v.s8.4dac827b497f from=translated src=- shape=acd728da vocab=3cbe4698
-/
lemma mul_mem
    {f g : ClassFun k G}
    (hf : f ∈ characterSpan k G)
    (hg : g ∈ characterSpan k G) :
    f * g ∈ characterSpan k G := by
  refine Submodule.span_induction
    (p := fun f _ => f * g ∈ characterSpan k G)
    ?gen ?zero ?add ?smul hf
  · rintro _ ⟨V, rfl⟩
    exact character_mul_mem V hg
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro n x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ n hx

end characterSpan

/--
The character ring of `G` over `k`.

This is the subring of `ClassFun k G` consisting of integral linear
combinations of characters of finite-dimensional representations. It is an
image-level character ring, not a Grothendieck or Green ring construction.-/
def CharacterRing
    (k : Type u) [Field k]
    (G : Type u) [Group G] :
    Subring (ClassFun k G) where
  carrier := characterSpan k G
  zero_mem' := Submodule.zero_mem _
  one_mem' := characterSpan.one_mem
  add_mem' := fun hf hg => Submodule.add_mem _ hf hg
  mul_mem' := characterSpan.mul_mem
  neg_mem' := fun hf => Submodule.neg_mem _ hf

namespace CharacterRing

/--
@isnad1 id=iff.0h3v.s7.99a10eec1f70 from=translated src=- shape=fcf92858 vocab=ec462d20
-/
@[simp]
lemma mem_iff
    {f : ClassFun k G} :
    f ∈ CharacterRing k G ↔ f ∈ characterSpan k G :=
  Iff.rfl

/-- A representation character regarded as an element of the character ring.-/
noncomputable def character
    (V : FDRep k G) :
    CharacterRing k G :=
  ⟨ClassFun.character V, characterSpan.character_mem V⟩

/--
@isnad1 id=eq.0h3v.s7.2fd80802a883 from=translated src=- shape=e8a3d1ff vocab=35885b7a
-/
@[simp]
lemma coe_character
    (V : FDRep k G) :
    (character V : ClassFun k G) = ClassFun.character V :=
  rfl

/--
@isnad1 id=eq.0h2v.s8.cfc6e2a1c474 from=translated src=- shape=2813f851 vocab=905c7d01
-/
@[simp]
lemma character_trivial :
    character (FDRep.trivial k G) = 1 := by
  apply Subtype.ext
  exact ClassFun.char_trivial k G

/--
@isnad1 id=eq.0h4v.s9.724946f10dca from=translated src=- shape=0568cabb vocab=5e4dcf77
-/
@[simp]
lemma character_tensor
    (V W : FDRep k G) :
    character (FDRep.tensor V W) = character V * character W := by
  apply Subtype.ext
  exact ClassFun.char_tensor V W

end CharacterRing

end Span

end Tengoku.Brauerinduction.ClassFun
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
