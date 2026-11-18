import Tengoku.Brauerinduction.BrauerInduction.Background.ClassFun.Character.Ring
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Character.Induced
import Tengoku.Brauerinduction.BrauerInduction.Elementary.BrauerElementary

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Induced-character spans and ideals

This file develops a generic API for integral spans of characters induced from
subgroups satisfying a predicate `P`.

* `InducedCharacterGen P` is the set of induced-character generators;
* `InducedCharacterSpan P` is their `ℤ`-span in `ClassFun k G`;
* `InducedCharacterIdeal P` packages the same span as an ideal of
  `ClassFun.CharacterRing k G`.

The generic span is contained in the character span, is stable under
multiplication by virtual characters, and is preserved by subgroup induction
when the subgroup predicate is preserved under the relevant embeddings.

The final section specializes this construction to Brauer-elementary
subgroups, defining `BrauerSpanChar` and `BrauerIdeal`. The subsequent
linear-character reduction is developed separately in
`BrauerInduction.LinearSpan`.
-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u

open BigOperators CategoryTheory

namespace BrauerInduction

variable {k : Type u} [Field k] {G : Type u} [Group G] [Finite G]

/--
Characters induced from representations of subgroups satisfying `P`.-/
def InducedCharacterGen
    {k G : Type u} [Field k] [Group G] [Finite G]
    (P : Subgroup G → Prop) :
    Set (ClassFun k G) :=
  {φ |
    ∃ (H : Subgroup G) (_ : P H)
      (V : FDRep k H),
      φ = ClassFun.ind H (ClassFun.character V)}

/--
The integral span of characters induced from representations of subgroups
satisfying `P`.-/
def InducedCharacterSpan
    {k : Type u} [Field k]
    {G : Type u} [Group G] [Finite G]
    (P : Subgroup G → Prop) :
    Submodule ℤ (ClassFun k G) :=
  Submodule.span ℤ (InducedCharacterGen P)

namespace InducedCharacterSpan

/--
@isnad1 id=mem.0h6v.s8.a05a4bdfe3d8 from=translated src=- shape=bbf9bdd1 vocab=8cff54e7
-/
lemma inducedCharacter_mem
    {P : Subgroup G → Prop}
    (H : Subgroup G)
    (hH : P H)
    (V : FDRep k H) :
    ClassFun.ind H (ClassFun.character V) ∈ InducedCharacterSpan P :=
  Submodule.subset_span ⟨H, hH, V, rfl⟩

/--
@isnad1 id=le.0h5v.s7.efabb604a686 from=translated src=- shape=60f075b6 vocab=31792fa7
-/
lemma mono
    {P Q : Subgroup G → Prop}
    (hPQ : ∀ H, P H → Q H) :
    InducedCharacterSpan (k := k) P ≤ InducedCharacterSpan Q := by
  rw [InducedCharacterSpan, Submodule.span_le]
  rintro _ ⟨H, hH, V, rfl⟩
  exact Submodule.subset_span ⟨H, hPQ H hH, V, rfl⟩

/--
Multiplication on the left by the character of a representation preserves an
induced-character span.
@isnad1 id=mem.1h5v.s8.408dfbe85990 from=translated src=- shape=e47fcf85 vocab=8b53588b
-/
lemma character_mul_mem
    (P : Subgroup G → Prop)
    (V : FDRep k G)
    {φ : ClassFun k G}
    (hφ : φ ∈ InducedCharacterSpan P) :
    ClassFun.character V * φ ∈ InducedCharacterSpan P := by
  refine Submodule.span_induction
    (p := fun θ _ =>
      ClassFun.character V * θ ∈ InducedCharacterSpan P)
    ?gen ?zero ?add ?smul hφ
  · rintro θ ⟨H, hH, W, rfl⟩
    rw [ClassFun.projection_formula
      H (ClassFun.character V) (ClassFun.character W)]
    rw [ClassFun.res_ofChar (H := H) V]
    rw [← ClassFun.char_tensor]
    exact inducedCharacter_mem
      H hH (FDRep.tensor (FDRep.res V H) W)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro n x _ hx
    have hcomm :
        ClassFun.character V * (n • x) =
          n • (ClassFun.character V * x) := by
      ext g
      simp only [ClassFun.mul_apply, ClassFun.zsmul_apply]
      rw [mul_smul_comm n]
    rw [hcomm]
    exact Submodule.smul_mem _ n hx

/--
Multiplication on the left by an element of the character span preserves an
induced-character span.
@isnad1 id=mem.2h5v.s8.9b68f149736d from=translated src=- shape=0746d49b vocab=950d15d4
-/
lemma characterSpan_mul_mem
    (P : Subgroup G → Prop)
    {φ ψ : ClassFun k G}
    (hφ : φ ∈ ClassFun.characterSpan k G)
    (hψ : ψ ∈ InducedCharacterSpan P) :
    φ * ψ ∈ InducedCharacterSpan P := by
  change
    φ ∈ Submodule.span ℤ (ClassFun.characterSet k G)
    at hφ
  refine Submodule.span_induction
    (p := fun θ _ => θ * ψ ∈ InducedCharacterSpan P)
    ?gen ?zero ?add ?smul hφ
  · rintro _ ⟨V, rfl⟩
    exact character_mul_mem P V hψ
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro n x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ n hx

/--
Induction from a subgroup maps one induced-character span into another,
provided the subgroup predicate is preserved when subgroups are mapped into
the ambient group.
@isnad1 id=mem.1h7v.s9.179d16c7bc69 from=translated src=- shape=a106ba5e vocab=8cf9e5fb
-/
lemma induction_mem
    {H : Subgroup G}
    {P : Subgroup H → Prop}
    {Q : Subgroup G → Prop}
    (hmap : ∀ K : Subgroup H, P K → Q (K.map H.subtype))
    {ψ : ClassFun k H}
    (hψ : ψ ∈ InducedCharacterSpan P) :
    ClassFun.ind H ψ ∈ InducedCharacterSpan Q := by
  refine Submodule.span_induction
    (p := fun f _ =>
      ClassFun.ind H f ∈ InducedCharacterSpan Q)
    ?gen ?zero ?add ?smul hψ

  · rintro f ⟨K, hK, W, rfl⟩
    let K_G : Subgroup G := K.map H.subtype
    let eK : K ≃* K_G :=
      K.equivMapOfInjective H.subtype Subtype.coe_injective
    let W_G : FDRep k K_G := FDRep.transport eK W
    have h_transport_char :
        ClassFun.character W_G =
          (ClassFun.equivOfMulEquiv eK).symm
            (ClassFun.character W) := by
      ext x
      rfl
    rw [ClassFun.ind_trans (K := H) (H := K) (ClassFun.character W)]
    rw [← h_transport_char]
    exact inducedCharacter_mem (P := Q) K_G (hmap K hK) W_G
  · rw [ClassFun.ind_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [ClassFun.ind_add]
    exact Submodule.add_mem _ hx hy
  · intro n x _ hx
    rw [ClassFun.ind_zsmul]
    exact Submodule.smul_mem _ n hx

end InducedCharacterSpan

section InducedCharacterIdeal

/--
The ideal of the character ring generated by characters induced from
representations of subgroups satisfying `P`.-/
def InducedCharacterIdeal
    (P : Subgroup G → Prop) :
    Ideal (ClassFun.CharacterRing k G) where
  carrier :=
    {φ | (φ : ClassFun k G) ∈ InducedCharacterSpan P}
  zero_mem' := by
    change (0 : ClassFun k G) ∈ InducedCharacterSpan P
    exact Submodule.zero_mem _
  add_mem' := by
    intro φ ψ hφ hψ
    change
      (φ : ClassFun k G) + (ψ : ClassFun k G) ∈ InducedCharacterSpan P
    exact Submodule.add_mem _ hφ hψ
  smul_mem' := by
    intro φ ψ hψ
    change
      (φ : ClassFun k G) * (ψ : ClassFun k G) ∈ InducedCharacterSpan P
    exact InducedCharacterSpan.characterSpan_mul_mem P φ.property hψ

namespace InducedCharacterIdeal

/--
@isnad1 id=iff.0h4v.s10.c1553f6f59ce from=translated src=- shape=0bab0a03 vocab=f9cbdce9
-/
@[simp]
lemma mem_iff
    (P : Subgroup G → Prop)
    (φ : ClassFun.CharacterRing k G) :
    φ ∈ InducedCharacterIdeal P ↔
      (φ : ClassFun k G) ∈ InducedCharacterSpan P :=
  Iff.rfl

/--
An implication between subgroup predicates induces an inclusion between the
corresponding induced-character ideals.
@isnad1 id=le.0h5v.s10.7691c4f17e0c from=translated src=- shape=5d7040bc vocab=28f527c2
-/
lemma mono
    {P Q : Subgroup G → Prop}
    (hPQ : ∀ H, P H → Q H) :
    InducedCharacterIdeal P ≤ InducedCharacterIdeal (k := k) Q := by
  intro φ hφ
  exact InducedCharacterSpan.mono hPQ hφ

end InducedCharacterIdeal

end InducedCharacterIdeal

section BrauerSpanChar

/--
The `ℤ`-span of characters induced from representations of Brauer-elementary
subgroups.-/
def BrauerSpanChar :
    Submodule ℤ (ClassFun k G) :=
  InducedCharacterSpan (fun H => IsBrauerElementary H)

/--
The ideal of the character ring consisting of integral combinations of
characters induced from representations of Brauer-elementary subgroups.-/
def BrauerIdeal :
    Ideal (ClassFun.CharacterRing k G) :=
  InducedCharacterIdeal (fun H => IsBrauerElementary H)

namespace BrauerIdeal

/--
@isnad1 id=iff.0h3v.s10.b4d1f70df4f6 from=translated src=- shape=90eee97b vocab=c48ddf71
-/
@[simp]
lemma mem_iff
    (φ : ClassFun.CharacterRing k G) :
    φ ∈ BrauerIdeal ↔ (φ : ClassFun k G) ∈ BrauerSpanChar :=
  Iff.rfl

end BrauerIdeal

namespace BrauerSpanChar

/--
Multiplication on the left by an arbitrary virtual character preserves
membership in `BrauerSpanChar`.
@isnad1 id=mem.2h4v.s8.5ba2e73ada9b from=translated src=- shape=e3c335ce vocab=4aeb0c60
-/
lemma characterSpan_mul_mem
    {φ ψ : ClassFun k G}
    (hφ : φ ∈ ClassFun.characterSpan k G)
    (hψ : ψ ∈ BrauerSpanChar) :
    φ * ψ ∈ BrauerSpanChar :=
  InducedCharacterSpan.characterSpan_mul_mem
    (fun H => IsBrauerElementary H) hφ hψ

/--
Multiplication on the left by the character of a representation preserves
membership in `BrauerSpanChar`.
@isnad1 id=mem.1h4v.s8.70d95bd09904 from=translated src=- shape=91a3cd9a vocab=21611f5a
-/
lemma character_mul_mem
    (V : FDRep k G)
    {φ : ClassFun k G}
    (hφ : φ ∈ BrauerSpanChar) :
    ClassFun.character V * φ ∈ BrauerSpanChar :=
  characterSpan_mul_mem
    (ClassFun.characterSpan.character_mem V) hφ

/--
Induction from a subgroup preserves membership in `BrauerSpanChar`.
@isnad1 id=mem.1h4v.s9.c63c9765e119 from=translated src=- shape=39ae1542 vocab=958390cd
-/
lemma induction_mem
    {H : Subgroup G}
    {ψ : ClassFun k H}
    (hψ :
      ψ ∈ BrauerSpanChar (G := H)) :
    ClassFun.ind H ψ ∈ BrauerSpanChar := by
  apply InducedCharacterSpan.induction_mem
    (P := fun K : Subgroup H => IsBrauerElementary K)
    (Q := fun K : Subgroup G => IsBrauerElementary K)
    ?_ hψ
  intro K hK
  exact IsBrauerElementary.ofMulEquiv
    hK (K.equivMapOfInjective H.subtype Subtype.coe_injective)

end BrauerSpanChar

end BrauerSpanChar

end BrauerInduction
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
