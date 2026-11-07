/-
Copyright (c) 2025 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Tengoku.Cslib.Cslib.Foundations.Relation.Defs
public import Tengoku.Seed.Order.WellFounded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Basic properties of relations

## TODO:
Many of the results here could be upstreamed to Mathlib. In particular:
- `ReflGen.le_reflGen` and relatives,
- `ReflGen.to_eqvGen` and relatives.
-/

@[expose] public section

variable {α : Type*} {r r₁ r₂ : α → α → Prop}

/--
@isnad1 id=wellfoun.1h2v.s4.dbb75afe7bf5 from=translated src=- shape=2bbe7c34 vocab=8cf92ed9
-/
theorem WellFounded.ofTransGen (trans_wf : WellFounded (Relation.TransGen r)) : WellFounded r := by
  grind [WellFounded.wellFounded_iff_has_min, Relation.TransGen]

/--
@isnad1 id=iff.0h2v.s4.8b3067419e15 from=translated src=- shape=196764fe vocab=8cf92ed9
-/
@[simp, grind =]
theorem WellFounded.iff_transGen : WellFounded (Relation.TransGen r) ↔ WellFounded r :=
  ⟨ofTransGen, transGen⟩

namespace Relation

open Function

/-- A pair of subrelations lifts to transitivity on the relation.-/
@[implicit_reducible]
def transLeftRight (s s' r : α → α → Prop) [IsTrans α r] (h : s ≤ r) (h' : s' ≤ r) :
    Trans s s' r where
  trans hab hbc := _root_.trans (h _ _ hab) (h' _ _ hbc)

/-- A subrelation lifts to transitivity on the left of the relation.-/
@[implicit_reducible]
def transLeft (s r : α → α → Prop) [IsTrans α r] (h : s ≤ r) : Trans s r r where
  trans hab hbc := _root_.trans (h _ _ hab) hbc

/-- A subrelation lifts to transitivity on the right of the relation.-/
@[implicit_reducible]
def transRight (s r : α → α → Prop) [IsTrans α r] (h : s ≤ r) : Trans r s r where
  trans hab hbc := _root_.trans hab (h _ _ hbc)

/--
@isnad1 id=le.2h5v.s6.7ec52cb916e4 from=translated src=- shape=9af7a006 vocab=73c0d0a9
-/
@[scoped grind .]
theorem comp_le_comp {s s' r r' : α → α → Prop} (hs : s ≤ s') (hr : r ≤ r') :
    Comp s r ≤ Comp s' r' := fun a c ⟨b, hab, hbc⟩ ↦ ⟨b, hs a b hab, hr b c hbc⟩

/--
@isnad1 id=le.0h2v.s5.a541259cfdb6 from=translated src=- shape=fccc6ed2 vocab=cd1f5676
-/
theorem comp_self_le (r : α → α → Prop) [IsTrans α r] : Comp r r ≤ r :=
  fun _ _ ⟨_, hab, hbc⟩ ↦ _root_.trans hab hbc

/--
@isnad1 id=iff.0h3v.s6.d1f7d314f693 from=translated src=- shape=3089acda vocab=91390479
-/
theorem swap_le_iff_le_swap {r₁ r₂ : α → α → Prop} : swap r₁ ≤ r₂ ↔ r₁ ≤ swap r₂ := by
  constructor <;> intro h a b hab <;> exact h b a hab

attribute [scoped grind] ReflGen TransGen ReflTransGen EqvGen

/--
@isnad1 id=le.0h2v.s5.8432560671f7 from=translated src=- shape=b9650280 vocab=f44580d3
-/
@[scoped grind .]
theorem ReflGen.le_reflGen : r ≤ ReflGen r := fun _ _ => ReflGen.single

/--
@isnad1 id=eqvgen.1h4v.s4.fa0a88a04563 from=translated src=- shape=a664b5d2 vocab=3a18cc82
-/
theorem ReflGen.to_eqvGen (h : ReflGen r a b) : EqvGen r a b :=
  EqvGen.reflGen_le_eqvGen r _ _ h

/--
@isnad1 id=le.0h2v.s5.aa733ad75402 from=translated src=- shape=b9650280 vocab=cdca28b5
-/
@[scoped grind .]
theorem TransGen.le_transGen : r ≤ TransGen r := fun _ _ => TransGen.single

/--
@isnad1 id=eqvgen.1h4v.s4.d5df17a838af from=translated src=- shape=a664b5d2 vocab=95faa801
-/
theorem TransGen.to_eqvGen (h : TransGen r a b) : EqvGen r a b :=
  EqvGen.transGen_le_eqvGen r _ _ h

/--
@isnad1 id=eqvgen.1h4v.s4.2fb46eddce4c from=translated src=- shape=a664b5d2 vocab=fabca640
-/
theorem ReflTransGen.to_eqvGen (h : ReflTransGen r a b) : EqvGen r a b :=
  EqvGen.reflTransGen_le_eqvGen r _ _ h

/--
@isnad1 id=le.0h2v.s5.4101597f645c from=translated src=- shape=b9650280 vocab=f97de9bb
-/
@[scoped grind .]
theorem SymmGen.le_symmGen : r ≤ SymmGen r := fun _ _ => Or.inl

/--
@isnad1 id=eqvgen.1h4v.s4.2041c8092482 from=translated src=- shape=a664b5d2 vocab=6b2dc54b
-/
theorem SymmGen.to_eqvGen (h : SymmGen r a b) : EqvGen r a b :=
  EqvGen.symmGen_le_eqvGen r _ _ h

/--
@isnad1 id=eq.0h2v.s5.2c071948a920 from=translated src=- shape=b1b3d4a2 vocab=790378df
-/
@[simp, scoped grind =] theorem sup_swap_eq_symmGen : r ⊔ Function.swap r = SymmGen r := rfl

/--
@isnad1 id=le.0h2v.s5.8c8c1d4ba965 from=translated src=- shape=b9650280 vocab=66e23510
-/
@[scoped grind .]
theorem EqvGen.le_eqvGen : r ≤ EqvGen r := EqvGen.rel

/--
@isnad1 id=le.2h3v.s6.fdbce401ed7a from=translated src=- shape=f891221e vocab=7a91006f
-/
theorem _root_.Equivalence.eqvGen_le (h : Equivalence r₂) (hle : r₁ ≤ r₂) : EqvGen r₁ ≤ r₂ :=
  have := h.isEquiv
  EqvGen.eqvGen_le hle

attribute [scoped grind →] ReflGen.to_eqvGen TransGen.to_eqvGen ReflTransGen.to_eqvGen
  SymmGen.to_eqvGen

/--
@isnad1 id=join.0h5v.s4.d680f8812f6e from=translated src=- shape=d8325356 vocab=b7a776e6
-/
theorem Join.single [Std.Refl r] (h : r a b) : Join r a b := ⟨b, h, refl b⟩

/--
@isnad1 id=eq.0h2v.s4.59c1bb4ad88d from=translated src=- shape=0bb4ffa3 vocab=7618028f
-/
@[simp, scoped grind =] theorem join₂_eq_join : Join₂ r r = Join r := rfl

/--
@isnad1 id=eq.0h3v.s5.d484f4cc03cc from=translated src=- shape=506f5aa0 vocab=57ae1d1a
-/
theorem join₂_eq_comp_swap : Join₂ r₁ r₂ = Comp r₁ (swap r₂) := rfl

instance [Std.Refl r₁] [Std.Refl r₂] : Std.Refl (Join₂ r₁ r₂) where
  refl a := ⟨a, refl a, refl a⟩

/--
@isnad1 id=join.0h6v.s5.7b67f6cacdd8 from=translated src=- shape=2ad6f82d vocab=39d114ad
-/
theorem Join₂.single_left [Std.Refl r₂] (h : r₁ a b) : Join₂ r₁ r₂ a b := ⟨b, h, refl b⟩

/--
@isnad1 id=join.0h6v.s5.73caadbe6510 from=translated src=- shape=d354006e vocab=39d114ad
-/
theorem Join₂.single_right [Std.Refl r₁] (h : r₂ a b) : Join₂ r₁ r₂ b a := ⟨b, refl b, h⟩

/--
@isnad1 id=le.2h4v.s6.9fdc10732aec from=translated src=- shape=43b74f1f vocab=f8e76f4d
-/
theorem Join₂.join₂_le [IsTrans α r] (h₁ : r₁ ≤ r) (h₂ : swap r₂ ≤ r) : Join₂ r₁ r₂ ≤ r :=
  (comp_le_comp h₁ h₂).trans (comp_self_le r)

/--
@isnad1 id=iff.0h5v.s4.abade864b52b from=translated src=- shape=d385fe60 vocab=db13c8bb
-/
theorem Join₂.swap_iff {a b : α} : Join₂ r₁ r₂ b a ↔ Join₂ r₂ r₁ a b := by grind [Join₂]

/--
@isnad1 id=le.2h5v.s6.3ce5b44fba5f from=translated src=- shape=d28aab15 vocab=08bebbf0
-/
protected theorem Join₂.mono (h₁ : r₁ ≤ r₁') (h₂ : r₂ ≤ r₂') : Join₂ r₁ r₂ ≤ Join₂ r₁' r₂' :=
  fun x y ⟨z, hxz, hyz⟩ => ⟨z, h₁ x z hxz, h₂ y z hyz⟩

/--
@isnad1 id=mjoin.0h3v.s3.a5aee79c2b1c from=translated src=- shape=dbdb3b9b vocab=143e6045
-/
@[deprecated _root_.refl +typeChanged (since := "2026-09-07")]
theorem MJoin.refl (a : α) : MJoin r a a := _root_.refl a

/--
@isnad1 id=mjoin.1h4v.s4.95749f64b008 from=translated src=- shape=a664b5d2 vocab=c5ca10da
-/
@[deprecated Join.single +typeChanged (since := "2026-09-07")]
theorem MJoin.single (h : ReflTransGen r a b) : MJoin r a b := Join.single h

/--
@isnad1 id=le.2h3v.s6.336a2c8e909a from=translated src=- shape=a04afc63 vocab=aa6b35a3
-/
theorem _root_.Equivalence.join_reflTransGen_le (h : Equivalence r₂) (hle : r₁ ≤ r₂) :
    Join (ReflTransGen r₁) ≤ r₂ :=
  have := h.isEquiv
  join_le_of_equivalence_of_le h <| reflTransGen_le_of_le hle

/--
@isnad1 id=le.0h2v.s5.c7a2ecf22f75 from=translated src=- shape=8a2cfc4e vocab=c6e3f46b
-/
theorem join_reflTransGen_le_eqvGen : Join (ReflTransGen r) ≤ EqvGen r :=
    (EqvGen.is_equivalence r).join_reflTransGen_le EqvGen.le_eqvGen

/--
@isnad1 id=le.2h4v.s6.7982bbef41a2 from=translated src=- shape=ce3e4822 vocab=4261472d
-/
theorem join₂_reflTransGen_le [Std.Refl r] [IsTrans α r] (h₁ : r₁ ≤ r) (h₂ : swap r₂ ≤ r) :
    Join₂ (ReflTransGen r₁) (ReflTransGen r₂) ≤ r := by
  refine Join₂.join₂_le ?_ (ReflTransGen.swap.trans ?_)
    <;> apply reflTransGen_le_of_le <;> assumption

/--
@isnad1 id=le.2h4v.s6.c0fd431c6ab0 from=translated src=- shape=b39f383c vocab=ee01ba51
-/
theorem join₂_reflTransGen_le_of_isEquiv [IsEquiv α r] (h₁ : r₁ ≤ r) (h₂ : r₂ ≤ r) :
    Join₂ (ReflTransGen r₁) (ReflTransGen r₂) ≤ r :=
  join₂_reflTransGen_le h₁ (by rwa [swap_le_iff_le_swap, Std.Symm.swap_eq])

/--
@isnad1 id=le.3h4v.s6.a63b3d843b04 from=translated src=- shape=b39f383c vocab=e585897f
-/
theorem _root_.Equivalence.join₂_reflTransGen_le (h : Equivalence r) (h₁ : r₁ ≤ r) (h₂ : r₂ ≤ r) :
    Join₂ (ReflTransGen r₁) (ReflTransGen r₂) ≤ r :=
  have := h.isEquiv
  join₂_reflTransGen_le_of_isEquiv h₁ h₂

/--
@isnad1 id=le.0h3v.s5.a34e82ce7f54 from=translated src=- shape=ed43dd49 vocab=f802b066
-/
theorem left_le_join₂_reflTransGen : r₁ ≤ Join₂ (ReflTransGen r₁) (ReflTransGen r₂) :=
  fun _ _ h => Join₂.single_left (.single h)

/--
@isnad1 id=le.0h3v.s5.ddf686c5067c from=translated src=- shape=3c30e741 vocab=3665c109
-/
theorem swap_right_le_join₂_reflTransGen : swap r₂ ≤ Join₂ (ReflTransGen r₁) (ReflTransGen r₂) :=
    fun _ _ h => Join₂.single_right (.single h)

/-- If a relation is squeezed by a relation and its multi-step closure, they are multi-step equal
@isnad1 id=eq.2h3v.s6.8e7788847929 from=translated src=- shape=cbaeeb79 vocab=b09fdaa5
-/
theorem reflTransGen_mono_closed (h₁ : r₁ ≤ r₂) (h₂ : r₂ ≤ ReflTransGen r₁) :
    ReflTransGen r₁ = ReflTransGen r₂ := by
  ext a b
  exact ⟨ReflTransGen.mono h₁ a b, reflTransGen_closed h₂ a b⟩

/--
@isnad1 id=reflgen.1h4v.s4.6f122871e3dc from=translated src=- shape=6000f390 vocab=58764521
-/
@[deprecated Relation.ReflGen.stdSymm +typeChanged (since := "2026-09-03")]
lemma ReflGen.symmGen_symm : ReflGen (SymmGen r) a b → ReflGen (SymmGen r) b a :=
  Std.Symm.symm a b

/--
@isnad1 id=eq.0h2v.s4.60f4a9d423ff from=translated src=- shape=8a2cfc4e vocab=feee384c
-/
@[simp, scoped grind =]
theorem reflTransGen_symmGen : ReflTransGen (SymmGen r) = EqvGen r := EqvGen.reflTransGen_symmGen r

/--
@isnad1 id=max.0h6v.s5.9b8e3dee1f22 from=translated src=- shape=1b044b0c vocab=e500c4df
-/
@[scoped grind <=]
theorem join_inl (r₁_ab : r₁ a b) : (r₁ ⊔ r₂) a b :=
  Or.inl r₁_ab

/--
@isnad1 id=max.0h6v.s5.a6ef65c0de8f from=translated src=- shape=8792c287 vocab=e500c4df
-/
@[scoped grind <=]
theorem join_inr (r₂_ab : r₂ a b) : (r₁ ⊔ r₂) a b :=
  Or.inr r₂_ab

/--
@isnad1 id=refltran.1h5v.s6.a50cac3b11c4 from=translated src=- shape=6b6a7573 vocab=241cf4e3
-/
@[scoped grind <=]
theorem join_inl_reflTransGen (r₁_ab : ReflTransGen r₁ a b) : ReflTransGen (r₁ ⊔ r₂) a b :=
  ReflTransGen.mono le_sup_left _ _ r₁_ab

/--
@isnad1 id=refltran.1h5v.s6.067734e43407 from=translated src=- shape=78c119dc vocab=241cf4e3
-/
@[scoped grind <=]
theorem join_inr_reflTransGen (r₂_ab : ReflTransGen r₂ a b) : ReflTransGen (r₁ ⊔ r₂) a b :=
  ReflTransGen.mono le_sup_right _ _ r₂_ab

end Relation
