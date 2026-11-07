/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Tengoku.Cslib.Cslib.Foundations.Relation.Restriction
public import Tengoku.Seed.Data.Fintype.EquivFin
public import Tengoku.Seed.Tactic.TFAE

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Relations: Euclidean Relations

This module proves basic properties about left and right Euclidean relations, which are use
in modal logic.

TODO: develop an attribute to dualize theorems to the converse of a relation

## References

* [*Simple Laws about Nonprominent Properties of Binary Relations*][Burghardt2018]

-/

@[expose] public section

open Relator

namespace Relation

variable {α : Type*} {r : α → α → Prop}

instance [RightEuclidean r] (s : Set α) : RightEuclidean (α := s) r :=
  ⟨RightEuclidean.rightEuclidean⟩

instance [LeftEuclidean r] (s : Set α) : LeftEuclidean (α := s) r :=
  ⟨LeftEuclidean.leftEuclidean⟩

/--
@isnad1 id=serial.1h2v.s3.37b74a73b747 from=translated src=- shape=6e704b37 vocab=150d06d4
-/
@[scoped grind →]
lemma refl_serial (r : α → α → Prop) (h : Std.Refl r) : Serial r where
  serial a := ⟨a, h.refl a⟩

namespace RightEuclidean

variable [RightEuclidean r]

/-- A `RightEuclidean` relation is reflexive on its codomain
@isnad1 id=reflon.0h2v.s4.d505494af858 from=translated src=- shape=1d6c36f0 vocab=55e0c897
-/
theorem reflOn_cod : (cod r).ReflOn r := fun _ ⟨_, ab⟩ ↦ rightEuclidean ab ab

/-- The converse of a `RightEuclidean` relation is `LeftEuclidean`
@isnad1 id=lefteucl.0h2v.s4.74a1c49f3feb from=translated src=- shape=aa286835 vocab=2e1437e1
-/
theorem leftEuclidean_swap : LeftEuclidean (fun a b => r b a) where
  leftEuclidean ca cb := rightEuclidean cb ca

instance [Std.Refl r] : Std.Symm r where
  symm a _ ab := rightEuclidean ab (refl a)

/--
@isnad1 id=istrans.0h2v.s4.9f762140fdf5 from=translated src=- shape=b478ed8f vocab=87386839
-/
theorem trichotomous_trans [Std.Trichotomous r] : IsTrans α r where
  trans a b c ab bc := by
    have := Std.Trichotomous.trichotomous (r := r) a c
    have cc := reflOn_cod.of_cod bc
    have (ca : r c a) := rightEuclidean ca cc
    grind

/--
@isnad1 id=rightuni.0h2v.s4.bd17a49182df from=translated src=- shape=cda235d3 vocab=88db491b
-/
theorem antisymm_rightUnique [Std.Antisymm r] : Relator.RightUnique r := by
  intros a b c ab ac
  exact antisymm (rightEuclidean ab ac) (rightEuclidean ac ab)

/--
@isnad1 id=antisymm.1h2v.s4.f567baa86c2d from=translated src=- shape=8272d177 vocab=88db491b
-/
theorem rightUnique_antisymm (h : Relator.RightUnique r) : Std.Antisymm r where
  antisymm _ _ ab ba := h ba (reflOn_cod.of_cod ab)

/--
@isnad1 id=istrans.1h2v.s4.d73abb3161ef from=translated src=- shape=8272d177 vocab=77a6ab2c
-/
theorem rightUnique_trans (h : Relator.RightUnique r) : IsTrans α r where
  trans a b c ab bc := by
    have eq : c = b := h bc (reflOn_cod.of_cod ab)
    simpa [eq]

/--
@isnad1 id=isequiv.1h2v.s4.27e11415b7af from=translated src=- shape=8272d177 vocab=2e651042
-/
theorem rightTotal_equiv (h : Relator.RightTotal r) : IsEquiv α r := by
  have : Std.Refl r := ⟨fun a => reflOn_cod.of_cod (h a).choose_spec⟩
  exact {toIsTrans := ⟨fun _ _ _ ab bc => rightEuclidean (symm ab) bc⟩}

omit [RightEuclidean r] in
/--
@isnad1 id=righteuc.2h2v.s4.a46d0ab859dc from=translated src=- shape=410360d3 vocab=6dd9e8f1
-/
theorem leftTotal_rightUnique_trans (h₁ : LeftTotal r) (h₂ : RightUnique r) [IsTrans α r] :
    RightEuclidean r where
  rightEuclidean {a b c} ab ac := by
    obtain ⟨d, dc⟩ := h₁ c
    have : b = c := h₂ ab ac
    have : d = c := h₂ (_root_.trans ac dc) ac
    grind

private theorem three_contra [Std.Trichotomous r] [Std.Antisymm r] :
    ¬ ∃ (a b c : α), a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  rintro ⟨a, b, c, _⟩
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ a b
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ a c
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ b c
  have := antisymm_rightUnique (r := r)
  have := @reflOn_cod (r := r)
  simp [Set.ReflOn] at this
  grind [Relator.RightUnique]

/--
@isnad1 id=finite.0h2v.s4.1691484469b7 from=translated src=- shape=e503586a vocab=758541dc
-/
theorem trichotomous_antisymm_finite [Std.Trichotomous r] [Std.Antisymm r] : Finite α := by
  classical
  by_contra! h
  apply three_contra (r := r)
  have ⟨_, hcard⟩ := Infinite.exists_subset_card_eq α 3
  have ⟨a, b, c, _, _, _, _⟩ := Finset.card_eq_three.mp hcard
  use a, b, c

/--
@isnad1 id=le.0h2v.s5.1dbc75943e71 from=translated src=- shape=fc346288 vocab=6f6d5f59
-/
theorem trichotomous_antisymm_card [Std.Trichotomous r] [Std.Antisymm r] [Fintype α] :
    Fintype.card α ≤ 2 := by
  by_contra! h
  apply three_contra (r := r)
  have ⟨a, b, c, _⟩ := Fintype.two_lt_card_iff.mp h
  use a, b, c

/--
@isnad1 id=le.0h2v.s4.686893152fff from=translated src=- shape=3c25f864 vocab=0e933e21
-/
theorem cod_subset_dom : cod r ⊆ dom r := fun _ ⟨_, ab⟩ ↦ of_cod (reflOn_cod.of_cod ab)

/--
@isnad1 id=righttot.0h2v.s6.75b81e3b30b6 from=translated src=- shape=2aafe64f vocab=36abf68d
-/
theorem rightTotal_cod : Relator.RightTotal (α := cod r) (β := cod r) r :=
  fun ⟨_, _, h⟩ => of_cod (reflOn_cod.of_cod h)

/--
@isnad1 id=isequiv.0h2v.s6.7ab5f3e11201 from=translated src=- shape=894063da vocab=b2ea8e7a
-/
theorem equiv_cod : IsEquiv (cod r) r := rightTotal_equiv rightTotal_cod

end RightEuclidean

namespace LeftEuclidean

variable [LeftEuclidean r]

/-- A `LeftEuclidean` relation is reflexive on its domain
@isnad1 id=reflon.0h2v.s4.09d80bb9ebb5 from=translated src=- shape=1d6c36f0 vocab=84fe50e7
-/
theorem reflOn_dom : (dom r).ReflOn r := fun _ ⟨_, ab⟩ ↦ leftEuclidean ab ab

/-- The converse of a `LeftEuclidean` relation is `RightEuclidean`
@isnad1 id=righteuc.0h2v.s4.83507442333d from=translated src=- shape=aa286835 vocab=2e1437e1
-/
@[local instance]
theorem rightEuclidean_swap : RightEuclidean (fun a b => r b a) where
  rightEuclidean ab ac := leftEuclidean ac ab

instance [Std.Refl r] : Std.Symm r where
  symm _ b ab := leftEuclidean (refl b) ab

/--
@isnad1 id=istrans.0h2v.s4.e42cc8216e0a from=translated src=- shape=b478ed8f vocab=d18dbe46
-/
theorem trichotomous_trans [Std.Trichotomous r] : IsTrans α r where
  trans a b c ab bc := by
    have := Std.Trichotomous.trichotomous (r := r) a c
    have aa := reflOn_dom.of_dom ab
    have (ca : r c a) := leftEuclidean aa ca
    grind

/--
@isnad1 id=leftuniq.0h2v.s4.f20a05a8842d from=translated src=- shape=cda235d3 vocab=33bee6f5
-/
theorem antisymm_leftUnique [Std.Antisymm r] : Relator.LeftUnique r := by
  intros a b c ac bc
  exact antisymm (leftEuclidean ac bc) (leftEuclidean bc ac)

/--
@isnad1 id=antisymm.1h2v.s4.ae8bb174b7a0 from=translated src=- shape=8272d177 vocab=33bee6f5
-/
theorem leftUnique_antisymm (h : Relator.LeftUnique r) : Std.Antisymm r where
  antisymm _ _ ab ba := h ab (reflOn_dom.of_dom ba)

/--
@isnad1 id=istrans.1h2v.s4.c092ea3cedf3 from=translated src=- shape=8272d177 vocab=45879838
-/
theorem leftUnique_trans (h : Relator.LeftUnique r) : IsTrans α r where
  trans a b c ab bc := by
    have eq : a = b := h ab (reflOn_dom.of_dom bc)
    simpa [eq]

/--
@isnad1 id=isequiv.1h2v.s4.67012d292735 from=translated src=- shape=8272d177 vocab=a148d73f
-/
theorem leftTotal_equiv (h : Relator.LeftTotal r) : IsEquiv α r := by
  have : Std.Refl r := ⟨fun a => reflOn_dom.of_dom (h a).choose_spec⟩
  exact {toIsTrans := ⟨fun _ _ _ ab bc => leftEuclidean ab (symm bc)⟩}

omit [LeftEuclidean r] in
/--
@isnad1 id=lefteucl.2h2v.s4.5e43823a2019 from=translated src=- shape=410360d3 vocab=087baa96
-/
theorem rightTotal_leftUnique_trans (h₁ : RightTotal r) (h₂ : LeftUnique r) [IsTrans α r] :
    LeftEuclidean r where
  leftEuclidean {a b c} ac bc := by
    obtain ⟨d, da⟩ := h₁ a
    have : a = b := h₂ ac bc
    have : a = d := h₂ ac (_root_.trans da ac)
    grind

/--
@isnad1 id=finite.0h2v.s4.bebe689a3651 from=translated src=- shape=e503586a vocab=9cea8c8d
-/
theorem trichotomous_antisymm_finite [Std.Trichotomous r] [Std.Antisymm r] : Finite α :=
  RightEuclidean.trichotomous_antisymm_finite (r := Function.swap r)

/--
@isnad1 id=le.0h2v.s5.86dab1f215e1 from=translated src=- shape=fc346288 vocab=d5db2e66
-/
theorem trichotomous_antisymm_card [Std.Trichotomous r] [Std.Antisymm r] [Fintype α] :
    Fintype.card α ≤ 2 :=
  RightEuclidean.trichotomous_antisymm_card (r := Function.swap r)

/--
@isnad1 id=le.0h2v.s4.81cfca52f65a from=translated src=- shape=3c25f864 vocab=9fcbbc3e
-/
theorem dom_subset_cod : dom r ⊆ cod r := fun _ ⟨_, ab⟩ ↦ of_dom (reflOn_dom.of_dom ab)

/--
@isnad1 id=lefttota.0h2v.s6.ee6eb01e2b77 from=translated src=- shape=2aafe64f vocab=846fd1a5
-/
theorem leftTotal_dom : Relator.LeftTotal (α := dom r) (β := dom r) r :=
  fun ⟨a, _, h⟩ => ⟨⟨a, of_dom h⟩, reflOn_dom.of_dom h⟩

/--
@isnad1 id=isequiv.0h2v.s6.0a52cc47e611 from=translated src=- shape=894063da vocab=68afce4d
-/
theorem equiv_dom : IsEquiv (dom r) r := leftTotal_equiv leftTotal_dom

end LeftEuclidean

section euclidean_symm

variable [Std.Symm r]

open RightEuclidean LeftEuclidean in
private theorem symm_equivalents : [RightEuclidean r, LeftEuclidean r, IsTrans α r].TFAE := by
  tfae_have 1 → 2 := fun _ => ⟨fun ac bc => rightEuclidean (symm ac) (symm bc)⟩
  tfae_have 2 → 3 := fun _ => ⟨fun _ _ _ ab bc => leftEuclidean ab (symm bc)⟩
  tfae_have 3 → 1 := fun _ => ⟨fun ab ac => _root_.trans (symm ab) ac⟩
  tfae_finish

/-- For a symmetric relation, `LeftEuclidean` and `RightEuclidean` are equivalent.
@isnad1 id=iff.0h2v.s4.1675d0c18db5 from=translated src=- shape=b62ffb35 vocab=7c29c4b9
-/
theorem symm_leftEuclidean_iff_rightEuclidean : LeftEuclidean r ↔ RightEuclidean r :=
  List.TFAE.out symm_equivalents 2 1

/-- For a symmetric relation, `LeftEuclidean` and transitivity are equivalent.
@isnad1 id=iff.0h2v.s4.af918d4f9f27 from=translated src=- shape=b62ffb35 vocab=1ed3d083
-/
theorem symm_leftEuclidean_iff_trans : LeftEuclidean r ↔  IsTrans α r :=
  List.TFAE.out symm_equivalents 2 3

/-- For a symmetric relation, `RightEuclidean` and transitivity are equivalent.
@isnad1 id=iff.0h2v.s4.5e9759120c15 from=translated src=- shape=b62ffb35 vocab=428a1c04
-/
theorem symm_rightEuclidean_iff_trans : RightEuclidean r ↔ IsTrans α r :=
  List.TFAE.out symm_equivalents 1 3

end euclidean_symm

/--
@isnad1 id=eq.0h2v.s4.2dea07f481b5 from=translated src=- shape=a05a8275 vocab=1b6697e0
-/
theorem leftEuclidean_rightEuclidean_dom_cod_eq [LeftEuclidean r] [RightEuclidean r] :
    dom r = cod r := by
  have : dom r ⊆ cod r := LeftEuclidean.dom_subset_cod
  have : cod r ⊆ dom r := RightEuclidean.cod_subset_dom
  grind

/--
@isnad1 id=lefteucl.1h2v.s6.435d5ab27cb6 from=translated src=- shape=0cb47783 vocab=a5bdd7b6
-/
theorem dom_cod_leftEuclidean (eq : dom r = cod r) [equiv_dom : IsEquiv (dom r) r] :
    LeftEuclidean r where
  leftEuclidean {a b c} ac bc := by
    have cb : r c b := equiv_dom.symm ⟨_, _, bc⟩ ⟨c, by grind⟩ bc
    exact equiv_dom.trans ⟨_, _, ac⟩ ⟨_, _, cb⟩ ⟨_, by grind⟩ ac cb

/--
@isnad1 id=righteuc.1h2v.s6.ae15dcb90f4f from=translated src=- shape=0cb47783 vocab=65e90a2a
-/
lemma dom_cod_rightEuclidean (eq : dom r = cod r) [equiv_dom : IsEquiv (dom r) r] :
    RightEuclidean r where
  rightEuclidean {a b c} ab ac := by
    have ba : r b a := equiv_dom.symm ⟨a, _, ab⟩ ⟨b, by grind⟩ ab
    exact equiv_dom.trans ⟨_, _, ba⟩ ⟨_, _, ac⟩ ⟨c, by grind⟩ ba ac

/-- A relation is both left and right Euclidean if and only if the relation is an equivalence on
  coinciding domain and codomain.
@isnad1 id=iff.0h2v.s6.877dd7c4638d from=translated src=- shape=cb4ecf0a vocab=ddc781b1
-/
theorem leftEuclidean_rightEuclidean_iff_dom_cod :
    LeftEuclidean r ∧ RightEuclidean r ↔ dom r = cod r ∧ IsEquiv (dom r) r where
  mp := fun ⟨_, _⟩ ↦ ⟨leftEuclidean_rightEuclidean_dom_cod_eq, LeftEuclidean.equiv_dom⟩
  mpr := fun ⟨eq, _⟩ ↦ ⟨dom_cod_leftEuclidean eq, dom_cod_rightEuclidean eq⟩

end Relation
