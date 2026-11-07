/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Tengoku.Cslib.Cslib.Foundations.Relation.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Termination (well-foundedness) properties of relations -/

@[expose] public section

variable {α : Type*} {r r₁ r₂ : α → α → Prop}

namespace Relation

/--
@isnad1 id=iff.0h3v.s4.eac0143fa083 from=translated src=- shape=fbdc40e7 vocab=28e25c45
-/
theorem normal_iff (r : α → α → Prop) (x : α) : Normal r x ↔ ∀ y, ¬ r x y := by
  rw [Normal, not_exists]

/--
@isnad1 id=iff.0h3v.s4.eac0143fa083 from=translated src=- shape=fbdc40e7 vocab=28e25c45
-/
@[deprecated (since := "2026-09-03")] alias Normal_iff := normal_iff

/-- A multi-step from a normal form must be reflexive.
@isnad1 id=eq.2h4v.s4.1e5d3d235e73 from=translated src=- shape=46d930c3 vocab=376a0bbd
-/
@[grind =>]
theorem Normal.reflTransGen_eq (h : Normal r x) (xy : ReflTransGen r x y) : x = y := by
  induction xy <;> grind

/--
@isnad1 id=iff.0h3v.s4.94dadc608381 from=translated src=- shape=4a3ea96e vocab=2157b0ad
-/
lemma SN_iff_SN_of_rel (x : α) : SN r x ↔ ∀ y, r x y → SN r y := by grind [Acc]

/--
@isnad1 id=sn.1h3v.s4.c5611bd1ce34 from=translated src=- shape=ca72848c vocab=2157b0ad
-/
lemma SN.intro : (h : ∀ y, r x y → SN r y) → SN r x := (SN_iff_SN_of_rel x).mpr

/--
@isnad1 id=sn.1h5v.s4.353879274398 from=translated src=- shape=d509d689 vocab=2157b0ad
-/
lemma SN.of_rel (hx : SN r x) (h : r x y) : SN r y := Acc.inv hx h

/--
@isnad1 id=sn.2h4v.s4.7cc376684709 from=translated src=- shape=24f4c90b vocab=5b9acd19
-/
@[grind →]
lemma SN.of_rel_reflTransGen (hx : SN r x) (h : ReflTransGen r x y) : SN r y := by
  induction h with
  | refl => exact hx
  | tail _ h ih => exact ih.of_rel h

/--
@isnad1 id=sn.1h3v.s4.48c200d559d0 from=translated src=- shape=bb8f9edd vocab=8b928e16
-/
lemma SN.transGen (hx : SN r x) : SN (TransGen r) x := by
  have eq : TransGen (Function.swap r) = (fun a b => TransGen r b a) := by
    ext
    exact transGen_swap
  simpa [eq] using Acc.transGen hx

/--
@isnad1 id=sn.2h4v.s5.69bac7254677 from=translated src=- shape=24c0bb28 vocab=68da1b09
-/
lemma SN.of_le {r' : α → α → Prop} (hx : SN r x) (h : r' ≤ r) : SN r' x := by
  refine Subrelation.accessible ?_ hx
  exact subrelation_iff_le.mpr fun {x y} => h y x

/--
@isnad1 id=iff.0h3v.s4.0db61c987429 from=translated src=- shape=87e9cca8 vocab=8b928e16
-/
@[simp]
lemma SN.iff_transGen (x : α) : SN (TransGen r) x ↔ SN r x :=
  ⟨fun hx => hx.of_le <| fun _ _ => TransGen.single, transGen⟩

/-- `SN r x` is equivalent to the more elementary definition, that there is no infinite sequence
of reductions starting with `x`.
@isnad1 id=iff.0h3v.s5.184f3d5f6a3f from=translated src=- shape=b8fc4fab vocab=285d0f5a
-/
theorem SN.iff_isEmpty_chain :
    SN r x ↔ IsEmpty {f : ℕ → α | f 0 = x ∧ ∀ n, r (f n) (f (n + 1))} :=
  acc_iff_isEmpty_descending_chain

/--
@isnad1 id=sn.1h5v.s5.7b7ff987a8d8 from=translated src=- shape=a5733efd vocab=73c9da77
-/
lemma SN.onFun_of_image {r : β → β → Prop} {f : α → β} (hx : SN r (f x)) :
    SN (Function.onFun r f) x := InvImage.accessible f hx

/--
@isnad1 id=sn.1h3v.s4.00fa06f541e6 from=translated src=- shape=f4baa398 vocab=47ca471b
-/
lemma SN.of_normal (hx : Normal r x) : SN r x := SN.intro fun y hy => (hx ⟨y, hy⟩).elim

/--
@isnad1 id=normaliz.1h3v.s4.9403556e3b88 from=translated src=- shape=f4baa398 vocab=5d32b954
-/
theorem SN.normalizable (hx : SN r x) : Normalizable r x := by
  induction hx with | intro x h ih =>
  by_cases hy: (∃ y, r x y)
  · obtain ⟨y, hy⟩ := hy
    obtain ⟨z, hz, hnormal⟩ := ih y hy
    exact ⟨z, .head hy hz, hnormal⟩
  · exists x

/--
@isnad1 id=sn.1h3v.s4.7e17cab804c5 from=translated src=- shape=3c023e8a vocab=e38d1fc2
-/
lemma Terminating.apply (hr : Terminating r) (x : α) : SN r x := WellFounded.apply hr x

/--
@isnad1 id=iff.0h2v.s4.b00e929ae55f from=translated src=- shape=ff227a19 vocab=e38d1fc2
-/
lemma Terminating.iff_forall_sn : Terminating r ↔ ∀ x, SN r x :=
  ⟨WellFounded.apply, WellFounded.intro⟩

/--
@isnad1 id=terminat.1h2v.s4.c5efe6082963 from=translated src=- shape=a1cd675a vocab=a5410e64
-/
theorem Terminating.to_transGen (ht : Terminating r) : Terminating (TransGen r) := by
  simp_rw [iff_forall_sn, SN.iff_transGen] at ht ⊢
  exact ht

/--
@isnad1 id=terminat.1h2v.s4.c5efe6082963 from=translated src=- shape=a1cd675a vocab=a5410e64
-/
@[deprecated (since := "2026-09-03")] alias Terminating.toTransGen := Terminating.to_transGen

/-- A terminating relation is acyclic.
@isnad1 id=acyclic.1h2v.s3.de3e1de01425 from=translated src=- shape=6e704b37 vocab=492ee6b2
-/
theorem Terminating.to_acyclic (ht : Terminating r) : Acyclic r :=
  ⟨fun x hx => ht.to_transGen.irrefl.irrefl x hx⟩

/--
@isnad1 id=acyclic.1h2v.s3.de3e1de01425 from=translated src=- shape=6e704b37 vocab=492ee6b2
-/
@[deprecated (since := "2026-09-03")] alias Terminating.toAcyclic := Terminating.to_acyclic

/--
@isnad1 id=terminat.1h2v.s4.1b61a86be036 from=translated src=- shape=2bbe7c34 vocab=a5410e64
-/
theorem Terminating.of_transGen : Terminating (TransGen r) → Terminating r := by
  simp_rw [iff_forall_sn, SN.iff_transGen]
  exact id

/--
@isnad1 id=terminat.1h2v.s4.1b61a86be036 from=translated src=- shape=2bbe7c34 vocab=a5410e64
-/
@[deprecated (since := "2026-09-03")] alias Terminating.ofTransGen := Terminating.of_transGen

/--
@isnad1 id=iff.0h2v.s4.3ad71af6c47c from=translated src=- shape=196764fe vocab=a5410e64
-/
theorem Terminating.iff_transGen : Terminating (TransGen r) ↔ Terminating r := by
  simp_rw [iff_forall_sn, SN.iff_transGen]

/--
@isnad1 id=iff.0h2v.s5.29f0c339d99d from=translated src=- shape=875742c4 vocab=5bbed617
-/
theorem Terminating.iff_isEmpty_chain :
    Terminating r ↔ IsEmpty {f : ℕ → α // ∀ n, r (f n) (f (n + 1))} :=
  wellFounded_iff_isEmpty_descending_chain

/--
@isnad1 id=terminat.2h3v.s5.0696c2fad442 from=translated src=- shape=a3c00c4e vocab=7a96bebe
-/
theorem Terminating.of_le {r' : α → α → Prop} (hr : Terminating r) (h : r' ≤ r) :
    Terminating r' := by
  rw [iff_forall_sn] at hr ⊢
  exact fun x => (hr x).of_le h

/--
@isnad1 id=terminat.0h2v.s5.a345e4b2a6b9 from=translated src=- shape=ea4f4d1f vocab=4bb6a216
-/
lemma Terminating.subtype_sn (r : α → α → Prop) :
    Terminating (α := {x // SN r x}) (fun a b => r a b) :=
  iff_forall_sn.mpr fun x => x.property.onFun_of_image

/--
@isnad1 id=normaliz.1h2v.s3.1428b4d7bb0d from=translated src=- shape=6e704b37 vocab=3cadb61a
-/
theorem Terminating.to_normalizing (hr : Terminating r) : Normalizing r :=
  fun x => (hr.apply x).normalizable

/--
@isnad1 id=normaliz.1h2v.s3.1428b4d7bb0d from=translated src=- shape=6e704b37 vocab=3cadb61a
-/
@[deprecated (since := "2026-09-03")] alias Terminating.isNormalizing := Terminating.to_normalizing

end Relation
