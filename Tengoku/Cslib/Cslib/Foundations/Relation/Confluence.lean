/-
Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring, Chris Henson
-/

module

public import Tengoku.Cslib.Cslib.Foundations.Relation.Termination
public import Tengoku.Seed.Tactic.TFAE

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Relations: Confluence

This module proves some properties regarding confluence that are used for both lambda calculi and
combinatory logic. Some notable theorems:

* `Diamond.to_confluent`: the diamond property implies confluence
* `LocallyConfluent.terminating_toConfluent`: Newman's lemma

We prove most results first for two relations, where `Confluent r` becomes `Commute r₁ r₂`, then
specialize to the classical case where `r₁ = r₂`.

## References

* [*Term Rewriting and All That*][Baader1998]

-/

@[expose] public section

variable {α : Type*} {r r₁ r₂ : α → α → Prop}

namespace Relation

open Function ReflTransGen

/--
@isnad1 id=eq.0h2v.s4.b48b9bc60d06 from=translated src=- shape=fa76e8b6 vocab=aa1abde9
-/
theorem Commute.to_confluent : Commute r r = Confluent r := rfl

/--
@isnad1 id=eq.0h2v.s4.b48b9bc60d06 from=translated src=- shape=fa76e8b6 vocab=aa1abde9
-/
@[deprecated (since := "2026-09-03")] alias Commute.toConfluent := Commute.to_confluent

/--
@isnad1 id=eq.0h2v.s4.dab8bf8abfe5 from=translated src=- shape=fa76e8b6 vocab=6d83051e
-/
@[simp] theorem StronglyCommute.to_stronglyConfluent :
  StronglyCommute r r = StronglyConfluent r := rfl

/--
@isnad1 id=eq.0h2v.s4.dab8bf8abfe5 from=translated src=- shape=fa76e8b6 vocab=6d83051e
-/
@[deprecated (since := "2026-09-03")] alias StronglyCommute.toStronglyConfluent :=
  StronglyCommute.to_stronglyConfluent

/--
@isnad1 id=eq.0h2v.s4.935b06e5228d from=translated src=- shape=fa76e8b6 vocab=4702aaa1
-/
@[simp] theorem DiamondCommute.to_diamond : DiamondCommute r r = Diamond r := rfl

/--
@isnad1 id=eq.0h2v.s4.935b06e5228d from=translated src=- shape=fa76e8b6 vocab=4702aaa1
-/
@[deprecated (since := "2026-09-03")] alias DiamondCommute.toDiamond := DiamondCommute.to_diamond

/--
@isnad1 id=eq.0h2v.s4.b9a95f76b847 from=translated src=- shape=fa76e8b6 vocab=189f10fa
-/
@[simp] theorem SemiCommute.to_semiConfluent : SemiCommute r r = SemiConfluent r := rfl

/--
@isnad1 id=eq.0h2v.s4.558674d0be52 from=translated src=- shape=fa76e8b6 vocab=a985621c
-/
@[simp] theorem LocallyCommute.to_locallyConfluent : LocallyCommute r r = LocallyConfluent r := rfl

instance : Std.Symm (@DiamondCommute α) where
  symm _ _ h _ _ _ h₁ h₂ := Join₂.swap_iff.mp <| h h₂ h₁

/--
@isnad1 id=diamondc.1h3v.s4.f9c5f5f7fdb9 from=translated src=- shape=f60d59ef vocab=80d0302b
-/
lemma DiamondCommute.diamond_commute_reflTransGen_right (h : DiamondCommute r₁ r₂) :
    DiamondCommute r₁ (ReflTransGen r₂) := by
  intro a b c h₁ h₂
  induction h₂ using ReflTransGen.head_induction_on generalizing b with
  | refl => exact Join₂.single_right h₁
  | head ha _ ih =>
    obtain ⟨d, hbd, hcd⟩ := h h₁ ha
    obtain ⟨d', hdd', hcd'⟩ := ih hcd
    exact ⟨d', hdd'.head hbd, hcd'⟩

/--
@isnad1 id=diamondc.1h3v.s4.cd4071c5155b from=translated src=- shape=49aeb47f vocab=80d0302b
-/
lemma DiamondCommute.diamond_commute_reflTransGen_left (h : DiamondCommute r₁ r₂) :
    DiamondCommute (ReflTransGen r₁) r₂ := by
  rw [comm (r := DiamondCommute)] at h ⊢
  exact h.diamond_commute_reflTransGen_right

/--
@isnad1 id=semicomm.1h3v.s4.d7d9f3ed46ca from=translated src=- shape=31fdfe4c vocab=448c23dd
-/
lemma DiamondCommute.to_semiCommute (h : DiamondCommute r₁ r₂) : SemiCommute r₁ r₂ :=
  fun h₁ h₂ => Join₂.mono le_rfl ReflTransGen.le_reflTransGen _ _ <|
    h.diamond_commute_reflTransGen_right h₁ h₂

/-- Extending a multistep reduction by a single step preserves multi-joinability.
@isnad1 id=semiconf.1h2v.s3.0768ab70462b from=translated src=- shape=6e704b37 vocab=2bc1b570
-/
lemma Diamond.to_semiConfluent (h : Diamond r) : SemiConfluent r := DiamondCommute.to_semiCommute h

/--
@isnad1 id=semiconf.1h2v.s3.0768ab70462b from=translated src=- shape=6e704b37 vocab=2bc1b570
-/
@[deprecated (since := "2026-09-12")] alias Diamond.extend := Diamond.to_semiConfluent

/--
@isnad1 id=istrans.1h3v.s4.c5e4c1e06c3b from=translated src=- shape=ec06899c vocab=46ef5ab1
-/
theorem Commute.isTrans_join₂_reflTransGen (h : Commute r₁ r₂) :
    IsTrans α (Join₂ (ReflTransGen r₁) (ReflTransGen r₂)) where
  trans a b c := by
    intro ⟨d, had, hbd⟩ ⟨d', hbd', hcd'⟩
    obtain ⟨e, he, he'⟩ := h hbd' hbd
    exact ⟨e, had.trans he', hcd'.trans he⟩

/--
@isnad1 id=istrans.1h2v.s4.d508caff91db from=translated src=- shape=8d30fd2b vocab=66ccd398
-/
theorem Confluent.isTrans_join_reflTransGen (h : Confluent r) : IsTrans α (Join (ReflTransGen r)) :=
  Commute.isTrans_join₂_reflTransGen h

/--
@isnad1 id=commute.1h3v.s4.445cdffbcc66 from=translated src=- shape=31fdfe4c vocab=cd7c94ef
-/
theorem SemiCommute.to_commute (h : SemiCommute r₁ r₂) : Commute r₁ r₂ := by
  intro a b₁ b₂ hab₁ hab₂
  induction hab₁ with
  | refl => use b₂
  | tail hab hbb' ih =>
    obtain ⟨d, hd, hd'⟩ := ih
    obtain ⟨e, he, he'⟩ := h hbb' hd
    use e, he, hd'.trans he'

/--
@isnad1 id=confluen.1h2v.s3.dea2f460ee25 from=translated src=- shape=6e704b37 vocab=34c060e5
-/
theorem SemiConfluent.to_confluent (h : SemiConfluent r) : Confluent r := SemiCommute.to_commute h

/--
@isnad1 id=confluen.1h2v.s3.dea2f460ee25 from=translated src=- shape=6e704b37 vocab=34c060e5
-/
@[deprecated (since := "2026-09-03")] alias SemiConfluent.toConfluent := SemiConfluent.to_confluent

/--
@isnad1 id=tfae.0h3v.s7.8d0823d9dae8 from=translated src=- shape=88d3eb56 vocab=840066da
-/
theorem commute_equivalents :
    [SemiCommute r₁ r₂, Commute r₁ r₂, IsTrans α (Join₂ (ReflTransGen r₁) (ReflTransGen r₂)),
      ReflTransGen (r₁ ⊔ swap r₂) ≤ Join₂ (ReflTransGen r₁) (ReflTransGen r₂),
      ReflTransGen (r₁ ⊔ swap r₂) = Join₂ (ReflTransGen r₁) (ReflTransGen r₂)].TFAE := by
  tfae_have 1 → 2 := SemiCommute.to_commute
  tfae_have 2 → 3 := Commute.isTrans_join₂_reflTransGen
  tfae_have 3 → 4 := fun h => reflTransGen_le_of_le <|
    sup_le left_le_join₂_reflTransGen swap_right_le_join₂_reflTransGen
  tfae_have 4 → 5 := fun h => h.antisymm <|
    join₂_reflTransGen_le (le_sup_left.trans le_reflTransGen) (le_sup_right.trans le_reflTransGen)
  tfae_have 5 → 1 := by
    intro h a b₁ b₂ h₁ h₂
    rw [Join₂.swap_iff, ← h]
    exact (ReflTransGen.mono le_sup_right _ _ <| reflTransGen_swap.mpr h₂).tail (Or.inl h₁)
  tfae_finish

/--
@isnad1 id=iff.0h3v.s4.b05335ecf4c2 from=translated src=- shape=ca377fb8 vocab=cd7c94ef
-/
theorem semiCommute_iff_commute : SemiCommute r₁ r₂ ↔ Commute r₁ r₂ := commute_equivalents.out 1 2

/--
@isnad1 id=commute.1h3v.s4.dd08d21d2337 from=translated src=- shape=31fdfe4c vocab=da79c7d7
-/
theorem DiamondCommute.to_commute (h : DiamondCommute r₁ r₂) : Commute r₁ r₂ :=
  semiCommute_iff_commute.mp h.to_semiCommute

/--
@isnad1 id=iff.0h2v.s5.58083c82c073 from=translated src=- shape=ac310e66 vocab=b05e1748
-/
theorem churchRosser_iff_eqvGen_le_join_reflTransGen :
    ChurchRosser r ↔ EqvGen r ≤ Join (ReflTransGen r) :=
  Iff.rfl

/--
@isnad1 id=tfae.0h2v.s6.1f97c80b5bb3 from=translated src=- shape=1cdce5dc vocab=5ed95acc
-/
theorem confluent_equivalents :
    [ChurchRosser r, SemiConfluent r, Confluent r, IsTrans α (Join (ReflTransGen r)),
      EqvGen r ≤ Join (ReflTransGen r), EqvGen r = Join (ReflTransGen r)].TFAE := by
  refine (List.tfae_cons ?_).mpr ⟨churchRosser_iff_eqvGen_le_join_reflTransGen, ?_⟩
  · grind
  · simpa [reflTransGen_symmGen] using commute_equivalents (r₁ := r) (r₂ := r)

/--
@isnad1 id=iff.0h2v.s3.dab63fd3acce from=translated src=- shape=eb3d60d9 vocab=b03d4bb6
-/
theorem semiConfluent_iff_churchRosser : SemiConfluent r ↔ ChurchRosser r :=
  List.TFAE.out confluent_equivalents 2 1

/--
@isnad1 id=iff.0h2v.s3.dab63fd3acce from=translated src=- shape=eb3d60d9 vocab=b03d4bb6
-/
@[deprecated (since := "2026-09-03")] alias SemiConfluent_iff_ChurchRosser :=
  semiConfluent_iff_churchRosser

/--
@isnad1 id=iff.0h2v.s3.cdd32aa35b6a from=translated src=- shape=eb3d60d9 vocab=8f419107
-/
theorem confluent_iff_churchRosser : Confluent r ↔ ChurchRosser r :=
  List.TFAE.out confluent_equivalents 3 1

/--
@isnad1 id=churchro.1h2v.s3.40fd0bbaa2c5 from=translated src=- shape=6e704b37 vocab=8f419107
-/
alias ⟨Confluent.to_churchRosser, _⟩ := confluent_iff_churchRosser

/--
@isnad1 id=iff.0h2v.s3.cdd32aa35b6a from=translated src=- shape=eb3d60d9 vocab=8f419107
-/
@[deprecated (since := "2026-09-03")] alias Confluent_iff_ChurchRosser := confluent_iff_churchRosser

attribute [scoped grind →] Confluent.to_churchRosser SemiConfluent.to_confluent

/--
@isnad1 id=iff.0h2v.s3.b1551af6315a from=translated src=- shape=eb3d60d9 vocab=34c060e5
-/
theorem confluent_iff_semiConfluent : Confluent r ↔ SemiConfluent r :=
  List.TFAE.out confluent_equivalents 3 2

/--
@isnad1 id=iff.0h2v.s3.b1551af6315a from=translated src=- shape=eb3d60d9 vocab=34c060e5
-/
@[deprecated (since := "2026-09-03")] alias Confluent_iff_SemiConfluent :=
  confluent_iff_semiConfluent

/--
@isnad1 id=confluen.1h2v.s3.bf0d3903a3c6 from=translated src=- shape=6e704b37 vocab=ad0dc4be
-/
theorem Diamond.to_confluent (h : Diamond r) : Confluent r := DiamondCommute.to_commute h

/--
@isnad1 id=confluen.1h2v.s3.bf0d3903a3c6 from=translated src=- shape=6e704b37 vocab=ad0dc4be
-/
@[deprecated (since := "2026-09-03")] alias Diamond.toConfluent := Diamond.to_confluent

/--
@isnad1 id=confluen.1h3v.s4.dc8a7cd30964 from=translated src=- shape=b6dd2b16 vocab=704b05fe
-/
theorem confluent_of_unique_end {x : α} (h : ∀ y : α, ReflTransGen r y x) : Confluent r := by
  intro a b c hab hac
  exact ⟨x, h b, h c⟩

/--
@isnad1 id=confluen.1h3v.s4.dc8a7cd30964 from=translated src=- shape=b6dd2b16 vocab=704b05fe
-/
@[deprecated (since := "2026-09-03")] alias Confluent_of_unique_end := confluent_of_unique_end

/-- For a Church-Rosser relation, elements in an equivalence class must be multi-step related.
@isnad1 id=refltran.3h4v.s5.216d68ec44c1 from=translated src=- shape=e84517bd vocab=cdb9f75c
-/
theorem ChurchRosser.normal_eqvGen_reflTransGen (cr : ChurchRosser r) (norm : Normal r x)
    (xy : EqvGen r y x) : ReflTransGen r y x := by
  have ⟨_, _, _⟩ := cr xy
  grind

/-- For a Church-Rosser relation there is one normal form in each equivalence class.
@isnad1 id=eq.4h4v.s5.56ebd472aa07 from=translated src=- shape=ab7004cc vocab=d6ec3147
-/
theorem ChurchRosser.normal_eq (cr : ChurchRosser r) (nx : Normal r x) (ny : Normal r y)
    (xy : EqvGen r x y) : x = y := by
  have ⟨z, _, _⟩ := cr xy
  grind

/-- Confluence implies that multi-step joinability is an equivalence.
@isnad1 id=equivale.1h2v.s4.47bad0d00dc2 from=translated src=- shape=8d30fd2b vocab=eb0cda20
-/
theorem Confluent.equivalence_join_reflTransGen (h : Confluent r) :
    Equivalence (Join (ReflTransGen r)) := by
  apply equivalence_join
  grind

/--
@isnad1 id=iff.1h2v.s5.c2085bcf7528 from=translated src=- shape=26d64e2d vocab=00787ef5
-/
theorem Normalizing.confluent_iff_forall_unique_normal (hn : Normalizing r) :
    Confluent r ↔ ∀ a : α, ∃! n : α, ReflTransGen r a n ∧ Normal r n := by
  constructor
  · intro hc a
    apply existsUnique_of_exists_of_unique (hn a)
    rintro n₁ n₂ ⟨hr₁, hn₁⟩ ⟨hr₂, hn₂⟩
    have hj : Join (ReflTransGen r) n₁ n₂ := hc hr₁ hr₂
    obtain ⟨m, h₁, h₂⟩ := hj
    rw [Normal.reflTransGen_eq hn₁ h₁, Normal.reflTransGen_eq hn₂ h₂]
  · intro h a b c hab hac
    obtain ⟨na, ⟨han, hnnor⟩, H⟩ := h a
    use na
    obtain ⟨nb, hbnb, hnb⟩ := hn b
    obtain ⟨nc, hcnc, hnc⟩ := hn c
    have hanb : (ReflTransGen r) a nb := ReflTransGen.trans hab hbnb
    have hanc : (ReflTransGen r) a nc := ReflTransGen.trans hac hcnc
    grind

/--
@isnad1 id=iff.1h2v.s5.dce57e7fd762 from=translated src=- shape=26d64e2d vocab=5e9d6449
-/
theorem Terminating.confluent_iff_forall_unique_normal (ht : Terminating r) :
    Confluent r ↔ ∀ a : α, ∃! n : α, ReflTransGen r a n ∧ Normal r n :=
  ht.to_normalizing.confluent_iff_forall_unique_normal

/--
@isnad1 id=iff.1h2v.s5.dce57e7fd762 from=translated src=- shape=26d64e2d vocab=5e9d6449
-/
@[deprecated (since := "2026-09-03")] alias Terminating.isConfluent_iff_all_unique_Normal :=
  Terminating.confluent_iff_forall_unique_normal

/--
@isnad1 id=terminat.1h2v.s3.240c04e58dc1 from=translated src=- shape=6e704b37 vocab=a2688812
-/
theorem Convergent.to_terminating (h : Convergent r) : Terminating r := h.right

/--
@isnad1 id=terminat.1h2v.s3.240c04e58dc1 from=translated src=- shape=6e704b37 vocab=a2688812
-/
@[deprecated (since := "2026-09-03")] alias Convergent.isTerminating := Convergent.to_terminating

/--
@isnad1 id=confluen.1h2v.s3.102d51002af7 from=translated src=- shape=6e704b37 vocab=7ccfa4aa
-/
theorem Convergent.to_confluent (h : Convergent r) : Confluent r := h.left

/--
@isnad1 id=confluen.1h2v.s3.102d51002af7 from=translated src=- shape=6e704b37 vocab=7ccfa4aa
-/
@[deprecated (since := "2026-09-03")] alias Convergent.isConfluent := Convergent.to_confluent

/--
@isnad1 id=normaliz.1h2v.s3.fdde929d52b1 from=translated src=- shape=6e704b37 vocab=481ae4d4
-/
theorem Convergent.to_normalizing (h : Convergent r) : Normalizing r :=
  h.to_terminating.to_normalizing

/--
@isnad1 id=normaliz.1h2v.s3.fdde929d52b1 from=translated src=- shape=6e704b37 vocab=481ae4d4
-/
@[deprecated (since := "2026-09-03")] alias Convergent.isNormalizing := Convergent.to_normalizing

/--
@isnad1 id=existsun.1h3v.s4.ae804a600bb2 from=translated src=- shape=1914854a vocab=70748cc5
-/
theorem Convergent.unique_normal (h : Convergent r) :
    ∀ a : α, ∃! n : α, ReflTransGen r a n ∧ Normal r n :=
  h.to_terminating.confluent_iff_forall_unique_normal.mp h.to_confluent

/--
@isnad1 id=existsun.1h3v.s4.ae804a600bb2 from=translated src=- shape=1914854a vocab=70748cc5
-/
@[deprecated (since := "2026-09-03")] alias Convergent.unique_Normal := Convergent.unique_normal

/--
@isnad1 id=locallyc.1h2v.s3.9384cb6fa7bf from=translated src=- shape=6e704b37 vocab=29f5fd6b
-/
theorem Confluent.to_locallyConfluent (h : Confluent r) : LocallyConfluent r := by
  intro _ _ _ ab ac
  exact h (.single ab) (.single ac)

/--
@isnad1 id=locallyc.1h2v.s3.9384cb6fa7bf from=translated src=- shape=6e704b37 vocab=29f5fd6b
-/
@[deprecated (since := "2026-09-03")] alias Confluent.toLocallyConfluent :=
  Confluent.to_locallyConfluent

/--
@isnad1 id=commute.2h3v.s5.8c2fd3404376 from=translated src=- shape=05652972 vocab=e8469c5c
-/
theorem LocallyCommute.commute_of_terminating_sup (hlc : LocallyCommute r₁ r₂)
    (ht : Terminating (r₁ ⊔ r₂)) : Commute r₁ r₂ := by
  intro x
  induction x using ht.induction with
  | h x ih =>
    intro y z hy hz
    rcases hy.cases_head with (rfl | ⟨y', hy, hy'⟩)
    · use z
    · rcases hz.cases_head with (rfl | ⟨z', hz, hz'⟩)
      · use y
      · obtain ⟨u, hyu, hzu⟩ := hlc hy hz
        obtain ⟨v, hyv, huv⟩ := ih y' (join_inl hy) hy' hyu
        obtain ⟨w, hvw, hzw⟩ := ih z' (join_inr hz) (hzu.trans huv) hz'
        exact ⟨w, hyv.trans hvw, hzw⟩

/-- Newman's lemma: a terminating, locally confluent relation is confluent.
@isnad1 id=confluen.2h2v.s4.91fd29c3c09a from=translated src=- shape=b478ed8f vocab=4e36b802
-/
theorem LocallyConfluent.terminating_toConfluent (hlc : LocallyConfluent r) (ht : Terminating r) :
    Confluent r := LocallyCommute.commute_of_terminating_sup hlc ((sup_idem r).symm ▸ ht)

/--
@isnad1 id=confluen.2h2v.s4.91fd29c3c09a from=translated src=- shape=b478ed8f vocab=4e36b802
-/
@[deprecated (since := "2026-09-03")] alias LocallyConfluent.Terminating_toConfluent :=
  LocallyConfluent.terminating_toConfluent

/--
@isnad1 id=ex.2h7v.s5.0a50f0569003 from=translated src=- shape=79ec19a9 vocab=5562f569
-/
theorem StronglyCommute.extend (h : StronglyCommute r₁ r₂) (xy : ReflTransGen r₁ x y)
    (xz : r₂ x z) : ∃ w, ReflGen r₂ y w ∧ ReflTransGen r₁ z w := by
  induction xy with
  | refl => exact ⟨z, .single xz, .refl⟩
  | @tail b c _ bc ih =>
    obtain ⟨w, bw, zw⟩ := ih
    cases bw with
    | refl => exact ⟨c, .refl, zw.tail bc⟩
    | single bw => cases h bc bw; grind [ReflTransGen.trans]

/--
@isnad1 id=commute.1h3v.s4.ea9b4d90ad4f from=translated src=- shape=31fdfe4c vocab=a381648f
-/
theorem StronglyCommute.to_commute (h : StronglyCommute r₁ r₂) : Commute r₁ r₂ := by
  rw [comm (r := Commute)]
  apply SemiCommute.to_commute
  intro a b c hab hac
  obtain ⟨d, hcd, hbd⟩ := h.extend hac hab
  exact ⟨d, hbd, hcd.to_reflTransGen⟩

/--
@isnad1 id=commute.1h3v.s4.ea9b4d90ad4f from=translated src=- shape=31fdfe4c vocab=a381648f
-/
@[deprecated (since := "2026-09-03")] alias StronglyCommute.toCommute := StronglyCommute.to_commute

/--
@isnad1 id=confluen.1h2v.s3.056795c8fe22 from=translated src=- shape=6e704b37 vocab=b0aad29e
-/
theorem StronglyConfluent.to_confluent (h : StronglyConfluent r) : Confluent r :=
  StronglyCommute.to_commute h

/--
@isnad1 id=confluen.1h2v.s3.056795c8fe22 from=translated src=- shape=6e704b37 vocab=b0aad29e
-/
@[deprecated (since := "2026-09-03")] alias StronglyConfluent.toConfluent :=
  StronglyConfluent.to_confluent

/-- Diamond commutation is preserved by taking the union of the left relations.
@isnad1 id=diamondc.2h4v.s6.b1a20b8a41b3 from=translated src=- shape=52e56487 vocab=d68c2be8
-/
lemma DiamondCommute.join_left (c₁ : DiamondCommute r₁ r₃) (c₂ : DiamondCommute r₂ r₃) :
    DiamondCommute (r₁ ⊔ r₂) r₃ := by
  rintro a b c (hab | hab) hac
  · exact Join₂.mono le_rfl le_sup_left _ _ (c₁ hab hac)
  · exact Join₂.mono le_rfl le_sup_right _ _ (c₂ hab hac)

/--
@isnad1 id=commute.2h4v.s6.7dacfa07b383 from=translated src=- shape=52e56487 vocab=679d0b72
-/
lemma Commute.join_left (c₁ : Commute r₁ r₃) (c₂ : Commute r₂ r₃) : Commute (r₁ ⊔ r₂) r₃ := by
  apply SemiCommute.to_commute
  rintro a b c (hab | hab) hac
  · exact Join₂.mono le_rfl (ReflTransGen.mono le_sup_left) _ _ (c₁ (.single hab) hac)
  · exact Join₂.mono le_rfl (ReflTransGen.mono le_sup_right) _ _ (c₂ (.single hab) hac)

/--
@isnad1 id=confluen.3h3v.s6.91797998ea71 from=translated src=- shape=68983806 vocab=3b51b9e7
-/
theorem Commute.join_confluent (c₁ : Confluent r₁) (c₂ : Confluent r₂) (comm : Commute r₁ r₂) :
    Confluent (r₁ ⊔ r₂) := by
  rw [← Commute.to_confluent]
  apply_rules [join_left, symm]

/-- `Relator.RightUnique` corresponds to deterministic reductions, which are confluent, as all
multi-reductions with a common origin start the same (this fact is
`Relation.ReflTransGen.total_of_right_unique`.)
@isnad1 id=confluen.1h2v.s4.6936d9642d45 from=translated src=- shape=8ea8ee1a vocab=dbf3e220
-/
theorem RightUnique.to_confluent (hr : Relator.RightUnique r) : Confluent r := by
  intro a b c ab ac
  obtain (h | h) := ReflTransGen.total_of_right_unique hr ab ac
  · use c
  · use b

/--
@isnad1 id=confluen.1h2v.s4.6936d9642d45 from=translated src=- shape=8ea8ee1a vocab=dbf3e220
-/
@[deprecated (since := "2026-09-03")] alias RightUnique.toConfluent := RightUnique.to_confluent

/--
@isnad1 id=iff.0h4v.s6.8125543137c9 from=translated src=- shape=27273208 vocab=5778ac1b
-/
theorem Reducible.sup_iff (x : α) : Reducible (r₁ ⊔ r₂) x ↔ Reducible r₁ x ∨ Reducible r₂ x :=
  exists_or

/--
@isnad1 id=iff.0h4v.s6.d106dd177404 from=translated src=- shape=27273208 vocab=09fdd2f4
-/
theorem Normal.sup_iff (x : α) : Normal (r₁ ⊔ r₂) x ↔ Normal r₁ x ∧ Normal r₂ x :=
  (not_iff_not.mpr <| Reducible.sup_iff x).trans not_or

end Relation
