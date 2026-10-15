module

public import Tengoku.Leancamcombi.CamCombi.StableCombi.Rel
public import Tengoku

@[expose] public section

variable {G : Type*} [Group G] {n : ℕ} {A : Set G}

@[to_additive] def IsMulOrderPropWith (n : ℕ) (A : Set G) : Prop := IsOrderPropRelWith n (· * · ∈ A)

@[to_additive] def IsMulOrderProp (A : Set G) : Prop := IsOrderPropRel (· * · ∈ A)

@[to_additive] def IsMulStableWith (n : ℕ) (A : Set G) : Prop := IsStableRelWith n (· * · ∈ A)

@[to_additive] def IsMulStable (A : Set G) : Prop := IsStableRel (· * · ∈ A)

@[to_additive]
def IsMulTreeBoundedWith (n : ℕ) (A : Set G) : Prop := IsTreeBoundedRelWith n (· * · ∈ A)

/--
@isnad1 id=iff.0h3v.s4.7e47aae1f090 from=translated src=- shape=6038ade6 vocab=fd3f27ea
-/
@[to_additive (attr := simp)]
lemma not_isMulStableWith : ¬ IsMulStableWith n A ↔ IsMulOrderPropWith n A := not_isStableRelWith

/--
@isnad1 id=iff.0h3v.s4.a5c649c90b24 from=translated src=- shape=6038ade6 vocab=fd3f27ea
-/
@[to_additive (attr := simp)]
lemma not_isMulOrderPropWith : ¬ IsMulOrderPropWith n A ↔ IsMulStableWith n A :=
  not_isOrderPropRelWith

/--
@isnad1 id=iff.0h2v.s4.be1cbe79dd69 from=translated src=- shape=d2f6837b vocab=f8dc6990
-/
@[to_additive (attr := simp)]
lemma not_isMulStable : ¬ IsMulStable A ↔ IsMulOrderProp A := not_isStableRel

/--
@isnad1 id=iff.0h2v.s4.34c5c4f1761d from=translated src=- shape=d2f6837b vocab=f8dc6990
-/
@[to_additive (attr := simp)]
lemma not_isMulOrderProp : ¬ IsMulOrderProp A ↔ IsMulStable A := not_isOrderPropRel
