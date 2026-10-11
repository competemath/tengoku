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

@[to_additive (attr := simp)]
lemma not_isMulStableWith : ¬ IsMulStableWith n A ↔ IsMulOrderPropWith n A := not_isStableRelWith

@[to_additive (attr := simp)]
lemma not_isMulOrderPropWith : ¬ IsMulOrderPropWith n A ↔ IsMulStableWith n A :=
  not_isOrderPropRelWith

@[to_additive (attr := simp)]
lemma not_isMulStable : ¬ IsMulStable A ↔ IsMulOrderProp A := not_isStableRel

@[to_additive (attr := simp)]
lemma not_isMulOrderProp : ¬ IsMulOrderProp A ↔ IsMulStable A := not_isOrderPropRel
