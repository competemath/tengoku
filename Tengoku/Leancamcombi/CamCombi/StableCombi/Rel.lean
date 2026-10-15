module

public import Tengoku

/-!
# Stable binary relations
-/

@[expose] public section

variable {α β : Type*} {n : ℕ} {r : α → β → Prop}

def IsOrderPropRelWith (n : ℕ) (r : α → β → Prop) : Prop :=
  ∃ (a : Fin n → α) (b : Fin n → β), ∀ i j, i ≤ j ↔ r (a i) (b j)

def IsOrderPropRel (r : α → β → Prop) : Prop :=
  ∃ (a : ℕ → α) (b : ℕ → β), ∀ i j, i ≤ j ↔ r (a i) (b j)

def IsStableRelWith (n : ℕ) (r : α → β → Prop) : Prop :=
  ∀ (a : Fin n → α) (b : Fin n → β), ∃ i j, ¬ (i ≤ j ↔ r (a i) (b j))

def IsStableRel (r : α → β → Prop) : Prop :=
  ∀ (a : ℕ → α) (b : ℕ → β), ∃ i j, ¬ (i ≤ j ↔ r (a i) (b j))

def IsTreeBoundedRelWith (n : ℕ) (r : α → β → Prop) : Prop :=
  ∀ (a : Vector Bool n → α) (b : ∀ m < n, Vector Bool m → β),
    ∃ (i : Vector Bool n) (m : ℕ) (hmn : m < n) (j : Vector Bool m),
      i.toList <+: j.toList ∧ ¬ (true :: i.toList <+: j.toList ↔ r (a i) (b m hmn j))

/--
@isnad1 id=iff.0h4v.s4.78504fd75b01 from=translated src=- shape=3db730ac vocab=6a2888b1
-/
@[simp] lemma not_isStableRelWith : ¬ IsStableRelWith n r ↔ IsOrderPropRelWith n r := by
  simp [IsOrderPropRelWith, IsStableRelWith]

/--
@isnad1 id=iff.0h4v.s4.9b197366cda5 from=translated src=- shape=3db730ac vocab=6a2888b1
-/
@[simp] lemma not_isOrderPropRelWith : ¬ IsOrderPropRelWith n r ↔ IsStableRelWith n r := by
  simp [← not_isStableRelWith]

/--
@isnad1 id=iff.0h3v.s4.61068e57c082 from=translated src=- shape=683f4a37 vocab=93ef35ce
-/
@[simp] lemma not_isStableRel : ¬ IsStableRel r ↔ IsOrderPropRel r := by
  simp [IsOrderPropRel, IsStableRel]

/--
@isnad1 id=iff.0h3v.s4.b7de0b8cb057 from=translated src=- shape=683f4a37 vocab=93ef35ce
-/
@[simp] lemma not_isOrderPropRel : ¬ IsOrderPropRel r ↔ IsStableRel r := by simp [← not_isStableRel]
