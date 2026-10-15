module

public import Tengoku.Leancamcombi.CamCombi.StableCombi.Rel
public import Tengoku

@[expose] public section

namespace FirstOrder.Language
variable {L : Language}

namespace Formula
variable (n : ℕ) (M : Type*) [L.Structure M] (φ : L.Formula (Fin 2))

def IsOrderPropWith : Prop := IsOrderPropRelWith n fun x y : M ↦ φ.Realize ![x, y]

def IsOrderProp : Prop := IsOrderPropRel fun x y : M ↦ φ.Realize ![x, y]

def IsStableWith : Prop := IsStableRelWith n fun x y : M ↦ φ.Realize ![x, y]

def IsStable : Prop := IsStableRel fun x y : M ↦ φ.Realize ![x, y]

def IsTreeBoundedWith : Prop := IsTreeBoundedRelWith n fun x y : M ↦ φ.Realize ![x, y]

variable {n M φ}

/--
@isnad1 id=iff.0h4v.s5.7d01f1f0b414 from=translated src=- shape=3c965a31 vocab=d4644a32
-/
@[simp] lemma not_isStableWith : ¬ IsStableWith n M φ ↔ IsOrderPropWith n M φ := not_isStableRelWith

/--
@isnad1 id=iff.0h4v.s5.f276068c659a from=translated src=- shape=3c965a31 vocab=d4644a32
-/
@[simp] lemma not_isOrderPropWith : ¬ IsOrderPropWith n M φ ↔ IsStableWith n M φ :=
  not_isOrderPropRelWith

/--
@isnad1 id=iff.0h3v.s4.cd582e2412c6 from=translated src=- shape=980840f0 vocab=8de09e8e
-/
@[simp] lemma not_isStable : ¬ IsStable M φ ↔ IsOrderProp M φ := not_isStableRel

/--
@isnad1 id=iff.0h3v.s4.c43a63b369fa from=translated src=- shape=980840f0 vocab=8de09e8e
-/
@[simp] lemma not_isOrderProp : ¬ IsOrderProp M φ ↔ IsStable M φ := not_isOrderPropRel

end Formula

namespace Theory
variable (T : L.Theory)

-- TODO: What universe should we set `M` to here?
def IsOrderProp : Prop :=
  ∃ (M : Type*) (_ : L.Structure M), M ⊨ T ∧ ∃ φ : L.Formula (Fin 2), φ.IsOrderProp M

def IsStable : Prop := ∀ ⦃M : Type*⦄ [L.Structure M], M ⊨ T → ∀ φ : L.Formula (Fin 2), φ.IsStable M

variable {T}

/--
@isnad1 id=iff.0h2v.s3.3c2fe6b24fda from=translated src=- shape=ec97e29f vocab=c9efe217
-/
@[simp] lemma not_isStable : ¬ IsStable T ↔ IsOrderProp T := by simp [IsStable, IsOrderProp]

/--
@isnad1 id=iff.0h2v.s3.1acdfb33bffb from=translated src=- shape=ec97e29f vocab=c9efe217
-/
@[simp] lemma not_isOrderProp : ¬ IsOrderProp T ↔ IsStable T := by simp [← not_isStable]

end FirstOrder.Language.Theory
