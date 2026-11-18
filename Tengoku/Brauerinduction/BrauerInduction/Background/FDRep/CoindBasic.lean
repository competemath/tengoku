import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Induced

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

variable {k : Type u} {G : Type u}

namespace FDRep

variable [CommRing k] [IsNoetherianRing k] [Group G]

/--
Evaluation of a coinduced representation at a group element, as a linear map.-/
noncomputable def coindEval
    [Finite G]
    (I : Subgroup G) (σ : FDRep k I) (x : G) :
    (FDRep.coind I σ) →ₗ[k] σ where
  toFun v := v.val x
  map_add' := by
    intro v w
    rfl
  map_smul' := by
    intro c v
    rfl

/--
@isnad1 id=eq.0h6v.s12.e6d224dbd54b from=translated src=- shape=b74ec381 vocab=8904db3f
-/
@[simp]
lemma coindEval_apply
    [Finite G]
    (I : Subgroup G) (σ : FDRep k I) (x : G)
    (v : (FDRep.coind I σ)) :
    coindEval I σ x v = v.val x :=
  rfl

/--
Two vectors in a coinduced representation are equal if their values agree at every
group element.
@isnad1 id=eq.1h6v.s13.af39fdb8afda from=translated src=- shape=f1a41104 vocab=ad8eddc6
-/
@[ext]
lemma coind_ext_val
    [Finite G]
    (I : Subgroup G) (σ : FDRep k I)
    {v w : (FDRep.coind I σ)}
    (h : ∀ x : G, v.val x = w.val x) :
    v = w := by
  apply Subtype.ext
  ext x
  exact h x

/--
Two vectors in a coinduced representation are equal if they agree at every
group element.
@isnad1 id=eq.1h6v.s11.263c6f8779f0 from=translated src=- shape=c79c71d9 vocab=f9f8c1a4
-/

lemma coind_ext
    [Finite G]
    (I : Subgroup G) (σ : FDRep k I)
    {v w : (FDRep.coind I σ)}
    (h : ∀ x : G, coindEval I σ x v = coindEval I σ x w) :
    v = w := by
  apply coind_ext_val I σ
  intro x
  exact h x

end FDRep
