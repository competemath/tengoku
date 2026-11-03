module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.Lemma31.Picture.CombMap
public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.Lemma31.Picture.PermSplit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Splitting a vertex of a combinatorial map

For darts `a ≠ b` of the same vertex of a `CombMap` `M`, `M.split a b` keeps the darts and the edge
involution `α` and replaces the rotation by `σ' = swap a b * σ`: the vertex
`(a, x₁, …, x_r, b, y₁, …, y_s)` is split into the two vertices `(a, x₁, …, x_r)` and
`(b, y₁, …, y_s)`.  No labels, `NPC`, girth or spherical assumption are involved.

## Results

* `split_numVertices`, `split_numEdges` : one more vertex, the same edges;
* `split_φ` : the new face permutation is `swap a b * φ`, so the faces are merged or split by the
  same transposition;
* `split_euler_of_not_sameCycle_face` : if `a`, `b` lie in **different** faces, `χ' = χ`
  (`V+1`, `E`, `F-1`);
* `split_euler_of_sameCycle_face` : if `a`, `b` lie in the **same** face, `χ' = χ + 2`
  (`V+1`, `E`, `F+1`).  In particular splitting a vertex does not always preserve `χ = 2`;
* `split_reach` : if `M` is connected, every dart of the split map is connected to `a` or to `b`
  (the split map has at most two components);
* `split_connected_of_eqvGen` : if moreover `a` and `b` are still connected, the split map is
  connected;
* `sameCycle_face_of_split_not_eqvGen` : if `a` and `b` become disconnected, they were in the
  same face of `M`;
* `split_connected` : if `M` is connected and `a`, `b` lie in different faces, the split map is
  connected.
-/

@[expose] public section

namespace TheoremA.Picture

open Equiv Function

namespace CombMap

variable (M : CombMap)

/-- One step along the face permutation is two steps along the map.
@isnad1 id=eqvgen.0h2v.s5.6cf12a4b25fb from=translated src=- shape=508d7965 vocab=29bcfd2f
-/
theorem eqvGen_φ (x : M.D) : Relation.EqvGen M.Step x (M.φ x) :=
  (Relation.EqvGen.rel x (M.α x) (Or.inr rfl)).trans _ _ _
    (Relation.EqvGen.rel (M.α x) (M.φ x) (Or.inl rfl))

/-- The faces lie inside the connected components.
@isnad1 id=eqvgen.1h3v.s4.1836d12c521a from=translated src=- shape=dbfd64fe vocab=bd116b6c
-/
theorem eqvGen_of_sameCycle_φ {x y : M.D} (h : M.φ.SameCycle x y) :
    Relation.EqvGen M.Step x y := by
  obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
  clear h
  induction n with
  | zero => exact Relation.EqvGen.refl _
  | succ n ih =>
    refine ih.trans _ _ _ ?_
    rw [pow_succ', Perm.mul_apply]
    exact M.eqvGen_φ _

variable (a b : M.D)

/-- Split the vertex through `a` and `b`: `σ' = swap a b * σ`, `α' = α`.-/
def split : CombMap where
  D := M.D
  σ := swap a b * M.σ
  α := M.α
  α_α := M.α_α
  α_ne := M.α_ne

/--
@isnad1 id=eq.0h3v.s5.db80564c7285 from=translated src=- shape=06986997 vocab=67764772
-/
@[simp] theorem split_σ : (M.split a b).σ = swap a b * M.σ := rfl

/--
@isnad1 id=eq.0h3v.s4.8e4d9ff31dec from=translated src=- shape=0daaf8bb vocab=f059f8a4
-/
@[simp] theorem split_α : (M.split a b).α = M.α := rfl

/--
@isnad1 id=eq.0h3v.s5.f4ea0ff97328 from=translated src=- shape=06986997 vocab=127380d1
-/
theorem split_φ : (M.split a b).φ = swap a b * M.φ := by
  simp only [φ, split, mul_assoc]
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/--
@isnad1 id=eq.0h3v.s4.601234467711 from=translated src=- shape=ef878ee9 vocab=9806e1b0
-/
theorem split_numEdges : (M.split a b).numEdges = M.numEdges := rfl

variable {M a b}

/--
@isnad1 id=eq.2h3v.s5.c8ef560db53f from=translated src=- shape=1708c980 vocab=facc4a89
-/
theorem split_numVertices (hab : a ≠ b) (h : M.σ.SameCycle a b) :
    (M.split a b).numVertices = M.numVertices + 1 :=
  numOrbits_swap_mul_split hab h

/--
@isnad1 id=eq.1h3v.s5.3b970323d5f5 from=translated src=- shape=6cb5caba vocab=fd9ff0b4
-/
theorem split_numFaces_of_not_sameCycle (h : ¬ M.φ.SameCycle a b) :
    (M.split a b).numFaces + 1 = M.numFaces := by
  unfold numFaces
  rw [split_φ]
  exact (numOrbits_swap_mul h).symm

/--
@isnad1 id=eq.2h3v.s5.f89c77b1f603 from=translated src=- shape=1708c980 vocab=fd9ff0b4
-/
theorem split_numFaces_of_sameCycle (hab : a ≠ b) (h : M.φ.SameCycle a b) :
    (M.split a b).numFaces = M.numFaces + 1 := by
  unfold numFaces
  rw [split_φ]
  exact numOrbits_swap_mul_split hab h

/-- **Splitting a vertex between two different faces preserves `χ`.**
@isnad1 id=eq.3h3v.s5.47e32d552bd1 from=translated src=- shape=483e5e72 vocab=88877f8e
-/
theorem split_euler_of_not_sameCycle_face (hab : a ≠ b) (hσ : M.σ.SameCycle a b)
    (hφ : ¬ M.φ.SameCycle a b) : (M.split a b).euler = M.euler := by
  have hV := split_numVertices hab hσ
  have hE := split_numEdges M a b
  have hF := split_numFaces_of_not_sameCycle hφ
  unfold euler
  omega

/-- **Splitting a vertex inside one face raises `χ` by two.**
@isnad1 id=eq.3h3v.s5.37685e4f2938 from=translated src=- shape=5aac6ec2 vocab=0f488d75
-/
theorem split_euler_of_sameCycle_face (hab : a ≠ b) (hσ : M.σ.SameCycle a b)
    (hφ : M.φ.SameCycle a b) : (M.split a b).euler = M.euler + 2 := by
  have hV := split_numVertices hab hσ
  have hE := split_numEdges M a b
  have hF := split_numFaces_of_sameCycle hab hφ
  unfold euler
  omega

/-! ### Connectivity -/

end CombMap

end TheoremA.Picture
