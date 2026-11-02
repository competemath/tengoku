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

/-- One step along the face permutation is two steps along the map.-/
theorem eqvGen_φ (x : M.D) : Relation.EqvGen M.Step x (M.φ x) :=
  (Relation.EqvGen.rel x (M.α x) (Or.inr rfl)).trans _ _ _
    (Relation.EqvGen.rel (M.α x) (M.φ x) (Or.inl rfl))

/-- The faces lie inside the connected components.-/
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

@[simp] theorem split_σ : (M.split a b).σ = swap a b * M.σ := rfl

@[simp] theorem split_α : (M.split a b).α = M.α := rfl

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

theorem split_numEdges : (M.split a b).numEdges = M.numEdges := rfl

variable {M a b}

theorem split_numVertices (hab : a ≠ b) (h : M.σ.SameCycle a b) :
    (M.split a b).numVertices = M.numVertices + 1 :=
  numOrbits_swap_mul_split hab h

theorem split_numFaces_of_not_sameCycle (h : ¬ M.φ.SameCycle a b) :
    (M.split a b).numFaces + 1 = M.numFaces := by
  unfold numFaces
  rw [split_φ]
  exact (numOrbits_swap_mul h).symm

theorem split_numFaces_of_sameCycle (hab : a ≠ b) (h : M.φ.SameCycle a b) :
    (M.split a b).numFaces = M.numFaces + 1 := by
  unfold numFaces
  rw [split_φ]
  exact numOrbits_swap_mul_split hab h

/-- **Splitting a vertex between two different faces preserves `χ`.**-/
theorem split_euler_of_not_sameCycle_face (hab : a ≠ b) (hσ : M.σ.SameCycle a b)
    (hφ : ¬ M.φ.SameCycle a b) : (M.split a b).euler = M.euler := by
  have hV := split_numVertices hab hσ
  have hE := split_numEdges M a b
  have hF := split_numFaces_of_not_sameCycle hφ
  unfold euler
  omega

/-- **Splitting a vertex inside one face raises `χ` by two.**-/
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
