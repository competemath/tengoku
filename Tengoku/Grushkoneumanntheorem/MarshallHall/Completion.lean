import Tengoku.Grushkoneumanntheorem.MarshallHall.CoreSupport
import Tengoku.Grushkoneumanntheorem.MarshallHall.FiniteCore

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Set Function
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

noncomputable section
namespace MarshallHall

universe u
variable {α : Type u} [DecidableEq α]

/-!
## The finite core as an embedded labelled graph

The finite-state action from `Separation` remembers the cosets needed by the
given subgroup generators.  The predicates below select exactly those
labelled edges of the action groupoid which still agree with the original
left-coset action.  The resulting graph is the finite core used in the
completion argument.
-/

def goodGeneratorEdge (H : Subgroup (FreeGroup α)) {O : Type u}
    [MulAction (FreeGroup α) O]
    [IsFreeGroupoid (ActionCategory (FreeGroup α) O)]
    (q : O → LeftCosetQuotient H)
    {a b : IsFreeGroupoid.Generators (ActionCategory (FreeGroup α) O)}
    (e : a ⟶ b) : Prop :=
  leftMulEquiv H (IsFreeGroupoid.of e).val (q a.back) = q b.back

def goodSymmetricEdge (H : Subgroup (FreeGroup α)) {O : Type u}
    [MulAction (FreeGroup α) O]
    [IsFreeGroupoid (ActionCategory (FreeGroup α) O)]
    (q : O → LeftCosetQuotient H)
    {a b : Symmetrify (IsFreeGroupoid.Generators
      (ActionCategory (FreeGroup α) O))} (e : a ⟶ b) : Prop :=
  Sum.recOn e
    (fun f => goodGeneratorEdge H q f)
    (fun f => goodGeneratorEdge H q f)

def goodSymmetricSubquiver (H : Subgroup (FreeGroup α)) {O : Type u}
    [MulAction (FreeGroup α) O]
    [IsFreeGroupoid (ActionCategory (FreeGroup α) O)]
    (q : O → LeftCosetQuotient H) :
    WideSubquiver (Symmetrify (IsFreeGroupoid.Generators
      (ActionCategory (FreeGroup α) O))) :=
  fun a b => {e | goodSymmetricEdge H q e}

/-! A shortest-path tree in a rooted connected partial graph, flattened back
to the full edge type so that it can be used by the explicit Schreier basis. -/

def flatGeodesicSubtree {V : Type u} [Quiver V]
    (P : WideSubquiver V) (r : P)
    [RootedConnected r] : WideSubquiver V :=
  fun a b => {e | ∃ (he : e ∈ P a b) (p : @Path (WideSubquiver.toType V P)
      P.quiver r a),
      shortestPath r b = p.cons ⟨e, he⟩}

def coreCondition {H : Subgroup (FreeGroup α)}
    (A : Set (LeftCosetQuotient H)) (u : List (α × Bool)) : Prop :=
  ∀ v ∈ List.tails u, ∀ x ∈ actionStates v,
    (Quotient.mk'' x : LeftCosetQuotient H) ∈ A

/--
@isnad1 id=corecond.1h5v.s5.91f7867bfaf6 from=translated src=- shape=61adcfa8 vocab=5111177e
-/
theorem coreCondition_tail {H : Subgroup (FreeGroup α)}
    {A : Set (LeftCosetQuotient H)} {x : α × Bool} {u : List (α × Bool)}
    (h : coreCondition A (x :: u)) : coreCondition A u := by
  intro v hv y hy
  exact h v (by simp only [List.tails, List.mem_cons]; exact Or.inr hv) y hy

/-! The same recursive construction also remembers the word labelling its
path.  This is the bridge from a subgroup word to the corresponding loop in
the completed covering graph. -/

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h7v.s11.b56241f601d9 from=translated src=- shape=74bbc1f3 vocab=d0cba666
-/
theorem good_tree_path
    (H : Subgroup (FreeGroup α)) {O : Type u}
    [MulAction (FreeGroup α) O]
    [IsFreeGroupoid (ActionCategory (FreeGroup α) O)]
    (q : O → LeftCosetQuotient H)
    (T : WideSubquiver (Symmetrify (IsFreeGroupoid.Generators
      (ActionCategory (FreeGroup α) O))))
    (hT : ∀ {a b} (e : a ⟶ b), e ∈ T a b →
      goodSymmetricEdge H q e)
    [Arborescence T]
    {a : T} (p : @Path (WideSubquiver.toType
      (Symmetrify (IsFreeGroupoid.Generators
        (ActionCategory (FreeGroup α) O))) T) T.quiver (root T) a) :
    leftMulEquiv H (IsFreeGroupoid.SpanningTree.homOfPath T p).val
      (q (root T).back) = q a.back := by
  induction p with
  | nil =>
      simp [IsFreeGroupoid.SpanningTree.homOfPath]
  | @cons b c p e ih =>
      rw [IsFreeGroupoid.SpanningTree.homOfPath]
      rcases e with ⟨e | e, heT⟩
      · have heP : goodSymmetricEdge H q (Sum.inl e) := by
          exact hT (Sum.inl e) heT
        simp only [ActionCategory.comp_val, Sum.recOn]
        rw [leftMulEquiv_mul, ih]
        exact heP
      · have heP : goodSymmetricEdge H q (Sum.inr e) := by
          exact hT (Sum.inr e) heT
        simp only [ActionCategory.comp_val, Sum.recOn]
        rw [leftMulEquiv_mul, ih]
        have heP' :
            leftMulEquiv H
                (IsFreeGroupoid.of (G := ActionCategory (FreeGroup α) O) e).val
                (q c.back) = q b.back := by
          exact heP
        have h := congrArg
            (leftMulEquiv H
              ((IsFreeGroupoid.of (G := ActionCategory (FreeGroup α) O) e).val)⁻¹) heP'
        rw [leftMulEquiv_inv_apply] at h
        rw [← CategoryTheory.Groupoid.inv_eq_inv]
        exact h.symm

end MarshallHall
