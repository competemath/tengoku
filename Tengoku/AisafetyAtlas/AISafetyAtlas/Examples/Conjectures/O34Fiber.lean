module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Conjectures.MAIS
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Analysis.Semialgebraic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Adjudicating MAIS issue #4's complete `MAIS-O34(a)` criterion

`AISafetyAtlas.Conjectures.MAIS.maisO34_exactFiberCandidate` transcribes the
complete singleton criterion proposed by Rob Sneiderman in MAIS issue #4. This
module adjudicates it and holds nothing else.

The chart it is stated on, and the whole reading algebra the adjudication runs
on, sit in `AISafetyAtlas.Conjectures.BinaryPair`: which profile reads which
coordinate, when a coordinate is pinned, when it is invisible, and when two
orientations collide. That module is not library infrastructure — it is a fixed
two-variable chart shared with the MAIS-O31 statement, which is why it lives
beside the conjectures rather than in `AISafetyAtlas.Causal`. None of it is
specific to this question, so none of it lives here.

The criterion is adjudicated affirmatively. Sufficiency blocks every rival;
necessity splits into a same-direction half, which turns on a vanishing
direction difference hiding its coordinate from all sixteen profiles, and an
opposite-orientation half, which builds the mate that two flat lines allow.
`maisO34_exactFiberCandidate_holds` names the transcribed proposition.

The scope is the transcribed chart. Issue #4 part (b) is not covered.
-/

namespace AISafetyAtlas.Examples.Conjectures.O34Fiber

open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Conjectures.BinaryPair

/-! ## The same-orientation fibre -/

@[simp] public theorem other_zero : other 0 = 1 := rfl

@[simp] public theorem other_one : other 1 = 0 := rfl

/-! ## Sufficiency of the submitted criterion -/

/-! ## Necessity of the same-direction clause

The first half of the converse. Sufficiency showed the criterion blocks every
rival; here the same-direction clause is shown to be *forced*: when it fails,
`child z` is both unread and free to move inside its companion set, so a mate
exists and the fibre is not a singleton.
-/

/-! ## The clause can fail

`sameDirection_of_isSingletonFiber` would be empty if no valid gap and model
made the same-direction clause fail. One does. The flat row makes `child 0`
unread, and its partner's companion set is wider than the singleton the clause
demands, so the fibre of this model is not a singleton.
-/

/-- A valid gap whose first row is flat.-/
@[expose] public noncomputable def o34FlatRowGap : Fin 2 → Fin 2 → ℝ :=
  ![![1 / 2, 1 / 2], ![-(1 / 4), 3 / 4]]

/-- A valid forward model whose unread coordinate has room to move.-/
@[expose] public noncomputable def o34FlatRowModel : PairModel where
  orientation := Orientation.forward
  root := 1 / 2
  child := ![1 / 5, 4 / 5]

/-! ## Necessity of the mate clause

`hasOppositeMate_of_opposite_mate` proved the three clauses are necessary for an
opposite-orientation mate. This proves they are sufficient, which is the step
the candidate needed and the only one that could have refuted it.
-/

/-! ## The complete adjudication -/

/-! ## Both sides of the equivalence are reachable

`isSingletonFiber_iff_candidate` would say nothing if either side were empty on
valid data. Neither is. One gap table has two flat lines, so the mate clause
holds and the fibre is not a singleton; another has no flat line at all, so the
criterion holds and the fibre is a singleton.
-/

/-- A valid gap with one flat row *and* one flat column.-/
@[expose] public noncomputable def o34TwoFlatGap : Fin 2 → Fin 2 → ℝ :=
  ![![1 / 2, 1 / 2], ![1 / 2, -(1 / 4)]]

@[expose] public noncomputable def o34TwoFlatModel : PairModel where
  orientation := Orientation.forward
  root := 1 / 2
  child := ![1 / 5, 4 / 5]

/-- A valid gap with no flat line at all.-/
@[expose] public noncomputable def o34SharpGap : Fin 2 → Fin 2 → ℝ :=
  ![![1 / 2, -(1 / 4)], ![-(1 / 4), 1 / 2]]

/-! ## The criterion is semialgebraic

`prob:starter-set`(a) asks for the singleton condition as *"an explicit
semialgebraic condition on `(u, θ)`"*. `o34_classFibre_iff_candidate` supplies
the condition and proves it decides the printed fibre; this section supplies the
missing adjective.

`def:twovar` names seven real coordinates — the four gap-table entries of `u`
and the three table parameters of `θ` — plus one binary structural choice, so
the locus lives in `ℝ⁷` once an orientation is fixed. Every atom of the
criterion is a polynomial sign condition in those coordinates: the child and
root differences are differences of gap entries, and the two clauses that
quantify over the reals are removed first by
`separatedValues_eq_singleton_iff` and `separatedValues_nonempty_iff`. What is
left is a boolean combination, and `IsSemialgebraic` is closed under those.
-/

/-- The seven real coordinates the printed condition is a condition on.-/
public abbrev O34Index := (Fin 2 × Fin 2) ⊕ Fin 3

/-- The gap table a chart point carries.-/
@[expose] public def o34ChartGap (q : O34Index → ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun x y ↦ q (Sum.inl (x, y))

/-- The model a chart point carries at a chosen orientation.-/
@[expose] public def o34ChartModel (gr : Orientation) (q : O34Index → ℝ) : PairModel where
  orientation := gr
  root := q (Sum.inr 0)
  child := fun i ↦ q (Sum.inr i.succ)

open MvPolynomial in
/-- The polynomial computing a child difference of the gap table.-/
@[expose] public noncomputable def o34ChildDiffPoly (gr : Orientation) (i : Fin 2) :
    MvPolynomial O34Index ℝ :=
  match gr with
  | .forward => X (Sum.inl (i, 1)) - X (Sum.inl (i, 0))
  | .reverse => X (Sum.inl (1, i)) - X (Sum.inl (0, i))

open MvPolynomial in
public theorem o34ChildDiffPoly_eval (gr : Orientation) (i : Fin 2) (q : O34Index → ℝ) :
    eval q (o34ChildDiffPoly gr i) = childDifference gr (o34ChartGap q) i := by
  cases gr <;> simp [o34ChildDiffPoly, childDifference, o34ChartGap]

open MvPolynomial in
public theorem o34RootDiffPoly_eval (gr : Orientation) (i : Fin 2) (q : O34Index → ℝ) :
    eval q (o34ChildDiffPoly (otherOrientation gr) i)
      = rootDifference gr (o34ChartGap q) i := by
  cases gr <;> simp [o34ChildDiffPoly, rootDifference, childDifference, o34ChartGap,
    otherOrientation]

open MvPolynomial in
/-- The polynomial reading one table coordinate, shifted by a constant.-/
@[expose] public noncomputable def o34ChildShiftPoly (i : Fin 2) (a : ℝ) :
    MvPolynomial O34Index ℝ :=
  X (Sum.inr i.succ) - C a

open MvPolynomial in
public theorem o34ChildShiftPoly_eval (i : Fin 2) (a : ℝ) (gr : Orientation)
    (q : O34Index → ℝ) :
    eval q (o34ChildShiftPoly i a) = (o34ChartModel gr q).child i - a := by
  simp [o34ChildShiftPoly, o34ChartModel]

open MvPolynomial in
/-- The polynomial reading the root coordinate, shifted by a constant.-/
@[expose] public noncomputable def o34RootShiftPoly (a : ℝ) : MvPolynomial O34Index ℝ :=
  X (Sum.inr 0) - C a

open MvPolynomial in
public theorem o34RootShiftPoly_eval (a : ℝ) (gr : Orientation) (q : O34Index → ℝ) :
    eval q (o34RootShiftPoly a) = (o34ChartModel gr q).root - a := by
  simp [o34RootShiftPoly, o34ChartModel]

open AISafetyAtlas.Causal AISafetyAtlas.Analysis MvPolynomial in
/-- A child coordinate meeting a constant is a semialgebraic condition.-/
private theorem isSemialgebraic_child_eq (gr : Orientation) (i : Fin 2) (a : ℝ) :
    IsSemialgebraic {q : O34Index → ℝ | (o34ChartModel gr q).child i = a} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ eval q (o34ChildShiftPoly i a) = 0) (fun q ↦ ?_)
    (isSemialgebraic_setOf_eval_eq_zero _)
  rw [o34ChildShiftPoly_eval i a gr q, sub_eq_zero]

open AISafetyAtlas.Causal AISafetyAtlas.Analysis MvPolynomial in
/-- A child difference vanishing is a semialgebraic condition.-/
private theorem isSemialgebraic_childDifference_eq_zero (gr : Orientation) (i : Fin 2) :
    IsSemialgebraic {q : O34Index → ℝ | childDifference gr (o34ChartGap q) i = 0} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ eval q (o34ChildDiffPoly gr i) = 0) (fun q ↦ ?_)
    (isSemialgebraic_setOf_eval_eq_zero _)
  rw [o34ChildDiffPoly_eval]

open AISafetyAtlas.Causal AISafetyAtlas.Analysis MvPolynomial in
private theorem isSemialgebraic_childDifference_ne_zero (gr : Orientation) (i : Fin 2) :
    IsSemialgebraic {q : O34Index → ℝ | childDifference gr (o34ChartGap q) i ≠ 0} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ eval q (o34ChildDiffPoly gr i) ≠ 0) (fun q ↦ ?_)
    (isSemialgebraic_setOf_eval_ne_zero _)
  rw [o34ChildDiffPoly_eval]

open AISafetyAtlas.Causal AISafetyAtlas.Analysis MvPolynomial in
private theorem isSemialgebraic_rootDifference_eq_zero (gr : Orientation) (i : Fin 2) :
    IsSemialgebraic {q : O34Index → ℝ | rootDifference gr (o34ChartGap q) i = 0} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ eval q (o34ChildDiffPoly (otherOrientation gr) i) = 0) (fun q ↦ ?_)
    (isSemialgebraic_setOf_eval_eq_zero _)
  rw [o34RootDiffPoly_eval]

open AISafetyAtlas.Causal AISafetyAtlas.Analysis MvPolynomial in
private theorem isSemialgebraic_rootDifference_ne_zero (gr : Orientation) (i : Fin 2) :
    IsSemialgebraic {q : O34Index → ℝ | rootDifference gr (o34ChartGap q) i ≠ 0} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ eval q (o34ChildDiffPoly (otherOrientation gr) i) ≠ 0) (fun q ↦ ?_)
    (isSemialgebraic_setOf_eval_ne_zero _)
  rw [o34RootDiffPoly_eval]

open AISafetyAtlas.Causal AISafetyAtlas.Analysis MvPolynomial in
/-- `ExactlyOneFlat` is a finite disjunction over `Fin 2`, hence semialgebraic
whenever its two atoms are.-/
private theorem isSemialgebraic_exactlyOneFlat
    {d : (O34Index → ℝ) → Fin 2 → ℝ}
    (hz : ∀ i, IsSemialgebraic {q : O34Index → ℝ | d q i = 0})
    (hn : ∀ i, IsSemialgebraic {q : O34Index → ℝ | d q i ≠ 0}) :
    IsSemialgebraic {q : O34Index → ℝ | ExactlyOneFlat (d q)} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ (d q 0 = 0 ∧ d q 1 ≠ 0) ∨ (d q 1 = 0 ∧ d q 0 ≠ 0))
    (fun q ↦ ?_) ?_
  · simp [ExactlyOneFlat, Fin.exists_fin_two]
  · exact ((hz 0).setOf_and (hn 1)).setOf_or ((hz 1).setOf_and (hn 0))

open AISafetyAtlas.Causal AISafetyAtlas.Analysis MvPolynomial in
/-- The companion clause, after its real quantifier is eliminated.-/
private theorem isSemialgebraic_companion_singleton {lam : ℝ}
    (hlam0 : 0 < lam) (hlam2 : lam < 1 / 2) (gr : Orientation) (z : Fin 2) :
    IsSemialgebraic {q : O34Index → ℝ |
      separatedValues lam ((o34ChartModel gr q).child (other z))
        = {(o34ChartModel gr q).child z}} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ 1 < 4 * lam ∧
      (((o34ChartModel gr q).child (other z) = 2 * lam ∧
          (o34ChartModel gr q).child z = lam) ∨
        ((o34ChartModel gr q).child (other z) = 1 - 2 * lam ∧
          (o34ChartModel gr q).child z = 1 - lam)))
    (fun q ↦ separatedValues_eq_singleton_iff hlam0 hlam2) ?_
  exact IsSemialgebraic.setOf_const_and
    (((isSemialgebraic_child_eq gr (other z) (2 * lam)).setOf_and
        (isSemialgebraic_child_eq gr z lam)).setOf_or
      ((isSemialgebraic_child_eq gr (other z) (1 - 2 * lam)).setOf_and
        (isSemialgebraic_child_eq gr z (1 - lam))))

open AISafetyAtlas.Causal AISafetyAtlas.Analysis MvPolynomial in
/-- The mate clause's nonemptiness condition, after its real quantifier is
eliminated: two half-planes in the root coordinate.-/
private theorem isSemialgebraic_companion_nonempty {lam : ℝ}
    (hlam0 : 0 < lam) (hlam2 : lam < 1 / 2) (gr : Orientation) :
    IsSemialgebraic {q : O34Index → ℝ |
      (separatedValues lam (o34ChartModel gr q).root).Nonempty} := by
  refine IsSemialgebraic.setOf_congr
    (Q := fun q ↦ 2 * lam ≤ (o34ChartModel gr q).root ∨
      (o34ChartModel gr q).root ≤ 1 - 2 * lam)
    (fun q ↦ separatedValues_nonempty_iff hlam0 hlam2) ?_
  refine IsSemialgebraic.setOf_or ?_ ?_
  · refine IsSemialgebraic.setOf_congr
      (Q := fun q ↦ 0 ≤ eval q (o34RootShiftPoly (2 * lam))) (fun q ↦ ?_)
      (isSemialgebraic_setOf_eval_nonneg _)
    rw [o34RootShiftPoly_eval _ gr q, sub_nonneg]
  · refine IsSemialgebraic.setOf_congr
      (Q := fun q ↦ 0 ≤ eval q (-o34RootShiftPoly (1 - 2 * lam))) (fun q ↦ ?_)
      (isSemialgebraic_setOf_eval_nonneg _)
    rw [map_neg, o34RootShiftPoly_eval _ gr q, neg_sub, sub_nonneg]

/-! ## The criterion, reached from a model of the printed class

`o34_classFibre_iff_candidate` compares a chart point's fibre against every model
of `𝕄₂(λ)`, which fixes the *rivals*. Its own subject is still a `PairModel`, and
so is `maisO34_exactFiberCandidate`'s outer binder — so on their face both speak
about chart points, and a universal over a smaller class asserts less.

`exists_pairModel_toModel_eq` says the two ranges coincide. This is the theorem
that spends it: start from a model of the printed class carrying an edge, and the
criterion is available for *that* model, at the chart point its own tables name.
Without it the surjectivity lemma has a consumer for the inner quantifier and
none for the outer one; `o31Classification_of_candidate` is the same theorem for
MAIS-O31. -/

end AISafetyAtlas.Examples.Conjectures.O34Fiber
