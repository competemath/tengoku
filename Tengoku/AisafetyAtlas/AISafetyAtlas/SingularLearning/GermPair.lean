module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.SylvesterPair
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.FreeBlockPair

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An arbitrary indefinite form plus a free-block germ

Two modules each hold half of what print's two-sided band lemma asks for.

* `hasLocalVolumeOrder_freeBlockGerm` proves the `Θ(ε)` band order
  for `|Q(ξ) + g(ζ)|` with a continuous germ `g` on a free block, but only when
  the quadratic part is literally `modelBandForm p q`, the model signature form.
* `hasLocalVolumeOrder_abs_matrixQuadForm` handles an arbitrary
  nondegenerate indefinite matrix form, but with no germ: the absolute value is
  taken of the quadratic part alone.

Neither is enough on its own.  A caller who holds an arbitrary `K` *and* a germ
cannot reach the first, because its statement names the model form; and cannot
reach the second, because the germ is added inside the absolute value, so the
transport `hasLocalVolumeOrder_abs_of_congruent` performs — which only ever sees
`|Q|` — has nothing to say about `|Q + g|`.

What joins them is a **signed** congruence.  `hasLocalVolumeOrder_abs_of_diagonal`
already builds the linear equivalence carrying a diagonalised form to the model,
and then discards it, keeping only the identity between absolute values.  Kept
signed, the same equivalence carries `Q(ξ) + g(ζ)` to `modelBandForm p q (e ξ) +
g(ζ)`, which is exactly `freeBlockGerm`, and the free block is untouched because
the equivalence is the identity there.

## Why the congruence is a disjunction

`exists_model_congruence` concludes

    `Q = modelBandForm p q ∘ e`   **or**   `Q = -(modelBandForm p q ∘ e)`,

with `2 ≤ p` in both branches, and the disjunction is not slack in the proof: the
one-sided statement is false.  Sylvester's law of inertia makes the signature an
invariant of a form under linear congruence, so `Q = modelBandForm p q ∘ e`
forces `(p, q)` to *be* the signature of `Q`.  At `K = diag(1,-1,-1,-1)` that
signature is `(1, 3)`, and no congruence to a model form with `2 ≤ p` exists.
Negating the form exchanges the blocks, which is why the second branch always
applies when the first cannot: `-Q` has signature `(3, 1)` there.

That last paragraph is an argument in prose, not a checked declaration: the tree
does not carry the inertia-invariance theorem in the form "no such `e` exists",
so the disjunction is *not* accompanied by a Lean proof that it cannot be
narrowed.  What is checked is that the disjunctive statement is provable and that
its second branch is the one an explicit signature-`(1,3)` matrix takes —
`Examples.SingularLearning.GermPair.hasLocalVolumeOrder_negMinkowski4_add_evenGerm`.

The `2 ≤ p` is what the band estimate needs and is where `3 ≤ n` is spent — both
blocks are nonempty because the form takes both signs, and three indices split
between two nonempty blocks put at least two in one of them.

## What the sign costs downstream

Nothing.  `|(-Q) + (-g)| = |Q + g|`, and `-g` is continuous and vanishes at the
origin whenever `g` does, so the negative branch of `exists_model_congruence` is
absorbed by running the same argument at `-g`.  The germ hypotheses are stable
under negation, which is the only reason the disjunction is harmless here; a
statement whose germ hypotheses were one-sided would have to carry the branch.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory
open scoped Matrix

/-! ## The signed congruence

`hasLocalVolumeOrder_abs_of_diagonal` builds the coordinate change and keeps only
`|Q x| = modelBandGerm p q (e x)`.  These two lemmas keep the signed identity
`Q x = modelBandForm p q (e x)` instead, which is what survives adding a germ.
-/

/-! ## Carrying a congruence across the free block

The equivalence produced above acts on the quadratic coordinates only.  Extended
by the identity on the free block it is still a continuous linear equivalence of
the ambient space, and `hasLocalVolumeOrder_comp_continuousLinearEquiv` transports
the pair back along it.
-/

/-- The congruence extended by the identity on the free block.-/
@[expose] public noncomputable def germCongruence (p q s : ℕ)
    (e : EuclideanSpace ℝ (Fin (p + q)) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + q))) :
    EuclideanSpace ℝ (Fin (p + q + s)) ≃L[ℝ] EuclideanSpace ℝ (Fin (p + q + s)) :=
  (((splitLE (p + q) s).symm.trans
    (e.toLinearEquiv.prodCongr (LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin s))))).trans
      (splitLE (p + q) s)).toContinuousLinearEquiv

/-! ## Print's Lemma 2, in full generality -/

end AISafetyAtlas.SingularLearning
