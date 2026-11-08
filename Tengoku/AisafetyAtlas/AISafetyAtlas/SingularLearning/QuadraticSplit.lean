module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.PairTransfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The signature splitting of a Euclidean space

Stage 3 of the MAIS-O77(b) programme needs the local band order of a
nondegenerate indefinite quadratic form.  Mathlib supplies Sylvester's law of
inertia -- QuadraticForm.equivalent_one_neg_one_weighted_sum_squared, verified
present at the pinned revision -- which reduces any such form to a signed sum of
squares, so what is left is the *model* germ

    `|‖u‖² - ‖v‖²|`   on   `ℝ^p × ℝ^q`,

read on `EuclideanSpace ℝ (Fin (p + q))`, which is where the atlas's volume
interface lives.

The coordinate splitting itself is `euclideanProdEquiv`, already in
`PairTransfer` and already proved measure preserving there.  This module adds
only what that packaging lacks: the same map as a **linear** equivalence, which
is what makes the germ's degree-two homogeneity a one-line consequence of
`map_smul` rather than a coordinate computation.

The two packagings are the same function by `rfl`, so the measure preservation is
inherited rather than reproved.  Keeping that as a stated lemma rather than an
appeal to "obviously the same map" is the point: a reshape whose measure or norm
behaviour is merely assumed is exactly the class of step whose failure no gate
reports, because every downstream statement still elaborates.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory

/-- The splitting as a linear equivalence.  The same function as
`euclideanProdEquiv` (see `coe_splitLE`); this packaging carries the linear
structure that `MeasurableEquiv` does not.-/
@[expose] public noncomputable def splitLE (p q : ℕ) :
    (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃ₗ[ℝ]
      EuclideanSpace ℝ (Fin (p + q)) :=
  ((WithLp.linearEquiv 2 ℝ (Fin p → ℝ)).prodCongr (WithLp.linearEquiv 2 ℝ (Fin q → ℝ))).trans <|
    (LinearEquiv.sumArrowLequivProdArrow (Fin p) (Fin q) ℝ ℝ).symm.trans <|
      (LinearEquiv.funCongrLeft ℝ ℝ finSumFinEquiv.symm).trans
        (WithLp.linearEquiv 2 ℝ (Fin (p + q) → ℝ)).symm

/-- The linear packaging is the measurable one, by `rfl`.  Everything measure
theoretic about `splitLE` is inherited through this.-/
public theorem coe_splitLE (p q : ℕ) : ⇑(splitLE p q) = ⇑(euclideanProdEquiv p q) := rfl

/-! ## The model band germ

The germ whose local order Stage 3 must compute.  It is written on the ambient
Euclidean space, because that is where `HasLocalVolumeOrder` lives, but it is
*defined* through the split, so every statement about it can be moved to the
product by `measurePreserving_splitLE`.
-/

/-- **The model band germ of signature `(p, q)`**: the absolute value of the
nondegenerate form `‖u‖² - ‖v‖²`, read on `EuclideanSpace ℝ (Fin (p + q))`
through the coordinate split.-/
@[expose] public noncomputable def modelBandGerm (p q : ℕ)
    (w : EuclideanSpace ℝ (Fin (p + q))) : ℝ :=
  |‖((splitLE p q).symm w).1‖ ^ 2 - ‖((splitLE p q).symm w).2‖ ^ 2|

end AISafetyAtlas.SingularLearning
