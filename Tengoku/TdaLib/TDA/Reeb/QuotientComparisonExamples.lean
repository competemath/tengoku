import Tengoku.TdaLib.TDA.Reeb.QuotientComparison

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reeb quotient functor fixtures

Regression fixtures for `TDA.Reeb.ReebQuotient.map`, `componentComparison` and the slice
packaging:

* a noninjective height-preserving surjection, the fold `(Bool × ℝ, fold) → (ℝ, id)`, whose
  induced `Q_fold` is not injective and whose induced map on path components at `⊤` is not
  injective, together with the naturality square of `η` at the fold;
* the identity of `ℝ`;
* an empty domain, where both sides of `η` are empty at every open;
* the real-valued slice packaging in universe `0`, a non-real target `ℝ × ℝ` and `Q_h` across
  independent carrier universes.

The fold shows that a continuous height-preserving surjection need not induce injections on path
components of inverse images. It is not a witness that `η` itself fails to be injective; that
witness is the topologist's sine curve of de Silva, Munch and Patel, Example 3.21, in
`TDA.Reeb.QuotientComparisonSineCurveExamples`.
-/

open CategoryTheory

universe u v w

namespace TDA.Reeb.Examples

open ReebQuotient

/-- The fold `Bool × ℝ → ℝ`, `(b, t) ↦ t`. It is the two-sheeted real height on `Bool × ℝ`, and
also a non-injective height-preserving surjection from `(Bool × ℝ, fold)` to `(ℝ, id)`.-/
def fold : C(Bool × ℝ, ℝ) := ContinuousMap.snd

/--
@isnad1 id=eq.0h1v.s7.3e7f6104b8f0 from=translated src=- shape=a421eba6 vocab=ed32f469
-/
theorem fold_comm : ∀ p, (ContinuousMap.id ℝ) (fold p) = fold p := fun _ => rfl

/--
@isnad1 id=surjecti.0h0v.s5.e517f917e553 from=translated src=- shape=31d37576 vocab=50a01713
-/
theorem fold_surjective : Function.Surjective fold := fun t => ⟨(false, t), rfl⟩

/--
@isnad1 id=not.0h0v.s5.aef5673fa5ed from=translated src=- shape=170d2a5f vocab=dd69d534
-/
theorem fold_not_injective : ¬ Function.Injective fold := fun hi => by
  simpa using hi (a₁ := (false, 0)) (a₂ := (true, 0)) rfl

/-- The two sheets stay distinct in `Q_fold`: a path in `Bool × ℝ` has constant first coordinate.
@isnad1 id=ne.0h0v.s6.4a210316113b from=translated src=- shape=1bca3ce9 vocab=7667e16b
-/
theorem fold_mk_ne : mk fold (false, 0) ≠ mk fold (true, 0) := by
  intro h
  obtain ⟨γ, -⟩ := (mk_eq_mk_iff _).1 h
  have := PreconnectedSpace.constant inferInstance (continuous_fst.comp γ.continuous)
    (x := 0) (y := 1)
  simp at this

/-- The quotient map induced by the fold identifies them, so it is not injective.
@isnad1 id=not.0h0v.s8.300a7064567e from=translated src=- shape=9c239631 vocab=97b5def2
-/
theorem map_fold_not_injective : ¬ Function.Injective (map fold fold_comm) := fun hi =>
  fold_mk_ne (hi rfl)

/-- A continuous height-preserving surjection need not induce injections on path components of
inverse images: `C_fold` at `U = ⊤` merges the two sheets.
@isnad1 id=not.0h0v.s11.f15394376c49 from=translated src=- shape=ed0dc86d vocab=77effc6c
-/
theorem componentNatTrans_fold_not_injective :
    ¬ Function.Injective ((componentNatTrans fold fold_comm).app ⊤) := by
  intro hi
  have h := @hi (ZerothHomotopy.mk ⟨(false, 0), trivial⟩) (ZerothHomotopy.mk ⟨(true, 0), trivial⟩)
    (by rfl)
  obtain ⟨γ⟩ := Quotient.exact h
  have := PreconnectedSpace.constant inferInstance
    (continuous_fst.comp (continuous_subtype_val.comp γ.continuous)) (x := 0) (y := 1)
  simp at this

end TDA.Reeb.Examples
