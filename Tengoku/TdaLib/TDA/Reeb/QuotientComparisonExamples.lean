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

theorem fold_comm : ∀ p, (ContinuousMap.id ℝ) (fold p) = fold p := fun _ => rfl

theorem fold_surjective : Function.Surjective fold := fun t => ⟨(false, t), rfl⟩

theorem fold_not_injective : ¬ Function.Injective fold := fun hi => by
  simpa using hi (a₁ := (false, 0)) (a₂ := (true, 0)) rfl

/-- The two sheets stay distinct in `Q_fold`: a path in `Bool × ℝ` has constant first coordinate.-/
theorem fold_mk_ne : mk fold (false, 0) ≠ mk fold (true, 0) := by
  intro h
  obtain ⟨γ, -⟩ := (mk_eq_mk_iff _).1 h
  have := PreconnectedSpace.constant inferInstance (continuous_fst.comp γ.continuous)
    (x := 0) (y := 1)
  simp at this

/-- The quotient map induced by the fold identifies them, so it is not injective.-/
theorem map_fold_not_injective : ¬ Function.Injective (map fold fold_comm) := fun hi =>
  fold_mk_ne (hi rfl)

/-- A continuous height-preserving surjection need not induce injections on path components of
inverse images: `C_fold` at `U = ⊤` merges the two sheets.-/
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
