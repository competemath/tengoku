import Tengoku.Seed.Logic.Relation
import Tengoku.Seed.Order.WellFounded

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Reachability from the unique source of a ranked relation -/
set_option autoImplicit false
namespace MagnitudeConjecture.RankedReachability
universe u
variable {V : Type u}

/-- In a relation with strictly increasing natural rank, every vertex is
reachable from its unique source.
@isnad1 id=refltran.2h5v.s5.06cf1dae4f8d from=translated src=- shape=cdf8cac5 vocab=dec87ef5
-/
theorem source_reaches (rank : V → ℕ) (E : V → V → Prop)
    (hE : ∀ x y, E x y → rank x < rank y)
    (source : V) (hsource : ∀ x, (¬ ∃ y, E y x) → x = source) :
    ∀ x, Relation.ReflTransGen E source x := by
  classical
  intro x
  induction x using (measure rank).wf.induction with
  | h x ih =>
    by_cases hx : ∃ y, E y x
    · obtain ⟨y, hy⟩ := hx
      exact (ih y (hE y x hy)).tail hy
    · rw [hsource x hx]

end MagnitudeConjecture.RankedReachability
