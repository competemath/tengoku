import Tengoku.Seed.Data.Int.LeastGreatest
import Tengoku.Seed.Data.Int.ConditionallyCompleteOrder
import Tengoku.Seed.Order.ConditionallyCompleteLattice.Basic
import Tengoku.Seed.LinearAlgebra.Quotient.Defs
import Tengoku.Seed.Algebra.Module.Submodule.Lattice
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

/-!
# Integer filtration degree and initial forms

Section 3 uses an exhaustive separated increasing filtration indexed by all
integers, including negative integers.  These generic lemmas prove that every
nonzero element has a least layer and that its image modulo the preceding layer
is nonzero.  They do not assume any coordinate obstruction or associated-graded
presentation.
-/

namespace StableCoordinate
namespace IntegerFiltration

/-- The integer degree is the infimum of the layers containing an element.
The lemmas below show that for a nonzero element this infimum is attained. -/
noncomputable def degree {A : Type*} (F : ℤ → Set A) (x : A) : ℤ :=
  sInf {d : ℤ | x ∈ F d}

/-- A least layer computes the filtration degree. -/
theorem degree_eq_of_least {A : Type*} (F : ℤ → Set A) {x : A} {d : ℤ}
    (hd : x ∈ F d) (hleast : ∀ e : ℤ, x ∈ F e → d ≤ e) :
    degree F x = d := by
  exact IsLeast.csInf_eq ⟨hd, hleast⟩

section LeastDegree

variable {A : Type*} [Zero A]

/-- An exhaustive separated increasing integer filtration gives every nonzero
object a genuine least degree, not merely an infimum or a natural-number degree. -/
theorem exists_least_index (F : ℤ → Set A) (hmono : Monotone F)
    (hexhaustive : ∀ x : A, ∃ d : ℤ, x ∈ F d)
    (hseparated : ∀ x : A, (∀ d : ℤ, x ∈ F d) → x = 0)
    {x : A} (hx : x ≠ 0) :
    ∃ d : ℤ, x ∈ F d ∧ ∀ e : ℤ, x ∈ F e → d ≤ e := by
  classical
  obtain ⟨b, hb⟩ : ∃ b : ℤ, x ∉ F b := by
    by_contra habs
    push Not at habs
    exact hx (hseparated x habs)
  apply Int.exists_least_of_bdd _ (hexhaustive x)
  refine ⟨b + 1, fun e he => ?_⟩
  have hnot : ¬ e ≤ b := fun heb => hb (hmono heb he)
  omega

/-- The degree of a nonzero element is an attained least index. -/
theorem degree_spec (F : ℤ → Set A) (hmono : Monotone F)
    (hexhaustive : ∀ x : A, ∃ d : ℤ, x ∈ F d)
    (hseparated : ∀ x : A, (∀ d : ℤ, x ∈ F d) → x = 0)
    {x : A} (hx : x ≠ 0) :
    x ∈ F (degree F x) ∧ ∀ e : ℤ, x ∈ F e → degree F x ≤ e := by
  obtain ⟨d, hd, hleast⟩ := exists_least_index F hmono hexhaustive hseparated hx
  rw [degree_eq_of_least F hd hleast]
  exact ⟨hd, hleast⟩

/-- The preceding layer misses every nonzero element. -/
theorem not_mem_degree_sub_one (F : ℤ → Set A) (hmono : Monotone F)
    (hexhaustive : ∀ x : A, ∃ d : ℤ, x ∈ F d)
    (hseparated : ∀ x : A, (∀ d : ℤ, x ∈ F d) → x = 0)
    {x : A} (hx : x ≠ 0) : x ∉ F (degree F x - 1) := by
  intro h
  have := (degree_spec F hmono hexhaustive hseparated hx).2 _ h
  omega

end LeastDegree

section InitialForm

variable {K A : Type*} [Ring K] [AddCommGroup A] [Module K A]

/-- A representative in the first possible layer is nonzero in the quotient by
its preceding layer.  This is the nonvanishing needed for an initial form. -/
theorem initial_form_ne_zero (F : ℤ → Submodule K A) {d : ℤ} {x : A}
    (hx : x ∈ F d) (hxprev : x ∉ F (d - 1)) :
    (Submodule.Quotient.mk ⟨x, hx⟩ :
      (F d) ⧸ (F (d - 1)).comap (F d).subtype) ≠ 0 := by
  intro h
  have hmem : (⟨x, hx⟩ : F d) ∈ (F (d - 1)).comap (F d).subtype :=
    (Submodule.Quotient.mk_eq_zero _).mp h
  exact hxprev hmem

/-- Separation phrased as a lattice intersection implies elementwise separation. -/
theorem separated_of_iInf_eq_bot (F : ℤ → Submodule K A) (hF : ⨅ d, F d = ⊥)
    (x : A) (hx : ∀ d : ℤ, x ∈ F d) : x = 0 := by
  have hx' : x ∈ ⨅ d, F d := (Submodule.mem_iInf F).mpr hx
  rw [hF] at hx'
  exact hx'

end InitialForm

end IntegerFiltration
end StableCoordinate

end OAI
