/-
# Leading monomials

A vector space with a finite basis of *monomials* `X`, linearly ordered, is `X → K`. The *leading
monomial* of a nonzero vector is the largest monomial of its support (`IsLeadingOf`), and the
leading monomials of a set of vectors are those of its members (`IsLeading`): for the relations of
an operad presented in a free shuffle operad with a monomial order, this is where a Gröbner basis
starts.

When an operad is the linearization of a set operad, or the associated graded of a filtered one,
the evaluation of the free operad sends every monomial to a basis element or to zero: it is the
linearization of a map `f : X → Option Y`, whose kernel is the space of vectors with vanishing sum
over every fiber (`fiberKer`). **The leading monomials of that kernel are the monomials sent to
zero and those which are not the least of their fiber** (`isLeading_fiberKer_iff`).

**A Gröbner criterion** (`isLeading_iff_of_supportedOn`, `isCompl_supportedOn`): if every monomial
outside a set `N` is the leading monomial of a vector of a space `I`, then every vector reduces
modulo `I` to one supported on `N` (`exists_reduction`, the division algorithm); if moreover no
nonzero vector of `I` is supported on `N` — for instance because a linear map killing `I` is
injective on the vectors supported on `N` — then the leading monomials of `I` are exactly the
monomials outside `N`, and the vectors supported on `N` are a complement of `I`. For `I` an
ideal of a free operad in some arity and `N` the monomials not divisible by the leading monomials
of a set of generators, this says that the generators are a Gröbner basis and that the normal
monomials are a basis of the quotient.
-/
import Tengoku.Seed.Algebra.BigOperators.Pi
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Algebra.Module.Pi
import Tengoku.Seed.Algebra.Module.Submodule.Defs
import Tengoku.Seed.Algebra.Field.Basic
import Tengoku.Seed.Algebra.Module.Submodule.Lattice
import Tengoku.Seed.Data.Fintype.Card
import Tengoku.Seed.Data.Finset.Max
import Tengoku.Seed.Tactic.Abel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Operad

section Ring

variable {K : Type*} [Ring K] {X Y : Type*}

section Fiber

variable [Fintype X] [DecidableEq Y]

variable (K) in
/-- **The kernel of the linearization of a map** `f : X → Option Y`, which sends a monomial to the
basis vector of its value, or to zero: the vectors whose sum over each fiber `f⁻¹(y)` vanishes.-/
def fiberKer (f : X → Option Y) : Submodule K (X → K) where
  carrier := {v | ∀ y, ∑ x ∈ Finset.univ.filter (fun x => f x = some y), v x = 0}
  add_mem' := by
    intro a b ha hb y
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at ha hb ⊢
    rw [ha y, hb y, add_zero]
  zero_mem' := by
    intro y
    simp
  smul_mem' := by
    intro c v hv y
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul] at hv ⊢
    rw [← Finset.mul_sum, hv y, mul_zero]

lemma mem_fiberKer {f : X → Option Y} {v : X → K} :
    v ∈ fiberKer K f ↔ ∀ y, ∑ x ∈ Finset.univ.filter (fun x => f x = some y), v x = 0 :=
  Iff.rfl

end Fiber

variable [LinearOrder X]

/-- `x` is **the leading monomial** of `v`: in the support of `v`, and above the rest of it.-/
def IsLeadingOf (v : X → K) (x : X) : Prop := v x ≠ 0 ∧ ∀ y, x < y → v y = 0

/-- A vector has at most one leading monomial.-/
lemma IsLeadingOf.unique {v : X → K} {x x' : X} (h : IsLeadingOf v x) (h' : IsLeadingOf v x') :
    x = x' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.1 (h.2 x' hlt)
  · exact h.1 (h'.2 x hlt)

/-- **The leading monomials of a set of vectors**: those of its members.-/
def IsLeading (V : Set (X → K)) (x : X) : Prop := ∃ v ∈ V, IsLeadingOf v x

variable [Fintype X] [DecidableEq Y]

/-- **The leading monomials of the kernel of a linearized map** are the monomials sent to zero and
those which are not the least of their fiber.-/
theorem isLeading_fiberKer_iff [Nontrivial K] (f : X → Option Y) (x : X) :
    IsLeading (fiberKer K f : Set (X → K)) x ↔ f x = none ∨ ∃ x' < x, f x' = f x := by
  constructor
  · rintro ⟨v, hv, hx, hmax⟩
    by_contra hcon
    simp only [not_or, not_exists, not_and] at hcon
    obtain ⟨hne, hmin⟩ := hcon
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 hne
    have h0 := (mem_fiberKer.1 hv) y
    rw [Finset.sum_eq_single x] at h0
    · exact hx h0
    · intro z hz hzx
      rw [Finset.mem_filter] at hz
      rcases lt_or_gt_of_ne hzx with h | h
      · exact absurd (hz.2.trans hy.symm) (hmin z h)
      · exact hmax z h
    · intro hxs
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ x, hy⟩) hxs
  · rintro (h | ⟨x', hx', h⟩)
    · refine ⟨Pi.single x 1, fun y => ?_, by simp, fun z hz => ?_⟩
      · rw [Finset.sum_pi_single', ite_eq_right]
        rw [Finset.mem_filter, h]
        simp
      · simp [hz.ne']
    · refine ⟨Pi.single x 1 - Pi.single x' 1, fun y => ?_, ?_, fun z hz => ?_⟩
      · simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single',
          Finset.mem_filter, Finset.mem_univ, true_and, h, sub_self]
      · simp [hx'.ne']
      · simp [hz.ne', (hx'.trans hz).ne']

end Ring

/-! ## A Gröbner criterion -/

section Field

variable {K : Type*} [Field K] {X : Type*}

variable (K) in
/-- The vectors supported on a set `N` of monomials.-/
def supportedOn (N : Set X) : Submodule K (X → K) where
  carrier := {v | ∀ x ∉ N, v x = 0}
  add_mem' ha hb x hx := by simp [ha x hx, hb x hx]
  zero_mem' _ _ := rfl
  smul_mem' c v hv x hx := by simp [hv x hx]

lemma mem_supportedOn {N : Set X} {v : X → K} : v ∈ supportedOn K N ↔ ∀ x ∉ N, v x = 0 :=
  Iff.rfl

variable [LinearOrder X] [Fintype X]

end Field

end Operad
