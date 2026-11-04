import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowUniqueness.eq_or_eq_or_eq_of_quadratic_invariant` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowUniqueness.eq_of_goodSolution_of_trace_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowUniqueness.three_goodSolutions_pairwise_eq` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# At most two reconstructed solutions of the right matrix quadratic

This module combines two ordinary algebraic inputs:

* the trace of every constrained `3 x 3` solution satisfies one fixed monic
  scalar quadratic;
* on the displayed nonzero-denominator open, the trace determines the matrix
  through the Cayley--Hamilton reconstruction certificate.

The conclusion is stated without finite-set or cardinality infrastructure:
among any three good solutions, two are equal.  This is only a conditional
matrix theorem.  It does not prove existence, genericity, chart coverage, an
Albert-model identification, or an invariant-field degree.
-/

noncomputable section

namespace AlbertLean.Generic.FourRowUniqueness

open AlbertLean.Generic.FourRowFactorization
open AlbertLean.Generic.FourRowTrace

universe u v

/-- A monic scalar quadratic cannot have three pairwise-distinct roots over a
field.  This wrapper records the disjunctive form used below.-/
theorem eq_or_eq_or_eq_of_quadratic_invariant
    {K : Type u} [Field K] {A : Type v}
    (P : A -> Prop) (f : A -> K) (a b : K)
    (hroot : ∀ x, P x -> f x ^ 2 + b * f x + a = 0)
    (hinjective : ∀ {x y}, P x -> P y -> f x = f y -> x = y)
    {x y z : A} (hx : P x) (hy : P y) (hz : P z) :
    x = y ∨ x = z ∨ y = z := by
  rcases eq_or_eq_or_eq_of_three_quadratic_roots b a (f x) (f y) (f z)
      (hroot x hx) (hroot y hy) (hroot z hz) with hxy | hxz | hyz
  · exact Or.inl (hinjective hx hy hxy)
  · exact Or.inr (Or.inl (hinjective hx hz hxz))
  · exact Or.inr (Or.inr (hinjective hy hz hyz))

section Matrices

variable {K : Type u} [Field K]

abbrev Mat3 (K : Type u) := Matrix (Fin 3) (Fin 3) K

/-- The right reconstruction denominator at a proposed trace `t`.-/
def reconstructionDenominator
    (U V : Mat3 K) (c d t : K) : Mat3 K :=
  U ^ 2 - V + t • U + (-d - 1 - c - t) • 1

/-- A solution lying on the explicit trace-reconstruction open.  The two
global determinant identities for `V` and `1-U+V` are deliberately kept out
of this predicate because they depend only on the shared parameters.-/
structure GoodSolution
    (U V : Mat3 K) (c d : K) (X : Mat3 K) : Prop where
  quadratic : X ^ 2 + X * U + V = 0
  det_eq : X.det = c
  det_one_add_eq : (1 + X).det = -d
  denominator_det_ne_zero :
    (reconstructionDenominator U V c d (Matrix.trace X)).det ≠ 0

/-- On the reconstruction open, two constrained solutions with equal trace
are equal.  Only the common Cayley--Hamilton reconstruction certificate and
right cancellation by the common denominator are used.-/
theorem eq_of_goodSolution_of_trace_eq
    (U V : Mat3 K) (c d : K) {X Y : Mat3 K}
    (hX : GoodSolution U V c d X)
    (hY : GoodSolution U V c d Y)
    (htrace : Matrix.trace X = Matrix.trace Y) : X = Y := by
  have hRX :=
    matrix_eq_trace_reconstruction_of_det_ne_zero X U V c d
      hX.quadratic hX.det_eq hX.det_one_add_eq (by
        simpa only [reconstructionDenominator] using
          hX.denominator_det_ne_zero)
  have hRY :=
    matrix_eq_trace_reconstruction_of_det_ne_zero Y U V c d
      hY.quadratic hY.det_eq hY.det_one_add_eq (by
        simpa only [reconstructionDenominator] using
          hY.denominator_det_ne_zero)
  calc
    X = (c • 1 - V * U - Matrix.trace X • V) *
        (U ^ 2 - V + Matrix.trace X • U +
          (-d - 1 - c - Matrix.trace X) • 1)⁻¹ := hRX
    _ = (c • 1 - V * U - Matrix.trace Y • V) *
        (U ^ 2 - V + Matrix.trace Y • U +
          (-d - 1 - c - Matrix.trace Y) • 1)⁻¹ := by rw [htrace]
    _ = Y := hRY.symm

/-- Concrete at-most-two endpoint.  Under the shared endpoint identities,
every good solution has a trace satisfying the same scalar quadratic; the
preceding reconstruction lemma makes that trace injective on good solutions.
Thus any three displayed solutions contain an equal pair.
@isnad1 id=or.7h8v.s8.62834c544081 from=translated src=- shape=0539a050 vocab=bee68413
-/
theorem three_goodSolutions_pairwise_eq
    (U V : Mat3 K) (c d : K)
    (hc : c ≠ 0) (hd : d ≠ 0)
    (hdetV : V.det = c ^ 2)
    (hdetNegOne : (1 - U + V).det = d ^ 2)
    (X Y Z : Mat3 K)
    (hX : GoodSolution U V c d X)
    (hY : GoodSolution U V c d Y)
    (hZ : GoodSolution U V c d Z) :
    X = Y ∨ X = Z ∨ Y = Z := by
  let b : K := (quadraticPolynomial U V).coeff 5
  let a : K :=
    (quadraticPolynomial U V).coeff 4 + 2 * (1 + c + d) -
      (quadraticPolynomial U V).coeff 5
  apply eq_or_eq_or_eq_of_quadratic_invariant
    (P := GoodSolution U V c d) (f := Matrix.trace) a b
  · intro W hW
    simpa [a, b] using
      trace_satisfies_quadratic_of_matrix_constraints W U V c d
        hW.quadratic hc hd hW.det_eq hW.det_one_add_eq hdetV hdetNegOne
  · intro W W' hW hW' htrace
    exact eq_of_goodSolution_of_trace_eq U V c d hW hW' htrace
  · exact hX
  · exact hY
  · exact hZ

end Matrices

end AlbertLean.Generic.FourRowUniqueness
