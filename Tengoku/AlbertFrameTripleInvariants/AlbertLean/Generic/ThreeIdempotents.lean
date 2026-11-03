import Tengoku.Seed.Algebra.Ring.Defs
import Tengoku.Seed.Algebra.Module.Defs
import Tengoku.Seed.Tactic.Abel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms pairwise_mul_eq_zero_of_sum_eq_one` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms scalar_coefficient_eq_zero_of_adjoint_eq_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mul_self_eq_self_of_adjoint_eq_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms adjoint_eq_zero_iff_mul_self_eq_self` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Elementary frame identities

These lemmas use no Albert model and no associativity of multiplication.
-/

noncomputable section

namespace AlbertLean.Generic.ThreeIdempotents

universe u v

section Orthogonality

variable {A : Type u} [NonAssocRing A]

/-- Three idempotents summing to one are pairwise orthogonal when additive
doubling is injective. Only distributivity, commutativity, and the unit laws
are used; multiplication need not be associative.
@isnad1 id=and.6h4v.s8.8f495b3bd5fb from=translated src=- shape=0bcc62b3 vocab=e64b1f37
-/
theorem pairwise_mul_eq_zero_of_sum_eq_one
    (e0 e1 e2 : A)
    (hcomm : ∀ x y : A, x * y = y * x)
    (htwo : ∀ x : A, x + x = 0 → x = 0)
    (h0 : e0 * e0 = e0) (h1 : e1 * e1 = e1) (h2 : e2 * e2 = e2)
    (hsum : e0 + e1 + e2 = 1) :
    e0 * e1 = 0 ∧ e0 * e2 = 0 ∧ e1 * e2 = 0 := by
  have hr0 := congrArg (fun y : A => e0 * y) hsum
  have hr1 := congrArg (fun y : A => e1 * y) hsum
  have hr2 := congrArg (fun y : A => e2 * y) hsum
  have hpq : e0 * e1 + e0 * e2 = 0 := by
    simp only [mul_add, mul_one, h0] at hr0
    calc
      e0 * e1 + e0 * e2 = (e0 + e0 * e1 + e0 * e2) - e0 := by abel
      _ = 0 := by rw [hr0, sub_self]
  have hpr : e0 * e1 + e1 * e2 = 0 := by
    simp only [mul_add, mul_one, h1, hcomm e1 e0] at hr1
    calc
      e0 * e1 + e1 * e2 = (e0 * e1 + e1 + e1 * e2) - e1 := by abel
      _ = 0 := by rw [hr1, sub_self]
  have hqr : e0 * e2 + e1 * e2 = 0 := by
    simp only [mul_add, mul_one, h2, hcomm e2 e0, hcomm e2 e1] at hr2
    calc
      e0 * e2 + e1 * e2 = (e0 * e2 + e1 * e2 + e2) - e2 := by abel
      _ = 0 := by rw [hr2, sub_self]
  have hp2 : e0 * e1 + e0 * e1 = 0 := by
    calc
      e0 * e1 + e0 * e1 =
          (e0 * e1 + e0 * e2) + (e0 * e1 + e1 * e2) -
            (e0 * e2 + e1 * e2) := by abel
      _ = 0 := by rw [hpq, hpr, hqr]; simp
  have hp : e0 * e1 = 0 := htwo _ hp2
  have hq : e0 * e2 = 0 := by
    rw [hp, zero_add] at hpq
    exact hpq
  have hr : e1 * e2 = 0 := by
    rw [hp, zero_add] at hpr
    exact hpr
  exact ⟨hp, hq, hr⟩

end Orthogonality

section AdjointToIdempotent

variable {K : Type u} {A : Type v}
variable [Field K] [NonAssocRing A] [Module K A]

omit [Module K A] in
/-- Abstract cubic-adjoint step. `trace_sharp` and `trace_zero` isolate the
trace identity normally used to deduce that the quadratic scalar coefficient
vanishes when the adjoint does.
@isnad1 id=eq.3h6v.s6.3639982c10f1 from=translated src=- shape=6dade0b7 vocab=abbb7a30
-/
theorem scalar_coefficient_eq_zero_of_adjoint_eq_zero
    (trace scalar : A → K) (sharp : A → A) (x : A)
    (trace_sharp : trace (sharp x) = scalar x)
    (trace_zero : trace 0 = 0)
    (hsharp : sharp x = 0) : scalar x = 0 := by
  rw [hsharp, trace_zero] at trace_sharp
  exact trace_sharp.symm

/-- Trace one and adjoint zero imply idempotence from the standard cubic
adjoint identity. No power-associativity or Jordan identity is used here.
@isnad1 id=eq.5h6v.s8.0fbd727b9bab from=translated src=- shape=2a25241e vocab=dcb1ca52
-/
theorem mul_self_eq_self_of_adjoint_eq_zero
    (trace scalar : A → K) (sharp : A → A) (x : A)
    (adjoint_identity :
      sharp x = x * x - trace x • x + scalar x • (1 : A))
    (trace_sharp : trace (sharp x) = scalar x)
    (trace_zero : trace 0 = 0)
    (htrace : trace x = 1)
    (hsharp : sharp x = 0) : x * x = x := by
  have hscalar : scalar x = 0 :=
    scalar_coefficient_eq_zero_of_adjoint_eq_zero
      trace scalar sharp x trace_sharp trace_zero hsharp
  rw [hsharp, htrace, hscalar] at adjoint_identity
  have hdiff : x * x - x = 0 := by simpa using adjoint_identity.symm
  exact sub_eq_zero.mp hdiff

/-- In trace dimension three the converse needs only the same trace/sharp
identity and scalar doubling cancellation; no Newton identity is needed.
@isnad1 id=iff.6h6v.s9.a274a771c041 from=translated src=- shape=3ec2d863 vocab=dcb1ca52
-/
theorem adjoint_eq_zero_iff_mul_self_eq_self
    (trace scalar : A → K) (sharp : A → A) (x : A)
    (adjoint_identity : sharp x = x * x - trace x • x + scalar x • (1 : A))
    (trace_sharp : trace (sharp x) = scalar x) (trace_zero : trace 0 = 0)
    (trace_smul_one : ∀ k : K, trace (k • (1 : A)) = k + k + k)
    (htwo : ∀ k : K, k + k = 0 → k = 0) (htrace : trace x = 1) :
    sharp x = 0 ↔ x * x = x := by
  constructor
  · exact mul_self_eq_self_of_adjoint_eq_zero trace scalar sharp x
      adjoint_identity trace_sharp trace_zero htrace
  · intro hid
    have hs : sharp x = scalar x • (1 : A) := by
      simpa only [hid, htrace, one_smul, sub_self, zero_add] using adjoint_identity
    have ht : scalar x + scalar x + scalar x = scalar x := by
      simpa only [hs, trace_smul_one] using trace_sharp
    have hdouble : scalar x + scalar x = 0 := by
      calc
        scalar x + scalar x = (scalar x + scalar x + scalar x) - scalar x := by abel
        _ = 0 := by rw [ht, sub_self]
    rw [hs, htwo _ hdouble, zero_smul]

end AdjointToIdempotent

end AlbertLean.Generic.ThreeIdempotents
