/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.Koethe.ShiftWitness.Band

/-!
# The rational-function eigenvector of the backward shifts

Nonzero edge triples give nonzero degree-at-most-two polynomials. Their images
in `RatFunc k` are invertible. Reciprocal prefix products produce a genuine
(non-finitely-supported) eigenvector on the full function space.
-/

@[expose] public section

noncomputable section

namespace KoetheCounterexample
namespace ShiftWitness

universe u
variable {k : Type u} [Field k]

/-- A triple encoded as a polynomial of degree at most two. -/
def edgePolynomial (z : Triple k) : Polynomial k :=
  Polynomial.C (z 0) + Polynomial.X * Polynomial.C (z 1) +
    Polynomial.X ^ 2 * Polynomial.C (z 2)

/--
@isnad1 id=ne.1h2v.s6.a93652379a4c from=translated src=- shape=0c91ebb3 vocab=54749049
-/
theorem edgePolynomial_ne_zero (z : Triple k) (hz : z ≠ 0) :
    edgePolynomial z ≠ 0 := by
  intro h
  apply hz
  funext i
  fin_cases i
  · have hc := congrArg (fun p : Polynomial k => p.coeff 0) h
    simpa [edgePolynomial] using hc
  · have hc := congrArg (fun p : Polynomial k => p.coeff 1) h
    simpa [edgePolynomial, Polynomial.coeff_mul_C] using hc
  · have hc := congrArg (fun p : Polynomial k => p.coeff 2) h
    simpa [edgePolynomial, Polynomial.coeff_mul_C] using hc

/-- The polynomial edge weight embedded faithfully in the rational-function field. -/
def edge (z : Triple k) : RatFunc k :=
  algebraMap (Polynomial k) (RatFunc k) (edgePolynomial z)

/--
@isnad1 id=eq.0h2v.s9.e6e9a7eb0357 from=translated src=- shape=aa4c43b0 vocab=6f0885e9
-/
theorem edge_eq (z : Triple k) :
    edge z = algebraMap k (RatFunc k) (z 0) +
      RatFunc.X * algebraMap k (RatFunc k) (z 1) +
      RatFunc.X ^ 2 * algebraMap k (RatFunc k) (z 2) := by
  simp only [edge, edgePolynomial, map_add, map_mul, map_pow,
    RatFunc.algebraMap_C, RatFunc.algebraMap_X, RatFunc.algebraMap_eq_C]

/--
@isnad1 id=ne.1h2v.s6.3b3701eab1c4 from=translated src=- shape=0c91ebb3 vocab=71d5ddf0
-/
theorem edge_ne_zero (z : Triple k) (hz : z ≠ 0) : edge z ≠ 0 :=
  RatFunc.algebraMap_ne_zero (edgePolynomial_ne_zero z hz)

/-- Reciprocal prefix products, defined on the full sequence module. -/
def eigenvector (v : ℕ → Triple k) : Space (RatFunc k) :=
  fun n => (∏ i ∈ Finset.range n, edge (v i))⁻¹

/--
@isnad1 id=eq.0h2v.s5.431c9e541fe9 from=translated src=- shape=2db21a6b vocab=c5906d09
-/
@[simp] theorem eigenvector_zero (v : ℕ → Triple k) : eigenvector v 0 = 1 := by
  simp [eigenvector]

/--
@isnad1 id=ne.0h2v.s5.ccbf3f401a63 from=translated src=- shape=fb589fe9 vocab=d495be6a
-/
theorem eigenvector_ne_zero (v : ℕ → Triple k) : eigenvector v ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

/--
@isnad1 id=eq.1h3v.s6.48a97537309c from=translated src=- shape=81362815 vocab=9b8f7eb5
-/
theorem edge_mul_eigenvector_succ (v : ℕ → Triple k) (hv : ∀ n, v n ≠ 0) (n : ℕ) :
    edge (v n) * eigenvector v (n + 1) = eigenvector v n := by
  rw [eigenvector, Finset.prod_range_succ, mul_inv_rev, ← mul_assoc,
    mul_inv_cancel₀ (edge_ne_zero (v n) (hv n)), one_mul]
  rfl

/-- The combined shift with transcendental scalar coefficients fixes a nonzero
vector. This is not a scalar combination over the ground field `k`.
@isnad1 id=eq.1h2v.s11.96127bc771f8 from=translated src=- shape=77e07754 vocab=4ec15113
-/
theorem combined_shift_eigenvector (v : ℕ → Triple k) (hv : ∀ n, v n ≠ 0) :
    (backShift v 0 + (RatFunc.X : RatFunc k) • backShift v 1 +
      (RatFunc.X : RatFunc k) ^ 2 • backShift v 2 : End (RatFunc k)) (eigenvector v) =
      eigenvector v := by
  ext n
  change algebraMap k (RatFunc k) (v n 0) * eigenvector v (n + 1) +
      RatFunc.X * (algebraMap k (RatFunc k) (v n 1) * eigenvector v (n + 1)) +
      RatFunc.X ^ 2 * (algebraMap k (RatFunc k) (v n 2) * eigenvector v (n + 1)) = _
  calc
    _ = edge (v n) * eigenvector v (n + 1) := by rw [edge_eq]; ring
    _ = eigenvector v n := edge_mul_eigenvector_succ v hv n

end ShiftWitness
end KoetheCounterexample

end
