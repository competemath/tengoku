module

public import Tengoku

/-! # Weak Division

## Reference

- "On the construction of Gröbner bases using syzygies" https://www.sciencedirect.com/science/article/pii/S074771718880052X
-/

@[expose] public section

namespace MonomialOrder

open MvPolynomial

open scoped MonomialOrder

variable {σ : Type*} {m : MonomialOrder σ} {R : Type*} [CommRing R]

lemma toWithBotSyn_monotone : Monotone m.toWithBotSyn := by
  simp [toWithBotSyn, toSyn_monotone]

lemma withBotDegree_le_coe_degree {R} [CommSemiring R] (f : MvPolynomial σ R) :
    m.withBotDegree f ≤ m.degree f := by
  by_cases hf : f = 0
  · simp [hf]
  simp [m.withBotDegree_eq_coe_degree_iff f |>.mpr hf]

lemma notMem_support_of_degree_lt' {a} {f : MvPolynomial σ R} (h : m.degree f ≺[m] a) :
    a ∉ f.support := by
  simp [coeff_eq_zero_of_lt h]

end MonomialOrder
