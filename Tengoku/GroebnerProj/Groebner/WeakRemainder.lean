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

/--
@isnad1 id=monotone.0h2v.s7.13142974b66c from=translated src=- shape=2f6f2abf vocab=453f4539
-/
lemma toWithBotSyn_monotone : Monotone m.toWithBotSyn := by
  simp [toWithBotSyn, toSyn_monotone]

/--
@isnad1 id=le.0h4v.s6.029386e78f9a from=translated src=- shape=4b00d616 vocab=6e739dea
-/
lemma withBotDegree_le_coe_degree {R} [CommSemiring R] (f : MvPolynomial σ R) :
    m.withBotDegree f ≤ m.degree f := by
  by_cases hf : f = 0
  · simp [hf]
  simp [m.withBotDegree_eq_coe_degree_iff f |>.mpr hf]

/--
@isnad1 id=not.1h5v.s8.0b1d6c7eed1f from=translated src=- shape=ffc7305a vocab=8cd5c6be
-/
lemma notMem_support_of_degree_lt' {a} {f : MvPolynomial σ R} (h : m.degree f ≺[m] a) :
    a ∉ f.support := by
  simp [coeff_eq_zero_of_lt h]

end MonomialOrder
