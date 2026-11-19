import Tengoku
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.Perm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
A coefficient-extraction bridge: relating `MvPolynomial.coeff` of the
cycle-index sum `Cperm N = ∑ g, ci g` to the count of permutations of a
given cycle type. Needed for `prop:content-bounds` and beyond, since
`thm:strong`'s proof never needed to extract an individual coefficient
(it only ever summed whole `H`-orbits).
-/

namespace CongruenceTheory

open Equiv Equiv.Perm MvPolynomial

open scoped Classical

/-- The exponent vector of the cycle-indicator monomial for `a` fixed points and a
multiset `m` of (non-trivial) cycle lengths.-/
noncomputable def ciExp (a : ℕ) (m : Multiset ℕ) : ℕ →₀ ℕ :=
  Finsupp.single 1 a + (m.map (fun j => Finsupp.single j 1)).sum

lemma ciExp_apply (a : ℕ) (m : Multiset ℕ) (j : ℕ) :
    ciExp a m j = (if j = 1 then a else 0) + m.count j := by
  induction m using Multiset.induction with
  | empty =>
    have key0 : ciExp a (0 : Multiset ℕ) j = (if j = 1 then a else 0) := by
      simp only [ciExp, Multiset.map_zero, Multiset.sum_zero, add_zero, Finsupp.single_apply]
      by_cases hj1 : j = 1 <;> simp [hj1, eq_comm]
    rw [key0]; simp
  | cons x s ih =>
    have key : ciExp a (x ::ₘ s) j = ciExp a s j + (if j = x then 1 else 0) := by
      simp only [ciExp, Multiset.map_cons, Multiset.sum_cons, Finsupp.add_apply,
        Finsupp.single_apply]
      by_cases hjx : j = x <;> simp [hjx, eq_comm] <;> ring
    rw [key, ih, Multiset.count_cons]
    by_cases hj1 : j = 1 <;> by_cases hjx : j = x <;> simp [hj1, hjx] <;> omega

/-- `X_1^a * ∏_{ℓ ∈ m} X_ℓ = monomial (ciExp a m) 1`.-/
lemma pow_mul_multisetProd_eq_monomial (a : ℕ) (m : Multiset ℕ) :
    (MvPolynomial.X 1 : MvPolynomial ℕ ℤ) ^ a * (m.map MvPolynomial.X).prod =
      MvPolynomial.monomial (ciExp a m) (1 : ℤ) := by
  induction m using Multiset.induction with
  | empty => simp [ciExp, MvPolynomial.X_pow_eq_monomial]
  | cons j s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ← mul_assoc,
      mul_comm ((MvPolynomial.X 1 : MvPolynomial ℕ ℤ) ^ a) (MvPolynomial.X j), mul_assoc, ih]
    rw [show (MvPolynomial.X j : MvPolynomial ℕ ℤ) = MvPolynomial.monomial (Finsupp.single j 1) 1
      from by rw [← pow_one (MvPolynomial.X j : MvPolynomial ℕ ℤ), MvPolynomial.X_pow_eq_monomial]]
    rw [MvPolynomial.monomial_mul_monomial, one_mul]
    congr 1
    simp only [ciExp, Multiset.map_cons, Multiset.sum_cons]
    abel

/-- `ci g` is the cycle-indicator monomial for `g`.-/
lemma ci_eq_monomial {N : ℕ} (g : Equiv.Perm (Fin N)) :
    ci g = MvPolynomial.monomial (ciExp (N - g.cycleType.sum) g.cycleType) (1 : ℤ) := by
  unfold ci
  rw [pow_mul_multisetProd_eq_monomial]
  simp

/-- Injectivity of `ciExp` on pairs `(a, m)` with `m` having no length-`1` parts.-/
lemma ciExp_eq_iff {a a' : ℕ} {m m' : Multiset ℕ} (hm : ∀ x ∈ m, x ≠ 1)
    (hm' : ∀ x ∈ m', x ≠ 1) : ciExp a m = ciExp a' m' ↔ a = a' ∧ m = m' := by
  constructor
  · intro h
    have hj : ∀ j, ciExp a m j = ciExp a' m' j := fun j => DFunLike.congr_fun h j
    have hm_eq : m = m' := by
      apply Multiset.ext.mpr
      intro j
      have hje := hj j
      rw [ciExp_apply, ciExp_apply] at hje
      rcases eq_or_ne j 1 with hj1 | hj1
      · subst hj1
        have hcm : m.count 1 = 0 := Multiset.count_eq_zero.mpr (fun hc => hm 1 hc rfl)
        have hcm' : m'.count 1 = 0 := Multiset.count_eq_zero.mpr (fun hc => hm' 1 hc rfl)
        omega
      · simpa [hj1] using hje
    refine ⟨?_, hm_eq⟩
    have hje := hj 1
    rw [ciExp_apply, ciExp_apply] at hje
    have hcm : m.count 1 = 0 := Multiset.count_eq_zero.mpr (fun hc => hm 1 hc rfl)
    have hcm' : m'.count 1 = 0 := Multiset.count_eq_zero.mpr (fun hc => hm' 1 hc rfl)
    simp only [hcm, hcm', reduceIte, add_zero] at hje
    exact hje
  · rintro ⟨rfl, rfl⟩; rfl

end CongruenceTheory
