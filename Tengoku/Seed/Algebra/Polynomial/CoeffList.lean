/-
Copyright (c) 2023 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Polynomial.Degree.Defs
public import Tengoku.Seed.Algebra.Polynomial.EraseLead
public import Tengoku.Seed.Data.List.Range

/-!
# A list of coefficients of a polynomial

## Definition

* `coeffList f`: a `List` of the coefficients, from leading term down to constant term.
* `coeffList 0` is defined to be `[]`.

This is useful for talking about polynomials in terms of list operations. It is "redundant" data in
the sense that `Polynomial` is already a `Finsupp` (of its coefficients), and `Polynomial.coeff`
turns this into a function, and these have exactly the same data as `coeffList`. The difference is
that `coeffList` is intended for working together with list operations: getting `List.head`,
comparing adjacent coefficients with each other, or anything that involves induction on Polynomials
by dropping the leading term (which is `Polynomial.eraseLead`).

Note that `coeffList` _starts_ with the highest-degree terms and _ends_ with the constant term. This
might seem backwards in the sense that `Polynomial.coeff` and `List.get!` are reversed to one
another, but it means that induction on `List`s is the same as induction on
`Polynomial.leadingCoeff`.

The most significant theorem here is `coeffList_eraseLead`, which says that `coeffList P` can be
written as `leadingCoeff P :: List.replicate k 0 ++ coeffList P.eraseLead`. That is, the list
of coefficients starts with the leading coefficient, followed by some number of zeros, and then the
coefficients of `P.eraseLead`.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- The list of coefficients starting from the leading term down to the constant term. -/
def coeffList (P : R[X]) : List R :=
  (List.range P.degree.succ).reverse.map P.coeff

variable {P : R[X]}

variable (R) in
/--
@isnad1 id=eq.0h1v.s4.6aaa995973e6 from=seed src=0 shape=a0696bc9 vocab=ddd2cc30
-/
@[simp]
theorem coeffList_zero : (0 : R[X]).coeffList = [] := by
  simp [coeffList]

/-- Only the zero polynomial has no coefficients.
@isnad1 id=iff.0h2v.s5.04afcf133f0e from=seed src=0 shape=b148e36b vocab=ddd2cc30
-/
@[simp]
theorem coeffList_eq_nil {P : R[X]} : P.coeffList = [] ↔ P = 0 := by
  simp [coeffList]

/--
@isnad1 id=eq.1h2v.s6.b8aed7782889 from=seed src=0 shape=9fc2a327 vocab=9d3c5793
-/
@[simp]
theorem coeffList_C {x : R} (h : x ≠ 0) : (C x).coeffList = [x] := by
  simp [coeffList, List.range_succ, degree_eq_natDegree (C_ne_zero.mpr h)]

/--
@isnad1 id=ex.1h2v.s5.024f55dc3ce7 from=seed src=0 shape=4012429e vocab=c17fc143
-/
theorem coeffList_eq_cons_leadingCoeff (h : P ≠ 0) :
    ∃ ls, P.coeffList = P.leadingCoeff :: ls := by
  simp [coeffList, List.range_succ, withBotSucc_degree_eq_natDegree_add_one h]

/--
@isnad1 id=eq.1h2v.s5.9c4cbd85e04e from=seed src=0 shape=5cb05c71 vocab=66cdd3d8
-/
@[simp]
theorem head?_coeffList (h : P ≠ 0) :
    P.coeffList.head? = P.leadingCoeff :=
  (coeffList_eq_cons_leadingCoeff h).casesOn fun _ ↦ (Eq.symm · ▸ rfl)

/--
@isnad1 id=eq.1h2v.s5.c3d3c6e574ca from=seed src=0 shape=401848fd vocab=9d11e286
-/
@[simp] theorem head_coeffList (P : R[X]) (hP) :
    P.coeffList.head hP = P.leadingCoeff :=
  let h := coeffList_eq_nil.not.mp hP
  (coeffList_eq_cons_leadingCoeff h).casesOn fun _ _ ↦
    Option.some.injEq _ _ ▸ List.head?_eq_some_head _ ▸ head?_coeffList h

/--
@isnad1 id=eq.0h2v.s4.719868bad618 from=seed src=0 shape=5ae7a428 vocab=d59020df
-/
theorem length_coeffList_eq_withBotSucc_degree (P : R[X]) : P.coeffList.length = P.degree.succ := by
  simp [coeffList]

/--
@isnad1 id=eq.0h2v.s6.04c4c4a5f166 from=seed src=0 shape=62a67e3f vocab=a31e19ef
-/
@[simp]
theorem length_coeffList_eq_ite [DecidableEq R] (P : R[X]) :
    P.coeffList.length = if P = 0 then 0 else P.natDegree + 1 := by
  by_cases h : P = 0 <;> simp [h, coeffList, withBotSucc_degree_eq_natDegree_add_one]

/--
@isnad1 id=eq.1h2v.s5.1dfedc8c3740 from=seed src=0 shape=d4b760d6 vocab=e844c84f
-/
theorem leadingCoeff_cons_eraseLead (h : P.nextCoeff ≠ 0) :
    P.leadingCoeff :: P.eraseLead.coeffList = P.coeffList := by
  have h₂ := ne_zero_of_natDegree_gt (natDegree_pos_of_nextCoeff_ne_zero h)
  have h₃ := mt nextCoeff_eq_zero_of_eraseLead_eq_zero h
  simpa [natDegree_eraseLead_add_one h, coeffList, withBotSucc_degree_eq_natDegree_add_one h₂,
    withBotSucc_degree_eq_natDegree_add_one h₃, List.range_succ] using
    (Polynomial.eraseLead_coeff_of_ne · ·.ne)

/--
@isnad1 id=eq.1h3v.s6.87cf10310c48 from=seed src=0 shape=8eae19be vocab=342ef77d
-/
@[simp]
theorem coeffList_monomial {x : R} (hx : x ≠ 0) (n : ℕ) :
    (monomial n x).coeffList = x :: List.replicate n 0 := by
  have h := mt (Polynomial.monomial_eq_zero_iff x n).mp hx
  apply List.ext_get (by classical simp [hx])
  rintro (_ | k) _ h₁
  · exact (coeffList_eq_cons_leadingCoeff h).rec (by simp_all)
  · rw [List.length_cons, List.length_replicate] at h₁
    have : ((monomial n) x).natDegree.succ = n + 1 := by
      simp [Polynomial.natDegree_monomial_eq n hx]
    simpa [coeffList, withBotSucc_degree_eq_natDegree_add_one h]
      using Polynomial.coeff_monomial_of_ne _ (by lia)

/-- Coefficients of a polynomial `P` are always the leading coefficient, some number of zeros, and
then `coeffList P.eraseLead`.
@isnad1 id=eq.1h2v.s6.ae9097ed01a2 from=seed src=0 shape=41cdada5 vocab=23124a92
-/
theorem coeffList_eraseLead (h : P ≠ 0) :
    P.coeffList =
      P.leadingCoeff :: (.replicate (P.natDegree - P.eraseLead.degree.succ) 0
        ++ P.eraseLead.coeffList) := by
  by_cases hdp : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hdp] at h ⊢
    simp [coeffList_C (C_ne_zero.mp h)]
  by_cases hep : P.eraseLead = 0
  · have h₂ : .monomial P.natDegree P.leadingCoeff = P := by
      simpa [hep] using P.eraseLead_add_monomial_natDegree_leadingCoeff
    nth_rewrite 1 [← h₂]
    simp [coeffList_monomial (Polynomial.leadingCoeff_ne_zero.mpr h), hep]
  have h₁ := withBotSucc_degree_eq_natDegree_add_one h
  have h₂ := withBotSucc_degree_eq_natDegree_add_one hep
  obtain ⟨n, hn, hn2⟩ : ∃ d, P.natDegree = P.eraseLead.natDegree + 1 + d ∧
      d = P.natDegree - P.eraseLead.degree.succ := by
    use P.natDegree - P.eraseLead.natDegree - 1
    have := eraseLead_natDegree_le P
    lia
  rw [← hn2]; clear hn2
  apply List.ext_getElem?
  rintro (_ | k)
  · obtain ⟨w, h⟩ := (coeffList_eq_cons_leadingCoeff h)
    simp_all
  simp only [coeffList, List.map_reverse]
  by_cases! hkd : P.natDegree + 1 ≤ k + 1
  · rw [List.getElem?_eq_none]
      <;> simp <;> lia
  obtain ⟨dk, hdk⟩ := exists_add_of_le (Nat.le_of_lt_succ hkd)
  rw [List.getElem?_reverse (by simpa [withBotSucc_degree_eq_natDegree_add_one h] using hkd),
    List.getElem?_cons_succ, List.length_map, List.length_range, List.getElem?_map,
    List.getElem?_range (by lia), Option.map_some]
  conv_lhs => arg 1; equals P.eraseLead.coeff dk =>
    rw [eraseLead_coeff_of_ne (f := P) dk (by lia)]
    congr
    lia
  by_cases! hkn : k < n
  · simpa [List.getElem?_append, hkn] using coeff_eq_zero_of_natDegree_lt (by lia)
  · rw [List.getElem?_append_right (List.length_replicate ▸ hkn),
      List.length_replicate, List.getElem?_reverse, List.getElem?_map]
    · rw [List.length_map, List.length_range,
        List.getElem?_range (by lia), Option.map_some]
      congr 2
      lia
    · simp
      lia

end Semiring

section Ring

variable [Ring R] (P : R[X])

/--
@isnad1 id=eq.0h2v.s5.df8769b628b6 from=seed src=0 shape=f890d398 vocab=b10c8a24
-/
@[simp]
theorem coeffList_neg : (-P).coeffList = P.coeffList.map (-·) := by
  by_cases hp : P = 0
  · rw [hp, coeffList_zero, neg_zero, coeffList_zero, List.map_nil]
  · simp [coeffList]

end Ring

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R] (P : R[X])

/--
@isnad1 id=eq.1h3v.s6.adde19463db2 from=seed src=0 shape=20c78cf7 vocab=9c1b23c7
-/
theorem coeffList_C_mul {x : R} (hx : x ≠ 0) : (C x * P).coeffList = P.coeffList.map (x * ·) := by
  by_cases hp : P = 0
  · simp [hp]
  · simp [coeffList, Polynomial.degree_C hx]

end NoZeroDivisors
end Polynomial
