import Tengoku
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.CoeffExtraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
**Proposition `prop:content-bounds`** (unconditional content bounds), upper
half: the coefficient of `X_1^{n+k-2}X_2` in `C_{n+k} - C_n C_k` is exactly
`nk`, computed for the permutation-native `Cperm`/`CpermPair`.
-/

namespace CongruenceTheory

open Equiv Equiv.Perm MvPolynomial Nat

open scoped Classical

/-- The permutation-native cycle-index sum on the disjoint-union domain `Fin n ⊕ Fin k`
(possibly unequal sizes).-/
noncomputable def CpermPair (n k : ℕ) : MvPolynomial ℕ ℤ :=
  ∑ g : Equiv.Perm (Fin n ⊕ Fin k), ci g

/-- Additivity of `ciExp` under multiset addition.
@isnad1 id=eq.0h4v.s6.2fd1d7ebc5c3 from=translated src=- shape=00962bba vocab=0b4c344c
-/
lemma ciExp_add (a a' : ℕ) (m m' : Multiset ℕ) :
    ciExp a m + ciExp a' m' = ciExp (a + a') (m + m') := by
  ext j
  simp only [Finsupp.add_apply, ciExp_apply, Multiset.count_add]
  by_cases hj : j = 1 <;> simp [hj] <;> omega

/-- A multiset sum of two multisets equals a singleton iff exactly one summand is that
singleton and the other is empty.
@isnad1 id=iff.0h3v.s6.d4c461a5a9ae from=translated src=- shape=0ec993be vocab=d1ac662a
-/
lemma multiset_add_eq_singleton_iff {A B : Multiset ℕ} {x : ℕ} :
    A + B = {x} ↔ (A = {x} ∧ B = 0) ∨ (A = 0 ∧ B = {x}) := by
  constructor
  · intro h
    have hcard : Multiset.card A + Multiset.card B = 1 := by
      rw [← Multiset.card_add, h]; simp
    have hcase : Multiset.card A = 0 ∨ Multiset.card A = 1 := by omega
    rcases hcase with hA | hA
    · right
      have hA0 : A = 0 := Multiset.card_eq_zero.mp hA
      refine ⟨hA0, ?_⟩
      rw [hA0, zero_add] at h
      exact h
    · left
      obtain ⟨a, hAa⟩ := Multiset.card_eq_one.mp hA
      have hB0 : B = 0 := Multiset.card_eq_zero.mp (by omega)
      rw [hAa, hB0, add_zero] at h
      have hax : a = x := Multiset.mem_singleton.mp (h ▸ Multiset.mem_singleton_self a)
      rw [hAa, hax]
      exact ⟨rfl, hB0⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp

/-- The indicator (as a `Finset.card`) of cycle type `{2}` inside `Perm (Fin n)`, i.e.
`C(n,2)` for `n ≥ 2` and `0` otherwise.-/
noncomputable def twoCycleCount (n : ℕ) : ℤ :=
  ((Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.cycleType = {2})).card : ℤ)

/--
@isnad1 id=eq.0h1v.s6.bf3a1e09869b from=translated src=- shape=7044580a vocab=46921b02
-/
lemma card_cycleType_zero (N : ℕ) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => σ.cycleType = (0 : Multiset ℕ))).card
      = 1 := by
  have : (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => σ.cycleType = (0 : Multiset ℕ))) =
      {1} := by
    ext σ
    simp [Equiv.Perm.cycleType_eq_zero]
  rw [this]; simp

/-- **`ci_eq_monomial`, general ambient type version.**
@isnad1 id=eq.0h2v.s7.651dc9980871 from=translated src=- shape=0d694765 vocab=8657ff40
-/
lemma ci_eq_monomial' {α : Type*} [Fintype α] [DecidableEq α] (g : Equiv.Perm α) :
    ci g = MvPolynomial.monomial (ciExp (Fintype.card α - g.cycleType.sum) g.cycleType)
      (1 : ℤ) := by
  unfold ci
  rw [pow_mul_multisetProd_eq_monomial]

/-- The number of `2`-cycles (transpositions) among `Perm α` equals `C(N,2)` where
`N = Fintype.card α`.
@isnad1 id=eq.0h1v.s6.1ab38677fcae from=translated src=- shape=88c65e0f vocab=cf7ade5e
-/
theorem card_twoCycle_eq_choose {α : Type*} [Fintype α] [DecidableEq α] :
    (Finset.univ.filter (fun g : Equiv.Perm α => g.cycleType = ({2} : Multiset ℕ))).card =
      (Fintype.card α).choose 2 := by
  have hcard := Equiv.Perm.card_of_cycleType α ({2} : Multiset ℕ)
  rw [show (Finset.univ.filter (fun σ : Equiv.Perm α => σ.cycleType = {2})) =
      ({g : Equiv.Perm α | g.cycleType = {2}} : Finset (Equiv.Perm α)) from rfl,
    hcard]
  by_cases hN : 2 ≤ Fintype.card α
  · rw [ite_eq_left (by simp [hN]), Nat.choose_eq_factorial_div_factorial hN]
    simp only [Multiset.sum_singleton, Multiset.prod_singleton, Multiset.toFinset_singleton,
      Finset.prod_singleton, Multiset.count_singleton_self, Nat.factorial_one]
    have hdenom : (Fintype.card α - 2)! * 2 * 1 = (2 : ℕ)! * (Fintype.card α - 2)! := by
      norm_num [Nat.factorial]
      ring
    rw [hdenom]
  · rw [ite_eq_right (by simp [hN]), Nat.choose_eq_zero_of_lt (by omega)]

/--
@isnad1 id=eq.0h1v.s6.d407e97ca95a from=translated src=- shape=6997d080 vocab=7607000f
-/
theorem two_mul_card_twoCycle {α : Type*} [Fintype α] [DecidableEq α] :
    2 * ((Finset.univ.filter (fun g : Equiv.Perm α => g.cycleType = ({2} : Multiset ℕ))).card :
      ℤ) = (Fintype.card α : ℤ) * ((Fintype.card α : ℤ) - 1) := by
  rw [card_twoCycle_eq_choose]
  have heq2 : 2 * ((Fintype.card α).choose 2) = (Fintype.card α) * (Fintype.card α - 1) := by
    rw [Nat.choose_two_right, mul_comm 2,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (Fintype.card α))]
  have hcast : (2 : ℤ) * ((Fintype.card α).choose 2 : ℤ) =
      ((Fintype.card α) * (Fintype.card α - 1) : ℕ) := by exact_mod_cast heq2
  rw [hcast]
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h | h
  · simp [h]
  · push_cast [Nat.cast_sub h]
    ring

/--
@isnad1 id=eq.0h1v.s5.22dead549dab from=translated src=- shape=54c3d2ae vocab=f23a3346
-/
theorem two_mul_twoCycleCount (N : ℕ) : 2 * twoCycleCount N = (N : ℤ) * ((N : ℤ) - 1) := by
  have h := two_mul_card_twoCycle (α := Fin N)
  rw [Fintype.card_fin] at h
  rw [show twoCycleCount N = ((Finset.univ.filter
      (fun g : Equiv.Perm (Fin N) => g.cycleType = ({2} : Multiset ℕ))).card : ℤ) from rfl]
  exact h

end CongruenceTheory
