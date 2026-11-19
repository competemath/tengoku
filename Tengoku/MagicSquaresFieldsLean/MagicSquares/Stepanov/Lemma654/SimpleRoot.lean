import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.AbsoluteIrreducibility
import Tengoku.Seed.RingTheory.Polynomial.Eisenstein.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open Polynomial

variable {F : Type*} [Field F]

/-- A simple root makes `Y^m - f(X)` Eisenstein at the corresponding
linear prime in `F[X]`. This works in every characteristic.
@isnad1 id=irreduci.2h4v.s6.78cf772f00ad from=translated src=- shape=b8dc7b8f vocab=c73003d9
-/
theorem kummerPolynomial_irreducible_of_simple_root
    {m : ℕ} (hm : 0 < m) {f : Polynomial F} {a : F}
    (ha : f.rootMultiplicity a = 1) : Irreducible (kummerPolynomial m f) := by
  have hf : f ≠ 0 := by
    intro h
    simp [h] at ha
  let P : Ideal (Polynomial F) := Ideal.span {X - C a}
  have hP : P.IsPrime :=
    (Ideal.span_singleton_prime (X_sub_C_ne_zero a)).mpr (prime_X_sub_C a)
  have hmonic := kummerPolynomial_monic hm f
  have hdeg : (kummerPolynomial m f).natDegree = m := natDegree_X_pow_sub_C
  have hdiv : X - C a ∣ f := by
    simpa using (le_rootMultiplicity_iff hf).mp (show 1 ≤ f.rootMultiplicity a by omega)
  have hnotdiv : ¬ (X - C a) ^ 2 ∣ f := by
    rw [← le_rootMultiplicity_iff hf, ha]
    omega
  have he : (kummerPolynomial m f).IsEisensteinAt P := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hmonic.leadingCoeff]
      intro hmem
      exact hP.ne_top (Ideal.eq_top_of_isUnit_mem P hmem isUnit_one)
    · intro n hn
      rw [hdeg] at hn
      change (X ^ m - C f).coeff n ∈ P
      rw [coeff_sub, coeff_X_pow, coeff_C]
      have hnm : n ≠ m := Nat.ne_of_lt hn
      simp only [hnm, ite_false, zero_sub]
      by_cases hn0 : n = 0
      · simp only [hn0, ite_true]
        exact Ideal.mem_span_singleton.mpr (dvd_neg.mpr hdiv)
      · simp only [hn0, ite_false, neg_zero]
        exact P.zero_mem
    · change (X ^ m - C f).coeff 0 ∉ P ^ 2
      rw [coeff_sub, coeff_X_pow, coeff_C]
      simp only [Ne.symm (Nat.ne_of_gt hm), ite_false, ite_true,
        zero_sub]
      simpa only [P, Ideal.span_singleton_pow, Ideal.mem_span_singleton, dvd_neg] using hnotdiv
  exact he.irreducible hP hmonic.isPrimitive (by omega)

/-- The simple-root case of LN97 Lemma 6.54, over the algebraic closure.
It is enough for the split squarefree polynomials in Section 7.
@isnad1 id=kummerab.2h4v.s5.f472ecaa75bc from=translated src=- shape=e3d40ee0 vocab=371c9e5e
-/
theorem kummerAbsolutelyIrreducible_of_simple_root
    {m : ℕ} (hm : 0 < m) {f : Polynomial F} {a : F}
    (ha : f.rootMultiplicity a = 1) : KummerAbsolutelyIrreducible m f := by
  apply kummerPolynomial_irreducible_of_simple_root hm
    (a := algebraMap F (AlgebraicClosure F) a)
  rw [← eq_rootMultiplicity_map (algebraMap F (AlgebraicClosure F)).injective a]
  exact ha

/-- Every factor in a product of distinct linear factors is a simple root.
@isnad1 id=eq.2h5v.s7.55a2fc7a1e2a from=translated src=- shape=c25b9338 vocab=f63d6bbe
-/
theorem rootMultiplicity_prod_distinct_linear
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (roots : ι → F)
    (hinj : Set.InjOn roots s) {j : ι} (hj : j ∈ s) :
    (∏ i ∈ s, (X - C (roots i))).rootMultiplicity (roots j) = 1 := by
  classical
  have hrest : (∏ i ∈ s.erase j, (X - C (roots i))).eval (roots j) ≠ 0 := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
    intro heq
    exact (Finset.mem_erase.mp hi).1 (hinj (Finset.mem_erase.mp hi).2 hj heq.symm)
  have hrest0 : (∏ i ∈ s.erase j, (X - C (roots i))) ≠ 0 := by
    intro hz
    simp [hz] at hrest
  rw [← Finset.prod_erase_mul s (fun i => X - C (roots i)) hj,
    rootMultiplicity_mul (mul_ne_zero hrest0 (X_sub_C_ne_zero _)),
    rootMultiplicity_eq_zero hrest, rootMultiplicity_X_sub_C_self, zero_add]

/-- The split squarefree polynomials used in Section 7 automatically
satisfy the absolute irreducibility hypothesis of Theorem 6.53.
@isnad1 id=kummerab.3h4v.s7.45249aae9120 from=translated src=- shape=a315c4f2 vocab=a6bb5a4b
-/
theorem kummerAbsolutelyIrreducible_prod_distinct_linear
    {m r : ℕ} (hm : 0 < m) (hr : 0 < r) (roots : Fin r → F)
    (hinj : Function.Injective roots) :
    KummerAbsolutelyIrreducible m (∏ i, (X - C (roots i))) := by
  apply kummerAbsolutelyIrreducible_of_simple_root hm (a := roots ⟨0, hr⟩)
  exact rootMultiplicity_prod_distinct_linear Finset.univ roots
    (fun _ _ _ _ h => hinj h) (Finset.mem_univ _)

end MagicSquares.LN97
