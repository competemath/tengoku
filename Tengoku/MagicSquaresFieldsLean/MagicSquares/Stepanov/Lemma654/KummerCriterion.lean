import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma654.SimpleRoot
import Tengoku.Seed.FieldTheory.KummerExtension
import Tengoku.Seed.FieldTheory.RatFunc.AsPolynomial
import Tengoku.Seed.RingTheory.Polynomial.GaussLemma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open Polynomial IntermediateField

/-- Over a field containing a root of `-1` of every positive order,
the usual prime-power obstruction is the complete Kummer irreducibility
criterion. This includes rational functions over algebraically closed
constant fields and handles even exponents as well as odd exponents.-/
theorem X_pow_sub_C_irreducible_of_roots_neg_one
    {K : Type*} [Field K] {m : ℕ} (hm : 0 < m)
    (hneg : ∀ n : ℕ, 0 < n → ∃ u : K, u ^ n = -1)
    {a : K} (ha : ∀ p : ℕ, p.Prime → p ∣ m → ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ m - C a) := by
  induction m using induction_on_primes generalizing K a with
  | zero => omega
  | one => simpa using irreducible_X_sub_C a
  | prime_mul p m hp ih =>
    rw [mul_comm]
    apply X_pow_mul_sub_C_irreducible
      (X_pow_sub_C_irreducible_of_prime hp (ha p hp (dvd_mul_right _ _)))
    intro E _ _ x hx
    have hxi : IsIntegral K x := by
      by_contra h
      have he := hx.symm.trans (minpoly.eq_zero h)
      exact (X_pow_sub_C_ne_zero hp.pos a) he
    apply ih (Nat.pos_of_ne_zero (by intro hz; simp [hz] at hm))
    · intro n hn
      obtain ⟨u, hu⟩ := hneg n hn
      refine ⟨algebraMap K K⟮x⟯ u, ?_⟩
      rw [← map_pow, hu, map_neg, map_one]
    · intro q hq hqm b hb
      by_cases hp2 : p = 2
      · obtain ⟨u, hu⟩ := hneg q hq.pos
        apply ha q hq (dvd_mul_of_dvd_right hqm p) (u * Algebra.norm K b)
        rw [mul_pow, hu, ← map_pow, hb, ← adjoin.powerBasis_gen hxi,
          Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
        simp [minpoly_gen, hx, hp2, adjoin.powerBasis_dim]
      · apply ha q hq (dvd_mul_of_dvd_right hqm p) (Algebra.norm K b)
        rw [← map_pow, hb, ← adjoin.powerBasis_gen hxi,
          Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
        simp [minpoly_gen, hx, hp.ne_zero.symm, (hp.odd_of_ne_two hp2).neg_pow,
          adjoin.powerBasis_dim]

variable {F : Type*} [Field F]

/-- Root multiplicity is multiplied by a positive polynomial power.-/
theorem rootMultiplicity_pow_of_ne_zero (f : Polynomial F) (hf : f ≠ 0) (a : F) (n : ℕ) :
    (f ^ n).rootMultiplicity a = n * f.rootMultiplicity a := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, rootMultiplicity_mul (mul_ne_zero (pow_ne_zero n hf) hf), ih]
    ring

/-- A rational-function power can only have root multiplicities divisible
by its exponent, even when its expression initially has a denominator.-/
theorem dvd_rootMultiplicity_of_ratFunc_pow
    {f : Polynomial F} (hf : f ≠ 0) {n : ℕ} (hn : 0 < n)
    (b : RatFunc F) (hb : b ^ n = algebraMap (Polynomial F) (RatFunc F) f) (a : F) :
    n ∣ f.rootMultiplicity a := by
  let phi := algebraMap (Polynomial F) (RatFunc F)
  have hd : phi b.denom ≠ 0 := by
    exact IsFractionRing.to_map_eq_zero_iff.not.mpr b.denom_ne_zero
  have he : b.num ^ n = f * b.denom ^ n := by
    apply IsFractionRing.injective (Polynomial F) (RatFunc F)
    have hh := hb
    rw [← RatFunc.num_div_denom b, div_pow] at hh
    have hc := (div_eq_iff (pow_ne_zero n hd)).mp hh
    simpa only [map_pow, map_mul, phi] using hc
  have hnum : b.num ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.ne_of_gt hn)] at he
    exact (mul_ne_zero hf (pow_ne_zero n b.denom_ne_zero)) he.symm
  have hmult := congrArg (fun g : Polynomial F => g.rootMultiplicity a) he
  rw [rootMultiplicity_pow_of_ne_zero _ hnum,
    rootMultiplicity_mul (mul_ne_zero hf (pow_ne_zero n b.denom_ne_zero)),
    rootMultiplicity_pow_of_ne_zero _ b.denom_ne_zero] at hmult
  exact (Nat.dvd_add_iff_left (dvd_mul_right n _)).mpr
    (hmult ▸ dvd_mul_right n (b.num.rootMultiplicity a))

/-- The sufficient direction of LN97 Lemma 6.54, stated by prime divisors
of the Kummer exponent. The root witnessing nondivisibility may differ
for different prime divisors.-/
theorem kummer_irreducible_of_root_multiplicities [IsAlgClosed F]
    {m : ℕ} (hm : 0 < m) (f : Polynomial F) (hf : f ≠ 0)
    (hroot : ∀ p : ℕ, p.Prime → p ∣ m → ∃ a : F, ¬ p ∣ f.rootMultiplicity a) :
    Irreducible (kummerPolynomial m f) := by
  apply (kummerPolynomial_monic hm f).irreducible_iff_irreducible_map_fraction_map
    (K := RatFunc F) |>.mpr
  simp only [kummerPolynomial, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  apply X_pow_sub_C_irreducible_of_roots_neg_one hm
  · intro n hn
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : F) hn
    refine ⟨algebraMap F (RatFunc F) u, ?_⟩
    rw [← map_pow, hu, map_neg, map_one]
  · intro p hp hpm b hb
    obtain ⟨a, ha⟩ := hroot p hp hpm
    exact ha (dvd_rootMultiplicity_of_ratFunc_pow hf hp.pos b hb a)

/-- Root multiplicities computed in the base field also establish
absolute irreducibility over its algebraic closure.-/
theorem kummerAbsolutelyIrreducible_of_root_multiplicities
    {m : ℕ} (hm : 0 < m) (f : Polynomial F) (hf : f ≠ 0)
    (hroot : ∀ p : ℕ, p.Prime → p ∣ m → ∃ a : F, ¬ p ∣ f.rootMultiplicity a) :
    KummerAbsolutelyIrreducible m f := by
  apply kummer_irreducible_of_root_multiplicities hm _ (Polynomial.map_ne_zero hf)
  intro p hp hpm
  obtain ⟨a, ha⟩ := hroot p hp hpm
  refine ⟨algebraMap F (AlgebraicClosure F) a, ?_⟩
  rwa [← eq_rootMultiplicity_map (algebraMap F (AlgebraicClosure F)).injective a]

/-- Exact multiplicities in a product of distinct linear factors with
arbitrary natural exponents.-/
theorem rootMultiplicity_prod_distinct_linear_powers
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (roots : ι → F) (exponents : ι → ℕ)
    (hinj : Set.InjOn roots s) {j : ι} (hj : j ∈ s) :
    (∏ i ∈ s, (X - C (roots i)) ^ exponents i).rootMultiplicity (roots j) = exponents j := by
  classical
  have hrest : (∏ i ∈ s.erase j, (X - C (roots i)) ^ exponents i).eval (roots j) ≠ 0 := by
    rw [Polynomial.eval_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    rw [Polynomial.eval_pow]
    apply pow_ne_zero
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero]
    intro heq
    exact (Finset.mem_erase.mp hi).1 (hinj (Finset.mem_erase.mp hi).2 hj heq.symm)
  have hrest0 : (∏ i ∈ s.erase j, (X - C (roots i)) ^ exponents i) ≠ 0 := by
    intro hz
    simp [hz] at hrest
  rw [← Finset.prod_erase_mul s (fun i => (X - C (roots i)) ^ exponents i) hj,
    rootMultiplicity_mul (mul_ne_zero hrest0 (pow_ne_zero _ (X_sub_C_ne_zero _))),
    rootMultiplicity_eq_zero hrest, rootMultiplicity_X_sub_C_pow, zero_add]

/-- The split multiplicity criterion in a form suited to the character
sum proof. No prime divisor of `m` may divide every root multiplicity.-/
theorem kummerAbsolutelyIrreducible_prod_distinct_linear_powers
    {m r : ℕ} (hm : 0 < m) (roots : Fin r → F) (hinj : Function.Injective roots)
    (exponents : Fin r → ℕ)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ m → ∃ i, ¬ p ∣ exponents i) :
    KummerAbsolutelyIrreducible m (∏ i, (X - C (roots i)) ^ exponents i) := by
  apply kummerAbsolutelyIrreducible_of_root_multiplicities hm
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (X_sub_C_ne_zero _)
  · intro p hp hpm
    obtain ⟨i, hi⟩ := hprime p hp hpm
    refine ⟨roots i, ?_⟩
    rwa [rootMultiplicity_prod_distinct_linear_powers Finset.univ roots exponents
      (fun _ _ _ _ h => hinj h) (Finset.mem_univ i)]

/-- Multiplying the right side of a Kummer equation by a nonzero constant
preserves absolute irreducibility.-/
theorem KummerAbsolutelyIrreducible.const_mul
    {m : ℕ} (hm : 0 < m) {f : Polynomial F} (hirr : KummerAbsolutelyIrreducible m f)
    {c : F} (hc : c ≠ 0) : KummerAbsolutelyIrreducible m (C c * f) := by
  let phi := algebraMap F (AlgebraicClosure F)
  have h := kummer_irreducible_normalize_of_isAlgClosed hm (f.map phi)
    (phi c)⁻¹ (inv_ne_zero ((map_ne_zero phi).mpr hc)) hirr
  simpa only [KummerAbsolutelyIrreducible, Polynomial.map_mul, Polynomial.map_C,
    inv_inv, phi] using h

end MagicSquares.LN97
