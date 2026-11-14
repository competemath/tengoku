import Tengoku.Seed.NumberTheory.LSeries.DirichletContinuation
import Tengoku.Seed.NumberTheory.Harmonic.Bounds
import Tengoku.Seed.Data.Nat.Squarefree

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Values and zeros under character induction

The finite Euler multiplier at one has norm at most `1 + log N`.
The proof expands its elementary majorant over subsets of the distinct
prime factors; their products are distinct integers between one and `N`.
The exact change-of-level identity then bounds the induced value at one
and preserves actual zeros away from the possible principal pole.
-/

noncomputable section

open Finset

namespace TwinPrime.Analytic

/-- The elementary Euler product is bounded by the full harmonic sum.
The empty product for modulus one is included.
@isnad1 id=le.1h1v.s5.97cbc9d435db from=translated src=- shape=8cd792f4 vocab=85ab194b
-/
theorem prod_one_add_inv_primeFactors_le_harmonic (N : ℕ) (hN : 0 < N) :
    (∏ p ∈ N.primeFactors, (1 + (p : ℝ)⁻¹)) ≤ harmonic N := by
  classical
  let P : Finset ℕ → ℕ := fun S => ∏ p ∈ S, p
  have hprime (S : Finset ℕ) (hS : S ∈ N.primeFactors.powerset) :
      ∀ p ∈ S, p.Prime := fun _ hp =>
    Nat.prime_of_mem_primeFactors (mem_powerset.mp hS hp)
  have hinj : Set.InjOn P (↑N.primeFactors.powerset : Set (Finset ℕ)) := by
    intro S hS T hT heq
    have hS' := Nat.primeFactors_prod (hprime S hS)
    have hT' := Nat.primeFactors_prod (hprime T hT)
    change (P S).primeFactors = S at hS'
    change (P T).primeFactors = T at hT'
    rw [heq, hT'] at hS'
    exact hS'.symm
  have hsub : N.primeFactors.powerset.image P ⊆ Icc 1 N := by
    intro n hn
    obtain ⟨S, hS, rfl⟩ := mem_image.mp hn
    have hpos : 0 < P S := prod_pos (fun p hp => (hprime S hS p hp).pos)
    have hdvd : P S ∣ N :=
      (prod_dvd_prod_of_subset S N.primeFactors id (mem_powerset.mp hS)).trans
        (Nat.prod_primeFactors_dvd N)
    exact mem_Icc.mpr ⟨hpos, Nat.le_of_dvd hN hdvd⟩
  calc
    _ = ∑ S ∈ N.primeFactors.powerset, (P S : ℝ)⁻¹ := by
      rw [prod_one_add]
      apply sum_congr rfl
      intro S _
      simp only [P, Nat.cast_prod, prod_inv_distrib]
    _ = ∑ n ∈ N.primeFactors.powerset.image P, (n : ℝ)⁻¹ :=
      (sum_image (f := fun n : ℕ => (n : ℝ)⁻¹) hinj).symm
    _ ≤ ∑ n ∈ Icc 1 N, (n : ℝ)⁻¹ :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = harmonic N := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- The logarithmic bound has constant one and no power of the modulus.
@isnad1 id=le.1h1v.s5.db5a0ce279a0 from=translated src=- shape=af917ad1 vocab=b280eab3
-/
theorem prod_one_add_inv_primeFactors_le_one_add_log (N : ℕ) (hN : 0 < N) :
    (∏ p ∈ N.primeFactors, (1 + (p : ℝ)⁻¹)) ≤ 1 + Real.log N :=
  (prod_one_add_inv_primeFactors_le_harmonic N hN).trans (harmonic_le_one_add_log N)

/-- The actual Euler multiplier at one, for an arbitrary inducing character.
@isnad1 id=le.1h3v.s7.8deaa6b3e109 from=translated src=- shape=c3065d05 vocab=612573fb
-/
theorem norm_characterEulerMultiplier_one_le {M : ℕ} (χ : DirichletCharacter ℂ M)
    (N : ℕ) (hN : 0 < N) :
    ‖∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-(1 : ℂ)))‖ ≤
      1 + Real.log N := by
  rw [norm_prod]
  apply (prod_le_prod (fun _ _ => norm_nonneg _) (fun p hp => ?_)).trans
    (prod_one_add_inv_primeFactors_le_one_add_log N hN)
  calc
    ‖1 - χ p * (p : ℂ) ^ (-(1 : ℂ))‖ ≤
        ‖(1 : ℂ)‖ + ‖χ p * (p : ℂ) ^ (-(1 : ℂ))‖ := norm_sub_le _ _
    _ = 1 + ‖χ p‖ * (p : ℝ)⁻¹ := by
      simp only [norm_one, norm_mul, Complex.cpow_neg_one, norm_inv, Complex.norm_natCast]
    _ ≤ 1 + (p : ℝ)⁻¹ := by
      have h := mul_le_mul_of_nonneg_right (χ.norm_le_one p)
        (inv_nonneg.mpr (Nat.cast_nonneg p : (0 : ℝ) ≤ p))
      simpa only [one_mul] using add_le_add_right h 1

/-- At one, a nonprincipal inducing character loses only a logarithmic
factor when moved to a larger positive modulus.
@isnad1 id=le.2h3v.s8.7272a632728f from=translated src=- shape=a94f4757 vocab=6d14f534
-/
theorem norm_LFunction_changeLevel_one_le {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1) :
    ‖DirichletCharacter.LFunction (χ.changeLevel hMN) 1‖ ≤
      ‖DirichletCharacter.LFunction χ 1‖ * (1 + Real.log N) := by
  rw [DirichletCharacter.LFunction_changeLevel hMN χ (Or.inl hχ), norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_characterEulerMultiplier_one_le χ N (NeZero.pos N)) (norm_nonneg _)

/-- An actual zero of the inducing L-function remains a zero at the larger
level. The value at the possible principal pole is explicitly excluded.
@isnad1 id=eq.3h4v.s8.185ae2d91bab from=translated src=- shape=6f3c8874 vocab=5291108a
-/
theorem LFunction_changeLevel_eq_zero_of_eq_zero {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (χ : DirichletCharacter ℂ M) (s : ℂ) (hs : s ≠ 1)
    (hzero : DirichletCharacter.LFunction χ s = 0) :
    DirichletCharacter.LFunction (χ.changeLevel hMN) s = 0 := by
  rw [DirichletCharacter.LFunction_changeLevel hMN χ (Or.inr hs), hzero, zero_mul]

/-- A prime Euler factor is nonzero throughout the positive half-plane.
@isnad1 id=ne.2h4v.s7.8769c5cd103b from=translated src=- shape=a16157e6 vocab=8eac65f4
-/
theorem characterEulerFactor_ne_zero_of_re_pos {M : ℕ}
    (χ : DirichletCharacter ℂ M) (p : ℕ) (hp : p.Prime)
    (s : ℂ) (hs : 0 < s.re) :
    1 - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hratio : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]
    calc
      _ ≤ 1 * (p : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (χ.norm_le_one _) (Real.rpow_nonneg hp0.le _)
      _ < 1 := by
        rw [one_mul]
        exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_neg_of_pos hs)
  intro heq
  have heq' : χ p * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp heq).symm
  rw [heq', norm_one] at hratio
  exact lt_irrefl _ hratio

/-- No Euler multiplier introduces a zero in the positive half-plane.
This finite statement includes the empty prime-factor set.
@isnad1 id=ne.1h4v.s7.d53091da80d6 from=translated src=- shape=5d4b0fae vocab=be9f4e88
-/
theorem characterEulerMultiplier_ne_zero_of_re_pos {M : ℕ}
    (χ : DirichletCharacter ℂ M) (N : ℕ) (s : ℂ) (hs : 0 < s.re) :
    (∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))) ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro p hp
  exact characterEulerFactor_ne_zero_of_re_pos χ p
    (Nat.prime_of_mem_primeFactors hp) s hs

/-- Away from the possible principal pole, induction preserves precisely
the actual zeros in the positive half-plane.
@isnad1 id=iff.3h4v.s8.2b7e501ef5e5 from=translated src=- shape=a6104331 vocab=c045eca7
-/
theorem LFunction_changeLevel_eq_zero_iff_of_re_pos
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (χ : DirichletCharacter ℂ M) (s : ℂ) (hs : s ≠ 1) (hre : 0 < s.re) :
    DirichletCharacter.LFunction (χ.changeLevel hMN) s = 0 ↔
      DirichletCharacter.LFunction χ s = 0 := by
  rw [DirichletCharacter.LFunction_changeLevel hMN χ (Or.inr hs), mul_eq_zero]
  simp only [characterEulerMultiplier_ne_zero_of_re_pos χ N s hre, or_false]

end TwinPrime.Analytic
