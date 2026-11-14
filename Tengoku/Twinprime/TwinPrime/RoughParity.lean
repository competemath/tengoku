import Tengoku.Twinprime.TwinPrime.Parity
import Tengoku.Twinprime.TwinPrime.Correlation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact rough-number parity identities

On `(X, 2X]`, sifting both `n` and `n + 2` by all primes at most `z`
leaves only primes and semiprimes if `2X + 2 < z^3`. Semiprimes include
prime squares. The two separate Liouville selectors therefore isolate twins.
The concluding implications retain every required lower-bound and parity
estimate as an explicit hypothesis.
-/

noncomputable section

open Finset ArithmeticFunction
open TwinPrime.Sieve
open scoped ArithmeticFunction.Omega

namespace TwinPrime

/-- A rough integer below the cube cutoff is prime or the product of two
primes, with no distinctness assumption on the two factors.-/
theorem prime_or_semiprime_of_rough {n z : ℕ} (hn : 2 ≤ n)
    (hnz : n < z ^ 3) (hrough : ∀ p, p.Prime → p ∣ n → z < p) :
    n.Prime ∨ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p * q := by
  have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
  obtain ⟨m, hm⟩ := Nat.minFac_dvd n
  by_cases hm1 : m = 1
  · left
    have hnfac : n = n.minFac := by simpa only [hm1, mul_one] using hm
    exact hnfac.symm ▸ hp
  · right
    have hm0 : m ≠ 0 := by
      intro h
      simp [h] at hm
      omega
    have hpm : z < n.minFac := hrough _ hp (Nat.minFac_dvd n)
    have hmz : m < z * z := by
      by_contra h
      have hz3 : z ^ 3 ≤ n := by
        calc z ^ 3 = z * (z * z) := by ring
          _ ≤ n.minFac * (z * z) := Nat.mul_le_mul_right _ hpm.le
          _ ≤ n.minFac * m := Nat.mul_le_mul_left _ (by omega)
          _ = n := hm.symm
      omega
    refine ⟨n.minFac, m, hp, ?_, hm⟩
    apply prime_of_forall_prime_factor_gt (by omega) hmz
    intro p hpp hpd
    apply hrough p hpp
    rw [hm]
    exact dvd_mul_of_dvd_right hpd _

/-- The factor count is with multiplicity: a prime square has count two.-/
theorem cardFactors_eq_one_or_two_of_rough {n z : ℕ} (hn : 2 ≤ n)
    (hnz : n < z ^ 3) (hrough : ∀ p, p.Prime → p ∣ n → z < p) :
    Ω n = 1 ∨ Ω n = 2 := by
  rcases prime_or_semiprime_of_rough hn hnz hrough with hp | ⟨p, q, hp, hq, rfl⟩
  · exact Or.inl (cardFactors_apply_prime hp)
  · right
    rw [cardFactors_mul hp.ne_zero hq.ne_zero,
      cardFactors_apply_prime hp, cardFactors_apply_prime hq]

/-- On this rough range the single Liouville selector is exactly the prime
indicator multiplied by two. In particular it vanishes on prime squares.-/
theorem one_sub_liouville_eq_prime_selector_of_rough {n z : ℕ} (hn : 2 ≤ n)
    (hnz : n < z ^ 3) (hrough : ∀ p, p.Prime → p ∣ n → z < p) :
    1 - (liouville n : ℝ) = if n.Prime then 2 else 0 := by
  rw [liouville_apply (by omega : n ≠ 0)]
  rcases cardFactors_eq_one_or_two_of_rough hn hnz hrough with h | h
  · rw [ite_eq_left (cardFactors_eq_one_iff_prime.mp h), h]
    norm_num
  · have hnp : ¬ n.Prime := by
      intro hp
      have := cardFactors_apply_prime hp
      omega
    rw [ite_eq_right hnp, h]
    norm_num

/-- The set `R(X,z)` of PLAN.md, with both endpoints fixed explicitly.-/
def roughDyadicSet (X z : ℕ) : Finset ℕ :=
  (Ioc X (2 * X)).filter (fun n => Nat.Coprime (primorial z) (n * (n + 2)))

def roughDyadicCount (X z : ℕ) : ℕ := (roughDyadicSet X z).card

def roughLiouvilleLeft (X z : ℕ) : ℝ :=
  ∑ n ∈ roughDyadicSet X z, (liouville n : ℝ)

def roughLiouvilleRight (X z : ℕ) : ℝ :=
  ∑ n ∈ roughDyadicSet X z, (liouville (n + 2) : ℝ)

def roughLiouvilleProduct (X z : ℕ) : ℝ :=
  ∑ n ∈ roughDyadicSet X z, (liouville n : ℝ) * (liouville (n + 2) : ℝ)

def roughParityCombination (X z : ℕ) : ℝ :=
  roughDyadicCount X z - roughLiouvilleLeft X z - roughLiouvilleRight X z +
    roughLiouvilleProduct X z

/-- Every dyadic twin survives the sifting when `z < X`, so there is no
small-prime-pair correction in the identity.-/
theorem twin_mem_roughDyadicSet {X z n : ℕ} (hzX : z < X)
    (hn : n ∈ Ioc X (2 * X)) (htwin : n ∈ twinPrimes) :
    n ∈ roughDyadicSet X z := by
  refine mem_filter.mpr ⟨hn, coprime_primorial_iff.mpr ?_⟩
  intro p hp hpz hpd
  rcases hp.dvd_mul.mp hpd with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hp htwin.1).mp h
    have := (mem_Ioc.mp hn).1
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hp htwin.2).mp h
    have := (mem_Ioc.mp hn).1
    omega

/-- The product of the two separate selectors is four precisely on twins.
The lower bound on `z` and `z < X` exclude `n = 0, 1`; the shifted member
is also at least two.-/
theorem rough_liouville_selector {X z n : ℕ} (hz : 3 ≤ z) (hzX : z < X)
    (hcube : 2 * X + 2 < z ^ 3) (hn : n ∈ roughDyadicSet X z) :
    (1 - (liouville n : ℝ)) * (1 - (liouville (n + 2) : ℝ)) =
      if n ∈ twinPrimes then 4 else 0 := by
  obtain ⟨hinterval, hcop⟩ := mem_filter.mp hn
  obtain ⟨hXn, hnX⟩ := mem_Ioc.mp hinterval
  have hrough := coprime_primorial_iff.mp hcop
  have hleft : ∀ p, p.Prime → p ∣ n → z < p := by
    intro p hp hpd
    by_contra h
    exact hrough p hp (by omega) (dvd_mul_of_dvd_left hpd _)
  have hright : ∀ p, p.Prime → p ∣ n + 2 → z < p := by
    intro p hp hpd
    by_contra h
    exact hrough p hp (by omega) (dvd_mul_of_dvd_right hpd _)
  rw [one_sub_liouville_eq_prime_selector_of_rough (by omega) (by omega) hleft,
    one_sub_liouville_eq_prime_selector_of_rough (by omega) (by omega) hright]
  simp only [mem_twinPrimes]
  split_ifs <;> norm_num <;> tauto

/-- A weighted finite form, valid for arbitrary real weights without positivity
or distribution assumptions.-/
theorem rough_liouville_weighted_identity (X z : ℕ) (hz : 3 ≤ z) (hzX : z < X)
    (hcube : 2 * X + 2 < z ^ 3) (a : ℕ → ℝ) :
    4 * ∑ n ∈ (Ioc X (2 * X)).filter (· ∈ twinPrimes), a n =
      ∑ n ∈ roughDyadicSet X z,
        a n * ((1 - (liouville n : ℝ)) * (1 - (liouville (n + 2) : ℝ))) := by
  have heq : (roughDyadicSet X z).filter (· ∈ twinPrimes) =
      (Ioc X (2 * X)).filter (· ∈ twinPrimes) := by
    ext n
    simp only [mem_filter]
    constructor
    · rintro ⟨hn, htwin⟩
      exact ⟨(mem_filter.mp hn).1, htwin⟩
    · rintro ⟨hn, htwin⟩
      exact ⟨twin_mem_roughDyadicSet hzX hn htwin, htwin⟩
  rw [← heq, sum_filter, mul_sum]
  apply sum_congr rfl
  intro n hn
  rw [rough_liouville_selector hz hzX hcube hn]
  split_ifs <;> ring

/-- PLAN.md (R), exactly: `4 N₂ = S - L₀ - L₂ + L₀₂`.-/
theorem rough_parity_identity (X z : ℕ) (hz : 3 ≤ z) (hzX : z < X)
    (hcube : 2 * X + 2 < z ^ 3) :
    4 * (N2 X : ℝ) = roughParityCombination X z := by
  have h := rough_liouville_weighted_identity X z hz hzX hcube (fun _ => 1)
  simp only [sum_const, nsmul_eq_mul, mul_one, one_mul] at h
  rw [N2, h]
  unfold roughParityCombination roughDyadicCount roughLiouvilleLeft
    roughLiouvilleRight roughLiouvilleProduct
  simp_rw [show ∀ u v : ℝ, (1 - u) * (1 - v) = 1 - u - v + u * v by
    intros; ring]
  simp [sum_add_distrib, sum_sub_distrib]

/-- Cofinal positivity of this specified four-correlation combination suffices.
This theorem does not assert that the required positive intervals exist.-/
theorem twinPrimeConjecture_of_cofinal_roughParity_pos
    (h : ∀ Y : ℕ, ∃ X ≥ Y, ∃ z : ℕ, 3 ≤ z ∧ z < X ∧
      2 * X + 2 < z ^ 3 ∧ 0 < roughParityCombination X z) :
    TwinPrimeConjecture := by
  apply twinPrimeConjecture_iff_cofinal_N2_pos.mpr
  intro Y
  obtain ⟨X, hXY, z, hz, hzX, hcube, hpos⟩ := h Y
  refine ⟨X, hXY, ?_⟩
  rw [← rough_parity_identity X z hz hzX hcube] at hpos
  have : (0 : ℝ) < N2 X := by linarith
  exact_mod_cast this

/-- Separate sufficient inputs: a positive lower bound `M` for the rough count
on the admissible range, and a cofinal one-sided parity bound saving a positive
fraction of that lower bound. Neither input is proved here.-/
theorem twinPrimeConjecture_of_rough_distribution_and_parity
    (z : ℕ → ℕ) (M : ℕ → ℝ) (δ : ℝ) (hδ : 0 < δ) (X₀ : ℕ)
    (hrange : ∀ X ≥ X₀, 3 ≤ z X ∧ z X < X ∧ 2 * X + 2 < (z X) ^ 3)
    (hM : ∀ X ≥ X₀, 0 < M X)
    (hdistribution : ∀ X ≥ X₀, M X ≤ (roughDyadicCount X (z X) : ℝ))
    (hparity : ∀ Y : ℕ, ∃ X ≥ max Y X₀,
      roughLiouvilleLeft X (z X) + roughLiouvilleRight X (z X) -
        roughLiouvilleProduct X (z X) ≤ (1 - δ) * M X) :
    TwinPrimeConjecture := by
  apply twinPrimeConjecture_of_cofinal_roughParity_pos
  intro Y
  obtain ⟨X, hX, hpar⟩ := hparity Y
  have hX₀ : X₀ ≤ X := le_trans (le_max_right _ _) hX
  obtain ⟨hz, hzX, hcube⟩ := hrange X hX₀
  refine ⟨X, le_trans (le_max_left _ _) hX, z X, hz, hzX, hcube, ?_⟩
  have hdist := hdistribution X hX₀
  have hpos := mul_pos hδ (hM X hX₀)
  unfold roughParityCombination
  nlinarith

end TwinPrime
