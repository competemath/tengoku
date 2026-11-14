import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Twin primes: definitions, equivalent formulations, elementary structure

The target theorem (the twin prime conjecture) is, verbatim,

  theorem twin_prime_conjecture :
      {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite

It is **open**. In this file it is recorded as the proposition `TwinPrimeConjecture`, and we
prove a number of things *about* it:

* equivalent formulations (unboundedness, `∀ N ∃ p > N`, frequently-at-top, the `6k ± 1` form,
  and equivalence with "bounded gaps `≤ 2`");
* elementary structure of twin primes (`p % 6 = 5` for `p ≥ 5`);
* Clement's criterion (1949): for `n ≥ 2`, `n` and `n + 2` are both prime iff
  `n (n + 2) ∣ 4 ((n - 1)! + 1) + n`;
* verified small instances.

Nothing here is deep; the point is to have a precise, machine-checked interface for the rest of
the project.
-/

namespace TwinPrime

open Nat Set Filter

/-- The set of lower members of twin prime pairs.-/
def twinPrimes : Set ℕ := {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}

/-- The twin prime conjecture, as a proposition (open).-/
def TwinPrimeConjecture : Prop := twinPrimes.Infinite

theorem twinPrimeConjecture_iff :
    TwinPrimeConjecture ↔ {p : ℕ | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite := Iff.rfl

@[simp] theorem mem_twinPrimes {p : ℕ} : p ∈ twinPrimes ↔ p.Prime ∧ (p + 2).Prime := Iff.rfl

instance : DecidablePred (· ∈ twinPrimes) := fun p =>
  inferInstanceAs (Decidable (p.Prime ∧ (p + 2).Prime))

/-! ### Small instances -/

theorem three_mem : 3 ∈ twinPrimes := by norm_num [mem_twinPrimes]
theorem five_mem : 5 ∈ twinPrimes := by norm_num [mem_twinPrimes]
theorem eleven_mem : 11 ∈ twinPrimes := by norm_num [mem_twinPrimes]
theorem seventeen_mem : 17 ∈ twinPrimes := by norm_num [mem_twinPrimes]
theorem two_not_mem : 2 ∉ twinPrimes := by norm_num [mem_twinPrimes]
theorem seven_not_mem : 7 ∉ twinPrimes := by norm_num [mem_twinPrimes]

/-- The twin primes have no upper bound at least as far as `101`: the eight pairs below 100.-/
theorem twinPrimes_lt_100 :
    (Finset.range 100).filter (· ∈ twinPrimes) = {3, 5, 11, 17, 29, 41, 59, 71} := by
  decide

/-! ### Equivalent formulations -/

theorem twinPrimeConjecture_iff_not_bddAbove : TwinPrimeConjecture ↔ ¬ BddAbove twinPrimes :=
  ⟨Set.Infinite.not_bddAbove, Set.infinite_of_not_bddAbove⟩

theorem twinPrimeConjecture_iff_forall_exists_gt :
    TwinPrimeConjecture ↔ ∀ N : ℕ, ∃ p ∈ twinPrimes, N < p := by
  rw [twinPrimeConjecture_iff_not_bddAbove, not_bddAbove_iff]

theorem twinPrimeConjecture_iff_frequently :
    TwinPrimeConjecture ↔ ∃ᶠ p in atTop, p.Prime ∧ (p + 2).Prime :=
  Nat.frequently_atTop_iff_infinite.symm

/-- The twin prime conjecture implies (trivially) that there are infinitely many primes.-/
theorem infinite_primes_of_twinPrimeConjecture (h : TwinPrimeConjecture) :
    {p : ℕ | p.Prime}.Infinite := by
  refine Set.Infinite.mono ?_ h
  intro p hp
  exact hp.1

/-! ### Structure mod 6 -/

/-- Every twin prime `p ≥ 5` is `≡ 5 (mod 6)`.-/
theorem mod_six_eq_five {p : ℕ} (hp : p ∈ twinPrimes) (h5 : 5 ≤ p) : p % 6 = 5 := by
  obtain ⟨hp1, hp2⟩ := hp
  have h2 : p % 2 = 1 := by
    rcases hp1.eq_two_or_odd with h | h
    · omega
    · exact h
  have h3 : p % 3 ≠ 0 := fun h => by
    have h3p : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp1).mp h3p
    omega
  have h3' : (p + 2) % 3 ≠ 0 := fun h => by
    have h3p : 3 ∣ p + 2 := Nat.dvd_of_mod_eq_zero h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp2).mp h3p
    omega
  have hp3 : p % 3 = 2 := by
    have : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases this with h | h
    · exfalso; apply h3'; omega
    · exact h
  omega

/-- Every twin prime pair other than `(3, 5)` has the form `(6k - 1, 6k + 1)`.-/
theorem exists_eq_six_mul_sub_one {p : ℕ} (hp : p ∈ twinPrimes) (h5 : 5 ≤ p) :
    ∃ k, 1 ≤ k ∧ p = 6 * k - 1 := by
  have := mod_six_eq_five hp h5
  exact ⟨(p + 1) / 6, by omega, by omega⟩

/-- The `6k ± 1` formulation.-/
theorem twinPrimeConjecture_iff_six :
    TwinPrimeConjecture ↔ {k : ℕ | (6 * k - 1).Prime ∧ (6 * k + 1).Prime}.Infinite := by
  rw [twinPrimeConjecture_iff_forall_exists_gt]
  constructor
  · intro h
    refine Set.infinite_of_forall_exists_gt fun N => ?_
    obtain ⟨p, hp, hNp⟩ := h (6 * N + 5)
    have h6 := mod_six_eq_five hp (by omega)
    refine ⟨(p + 1) / 6, ?_, by omega⟩
    have e1 : 6 * ((p + 1) / 6) - 1 = p := by omega
    have e2 : 6 * ((p + 1) / 6) + 1 = p + 2 := by omega
    simp only [Set.mem_ofPred_eq, e1, e2]
    exact hp
  · intro h N
    obtain ⟨k, hk, hNk⟩ := Set.Infinite.exists_gt h N
    refine ⟨6 * k - 1, ?_, by omega⟩
    have e : 6 * k - 1 + 2 = 6 * k + 1 := by omega
    simp only [mem_twinPrimes, e]
    exact hk

/-! ### Relation with bounded gaps -/

/-- "Bounded gaps `≤ H`": infinitely many primes `p` have another prime in `(p, p + H]`.
Zhang (2013) proved `BoundedGaps 70000000`; Polymath8b / Maynard give `BoundedGaps 246`.-/
def BoundedGaps (H : ℕ) : Prop :=
  {p : ℕ | p.Prime ∧ ∃ q, p < q ∧ q ≤ p + H ∧ q.Prime}.Infinite

theorem boundedGaps_mono {H H' : ℕ} (h : H ≤ H') (hH : BoundedGaps H) : BoundedGaps H' := by
  unfold BoundedGaps at hH ⊢
  refine Set.Infinite.mono ?_ hH
  rintro p ⟨hp, q, hq1, hq2, hq3⟩
  exact ⟨hp, q, hq1, by omega, hq3⟩

theorem boundedGaps_two_of_twinPrimeConjecture (h : TwinPrimeConjecture) : BoundedGaps 2 := by
  unfold BoundedGaps
  refine Set.Infinite.mono ?_ h
  rintro p ⟨hp, hq⟩
  exact ⟨hp, p + 2, by omega, le_rfl, hq⟩

/-- Bounded gaps `≤ 2` is *equivalent* to the twin prime conjecture: the only prime pair at
distance `1` is `(2, 3)`.-/
theorem twinPrimeConjecture_iff_boundedGaps_two : TwinPrimeConjecture ↔ BoundedGaps 2 := by
  refine ⟨boundedGaps_two_of_twinPrimeConjecture, fun h => ?_⟩
  have hsub : {p : ℕ | p.Prime ∧ ∃ q, p < q ∧ q ≤ p + 2 ∧ q.Prime} ⊆ twinPrimes ∪ {2} := by
    rintro p ⟨hp, q, hq1, hq2, hq3⟩
    by_cases h2 : p = 2
    · exact Or.inr (by simp [h2])
    · left
      refine ⟨hp, ?_⟩
      have hodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left h2
      rcases Nat.lt_or_ge q (p + 2) with hlt | hge
      · -- q = p + 1 is even and > 2, impossible
        have hq : q = p + 1 := by omega
        subst hq
        have h1 := hq3.eq_two_or_odd
        have h2' := hp.two_le
        omega
      · have hq : q = p + 2 := by omega
        subst hq
        exact hq3
  rcases Set.infinite_union.mp (h.mono hsub) with h1 | h1
  · exact h1
  · exact absurd h1 (Set.finite_singleton 2).not_infinite

/-! ### Clement's criterion -/

private theorem cast_eq_zero_of_dvd {a n : ℕ} (h : n ∣ a) : ((a : ℕ) : ZMod n) = 0 := by
  have := (ZMod.natCast_eq_natCast_iff a 0 n).mpr (Nat.modEq_zero_iff_dvd.mpr h)
  simpa using this

private theorem dvd_of_cast_eq_zero {a n : ℕ} (h : ((a : ℕ) : ZMod n) = 0) : n ∣ a := by
  have := (ZMod.natCast_eq_natCast_iff a 0 n).mp (by simpa using h)
  exact Nat.modEq_zero_iff_dvd.mp this

/-- `(n + 1)! = (n + 1) · n · (n - 1)!` for `n ≥ 1`.-/
private theorem factorial_add_one_eq {n : ℕ} (hn : 1 ≤ n) :
    (n + 1)! = (n + 1) * (n * (n - 1)!) := by
  rw [Nat.factorial_succ, Nat.mul_factorial_pred (by omega)]

private theorem natCast_eq_neg_two (n : ℕ) : ((n : ℕ) : ZMod (n + 2)) = -2 := by
  have := ZMod.natCast_self (n + 2)
  push_cast at this
  linear_combination this

/-- **Clement's criterion** (1949). For `n ≥ 2`: `n` and `n + 2` are both prime if and only if
`n (n + 2) ∣ 4 ((n - 1)! + 1) + n`.-/
theorem clement {n : ℕ} (hn : 2 ≤ n) :
    n ∈ twinPrimes ↔ n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n := by
  constructor
  · rintro ⟨hp, hq⟩
    have hn2 : n ≠ 2 := by
      rintro rfl
      norm_num at hq
    have hodd : n % 2 = 1 := hp.eq_two_or_odd.resolve_left hn2
    haveI := Fact.mk hp
    haveI := Fact.mk hq
    -- Wilson for `n`: `n ∣ (n-1)! + 1`
    have h1 : n ∣ (n - 1)! + 1 := by
      apply dvd_of_cast_eq_zero
      push_cast
      rw [ZMod.wilsons_lemma n]
      ring
    -- Wilson for `n + 2`: `(n + 2) ∣ 2 (2 (n-1)! + 1)`
    have h2 : n + 2 ∣ 2 * (2 * (n - 1)! + 1) := by
      apply dvd_of_cast_eq_zero
      have hw : (((n + 2) - 1)! : ZMod (n + 2)) = -1 := ZMod.wilsons_lemma (n + 2)
      rw [show n + 2 - 1 = n + 1 from rfl, factorial_add_one_eq (by omega)] at hw
      push_cast at hw ⊢
      have hn' := natCast_eq_neg_two n
      linear_combination 2 * hw - 2 * ((n - 1)! : ZMod (n + 2)) * ((n : ZMod (n + 2)) - 1) * hn'
    have hA : n ∣ 4 * ((n - 1)! + 1) + n := Dvd.dvd.add (Dvd.dvd.mul_left h1 4) (dvd_refl n)
    have hB : n + 2 ∣ 4 * ((n - 1)! + 1) + n := by
      have e : 4 * ((n - 1)! + 1) + n = 2 * (2 * (n - 1)! + 1) + (n + 2) := by ring
      rw [e]
      exact Dvd.dvd.add h2 (dvd_refl _)
    have hcop : Nat.Coprime n (n + 2) := (Nat.coprime_primes hp hq).mpr (by omega)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hA hB
  · intro h
    have hdn : n ∣ 4 * ((n - 1)! + 1) := by
      have := Nat.dvd_trans (dvd_mul_right n (n + 2)) h
      exact (Nat.dvd_add_left (dvd_refl n)).mp this
    have hdn2 : n + 2 ∣ 2 * (2 * (n - 1)! + 1) := by
      have h' := Nat.dvd_trans (dvd_mul_left (n + 2) n) h
      have e : 4 * ((n - 1)! + 1) + n = 2 * (2 * (n - 1)! + 1) + (n + 2) := by ring
      rw [e] at h'
      exact (Nat.dvd_add_left (dvd_refl _)).mp h'
    -- `n` is odd
    have hodd : n % 2 = 1 := by
      by_contra hev
      have hk : n / 2 + 1 ∣ 2 * (n - 1)! + 1 := by
        have e : n + 2 = 2 * (n / 2 + 1) := by omega
        rw [e] at hdn2
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdn2
      rcases Nat.lt_or_ge n 4 with h4 | h4
      · have : n = 2 := by omega
        subst this
        norm_num at h
      · have hle : n / 2 + 1 ≤ n - 1 := by omega
        have hd : n / 2 + 1 ∣ (n - 1)! := Nat.dvd_factorial (by omega) hle
        have h1 : n / 2 + 1 ∣ 1 := (Nat.dvd_add_right (Dvd.dvd.mul_left hd 2)).mp hk
        have := Nat.dvd_one.mp h1
        omega
    have hcop2 : Nat.Coprime 2 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
    have hp : n.Prime := by
      have hcop : Nat.Coprime n 4 := by
        simpa using (Nat.Coprime.pow_left 2 hcop2).symm
      have h1 : n ∣ (n - 1)! + 1 := hcop.dvd_of_dvd_mul_left hdn
      rw [Nat.prime_iff_fac_equiv_neg_one (by omega)]
      have h0 := cast_eq_zero_of_dvd h1
      push_cast at h0
      linear_combination h0
    have hq : (n + 2).Prime := by
      have hcop : Nat.Coprime (n + 2) 2 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)).symm
      have h1 : n + 2 ∣ 2 * (n - 1)! + 1 := hcop.dvd_of_dvd_mul_left hdn2
      rw [Nat.prime_iff_fac_equiv_neg_one (by omega)]
      have h0 := cast_eq_zero_of_dvd h1
      push_cast at h0
      rw [show n + 2 - 1 = n + 1 from rfl, factorial_add_one_eq (by omega)]
      push_cast
      have hn' := natCast_eq_neg_two n
      linear_combination h0 + ((n - 1)! : ZMod (n + 2)) * ((n : ZMod (n + 2)) - 1) * hn'
    exact ⟨hp, hq⟩

end TwinPrime
