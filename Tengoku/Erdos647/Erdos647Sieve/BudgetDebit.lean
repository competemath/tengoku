/-
The unconditional corrected small-prime budget, against the protected specification.
New implementation source. Not compiled in the assistant environment.
No Mertens import, cofactor assumption, or presumed budget estimate is used.
-/
import Tengoku.Erdos647.Erdos647Sieve.DivisorBudget
import Tengoku.Erdos647.Erdos647Sieve.Occupancy
import Tengoku.Erdos647.Erdos647Sieve.HitCountBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve

/-- The unrestricted polynomial is still over Z. Only for n>H can its factors be
identified with casts of the positive natural values n-k.-/
theorem windowPolynomial_eq_nat_product {H n : ℕ} (hHn : H < n) :
    windowPolynomial H (n : ℤ) =
      ((∏ k ∈ Finset.Icc 1 H, (n - k) : ℕ) : ℤ) := by
  classical
  unfold windowPolynomial
  rw [Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro k hk
  have hkn : k ≤ n := (Finset.mem_Icc.mp hk).2.trans hHn.le
  exact (Nat.cast_sub hkn).symm

/-- Elementary prime-divides-product extraction, with no assumptions on the values.-/
theorem prime_dvd_nat_product_iff {p : ℕ} (hp : p.Prime) (S : Finset ℕ) (f : ℕ → ℕ) :
    p ∣ ∏ k ∈ S, f k ↔ ∃ k ∈ S, p ∣ f k := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      constructor
      · intro hd
        have heq : p = 1 := Nat.eq_one_of_dvd_one (by simpa using hd)
        exact (hp.ne_one heq).elim
      · rintro ⟨k, hk, _⟩
        simp at hk
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha, hp.dvd_mul, ih]
      simp only [Finset.mem_insert]
      constructor
      · rintro (h | ⟨k, hk, h⟩)
        · exact ⟨a, Or.inl rfl, h⟩
        · exact ⟨k, Or.inr hk, h⟩
      · rintro ⟨k, (hka | hk), hd⟩
        · subst k
          exact Or.inl hd
        · exact Or.inr ⟨k, hk, hd⟩

/-- Bridge the prime divisibility test over Z to an actual positive window value.-/
theorem prime_dvd_window_iff {H n p : ℕ} (hHn : H < n) (hp : p.Prime) :
    (p : ℤ) ∣ windowPolynomial H (n : ℤ) ↔
      ∃ k ∈ Finset.Icc 1 H, p ∣ n - k := by
  rw [windowPolynomial_eq_nat_product hHn]
  have hcast : ((p : ℤ) ∣ ((∏ k ∈ Finset.Icc 1 H, (n - k) : ℕ) : ℤ)) ↔
      p ∣ (∏ k ∈ Finset.Icc 1 H, (n - k) : ℕ) := by
    constructor <;> intro h <;> exact_mod_cast h
  rw [hcast]
  exact prime_dvd_nat_product_iff hp (Finset.Icc 1 H) (fun k => n - k)

/-- Every prime hit contributes at least one incidence with a shift.-/
theorem one_le_divisorOccurrences_of_hit {H n p : ℕ} (hHn : H < n) (hp : p.Prime)
    (hhit : (p : ℤ) ∣ windowPolynomial H (n : ℤ)) :
    1 ≤ divisorOccurrences H n p := by
  obtain ⟨k, hk, hkdvd⟩ := (prime_dvd_window_iff hHn hp).mp hhit
  have hpos : 0 < ((Finset.Icc 1 H).filter (fun k => p ∣ n - k)).card :=
    Finset.card_pos.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hkdvd⟩⟩
  exact hpos

/-- The selected-prime and small-prime sets are disjoint for purely order reasons.-/
theorem smallPrimes_disjoint_selectedPrimes (H : ℕ) (y : ℝ) :
    Disjoint ((Finset.Icc 2 H).filter Nat.Prime) (selectedPrimes H y) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hpSmall hpSelected
  have hple : p ≤ H := (Finset.mem_Icc.mp (Finset.mem_filter.mp hpSmall).1).2
  have hpge : H + 1 ≤ p := by
    have hmem : p ∈ (Finset.Icc (H + 1) (Nat.floor y)).filter Nat.Prime := hpSelected
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hmem).1).1
  omega

/-- Disjoint small and selected prime incidences fit inside the total omega budget.
This lemma does not require a prefix survivor: it holds in every positive window.-/
theorem smallPrimeDebit_add_hitCount_le_primeFactor_sum
    {H n : ℕ} (hHn : H < n) (y : ℝ) :
    smallPrimeDebit H + hitCount H y (n : ℤ) ≤
      ∑ k ∈ Finset.Icc 1 H, (n - k).primeFactors.card := by
  classical
  let S : Finset ℕ := (Finset.Icc 2 H).filter Nat.Prime
  let L : Finset ℕ := (selectedPrimes H y).filter
    (fun p => (p : ℤ) ∣ windowPolynomial H (n : ℤ))
  have hSprime : ∀ p ∈ S, p.Prime := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hLprime : ∀ p ∈ L, p.Prime := by
    intro p hp
    have hpSel : p ∈ selectedPrimes H y := (Finset.mem_filter.mp hp).1
    change p ∈ (Finset.Icc (H + 1) (Nat.floor y)).filter Nat.Prime at hpSel
    exact (Finset.mem_filter.mp hpSel).2
  have hdisj : Disjoint S L := by
    apply Finset.disjoint_left.mpr
    intro p hpS hpL
    exact (Finset.disjoint_left.mp (smallPrimes_disjoint_selectedPrimes H y))
      hpS (Finset.mem_filter.mp hpL).1
  have hsmall : smallPrimeDebit H ≤ ∑ p ∈ S, divisorOccurrences H n p := by
    change (∑ p ∈ S, H / p) ≤ _
    apply Finset.sum_le_sum
    intro p hp
    exact div_le_divisorOccurrences hHn (hSprime p hp).pos
  have hlarge : hitCount H y (n : ℤ) ≤ ∑ p ∈ L, divisorOccurrences H n p := by
    have hLcard : L.card ≤ ∑ p ∈ L, divisorOccurrences H n p := by
      calc
        L.card = ∑ p ∈ L, (1 : ℕ) := by simp
        _ ≤ ∑ p ∈ L, divisorOccurrences H n p := by
          apply Finset.sum_le_sum
          intro p hp
          exact one_le_divisorOccurrences_of_hit hHn (hLprime p hp)
            (Finset.mem_filter.mp hp).2
    have hcount : hitCount H y (n : ℤ) = L.card := by
      simpa only [L] using hitCount_eq_nat_filter_card H y (n : ℤ)
    exact hcount.le.trans hLcard
  have hrow : ∀ k ∈ Finset.Icc 1 H,
      ((S ∪ L).filter (fun p => p ∣ n - k)).card ≤ (n - k).primeFactors.card := by
    intro k hk
    have hkn : k < n := lt_of_le_of_lt (Finset.mem_Icc.mp hk).2 hHn
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hpUnion, hpdvd⟩ := Finset.mem_filter.mp hp
    have hprime : p.Prime := by
      rcases Finset.mem_union.mp hpUnion with hpS | hpL
      · exact hSprime p hpS
      · exact hLprime p hpL
    exact Nat.mem_primeFactors.mpr ⟨hprime, hpdvd, by omega⟩
  calc
    smallPrimeDebit H + hitCount H y (n : ℤ)
        ≤ (∑ p ∈ S, divisorOccurrences H n p) +
          ∑ p ∈ L, divisorOccurrences H n p := add_le_add hsmall hlarge
    _ = ∑ p ∈ S ∪ L, divisorOccurrences H n p := (Finset.sum_union hdisj).symm
    _ = ∑ k ∈ Finset.Icc 1 H,
          ((S ∪ L).filter (fun p => p ∣ n - k)).card :=
        sum_divisorOccurrences_eq (S ∪ L) H n
    _ ≤ ∑ k ∈ Finset.Icc 1 H, (n - k).primeFactors.card :=
        Finset.sum_le_sum hrow

/-- The EXACT protected target; no missing arithmetic estimate is a premise.-/
theorem budgetDebit : BudgetDebitClaim := by
  intro n H y _hH _hy hprefix
  have hinc := smallPrimeDebit_add_hitCount_le_primeFactor_sum hprefix.1 y
  have hlog := prefix_primeFactor_sum_le_logBudget hprefix
  have hcast : (smallPrimeDebit H : ℤ) + (hitCount H y (n : ℤ) : ℤ) ≤
      ((∑ k ∈ Finset.Icc 1 H, (n - k).primeFactors.card : ℕ) : ℤ) := by
    exact_mod_cast hinc
  unfold correctedBudget
  omega

end Erdos647Sieve
end
