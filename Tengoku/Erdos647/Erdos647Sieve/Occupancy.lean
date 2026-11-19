/-
Minimum divisor occupancy in a positive backwards window.
New implementation source. Not compiled in the assistant environment.
The argument constructs distinct shifts, not a finite enumeration certificate.
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve

/-- Number of shifts in the window whose positive value is divisible by p.-/
def divisorOccurrences (H n p : ℕ) : ℕ :=
  ((Finset.Icc 1 H).filter (fun k => p ∣ n - k)).card

/-- Any positive p divides at least floor(H/p) of H consecutive positive integers.
The map j ↦ ((n-1) mod p + 1) + j*p supplies the distinct shifts.-/
theorem div_le_divisorOccurrences {H n p : ℕ} (hHn : H < n) (hp : 0 < p) :
    H / p ≤ divisorOccurrences H n p := by
  classical
  let r : ℕ := (n - 1) % p + 1
  have hn : 1 ≤ n := by omega
  have hr1 : 1 ≤ r := by dsimp [r]; omega
  have hrp : r ≤ p := by
    have hmod := Nat.mod_lt (n - 1) hp
    dsimp [r]
    omega
  have hnbase : n - r = p * ((n - 1) / p) := by
    have hdecomp := Nat.mod_add_div (n - 1) p
    dsimp [r]
    omega
  have hbase : p ∣ n - r := ⟨(n - 1) / p, hnbase⟩
  have hmap : ∀ j ∈ Finset.range (H / p),
      r + j * p ∈ (Finset.Icc 1 H).filter (fun k => p ∣ n - k) := by
    intro j hj
    have hjlt : j < H / p := Finset.mem_range.mp hj
    have hjle : j + 1 ≤ H / p := by omega
    have hmul := Nat.mul_le_mul_right p hjle
    have hdecomp := Nat.mod_add_div H p
    have hupper : r + j * p ≤ H := by
      nlinarith [Nat.zero_le (H % p)]
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hupper⟩, ?_⟩
    have heq : n - (r + j * p) = (n - r) - j * p := by omega
    rw [heq]
    exact Nat.dvd_sub hbase (Nat.dvd_mul_left p j)
  have hinj : Set.InjOn (fun j : ℕ => r + j * p) (Finset.range (H / p) : Set ℕ) := by
    intro i _ j _ hij
    have hmul : i * p = j * p := Nat.add_left_cancel hij
    exact mul_right_cancel₀ (Nat.ne_of_gt hp) hmul
  have hcard :
      (Finset.range (H / p)).card ≤
        ((Finset.Icc 1 H).filter (fun k => p ∣ n - k)).card := by
    apply Finset.card_le_card_of_injOn (fun j : ℕ => r + j * p)
    · intro j hj
      exact hmap j hj
    · exact hinj
  simpa only [Finset.card_range, divisorOccurrences] using hcard

/-- Transpose the finite incidence relation between selected primes and shifts.-/
theorem sum_divisorOccurrences_eq (P : Finset ℕ) (H n : ℕ) :
    (∑ p ∈ P, divisorOccurrences H n p) =
      ∑ k ∈ Finset.Icc 1 H, (P.filter (fun p => p ∣ n - k)).card := by
  classical
  unfold divisorOccurrences
  have hcard (s : Finset ℕ) : s.card = ∑ _ ∈ s, (1 : ℕ) := by simp
  simp only [hcard, Finset.sum_filter]
  rw [Finset.sum_comm]

end Erdos647Sieve
end
