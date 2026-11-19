import Tengoku.MagicSquaresFieldsLean.MagicSquares.FieldTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace MagicSquares.Certificates

local instance q3ExtensionCoveragePrimeDecidable (n : ℕ) : Decidable n.Prime :=
  Nat.decidablePrime' n

/-- Exhaustive enumeration only needs small bases and exponents.-/
private theorem q3_extension_grid : ∀ p ∈ Finset.range 83, ∀ n ∈ Finset.range 20,
    p.Prime → 1 < n → p ^ n < 553736 → p ^ n % 4 = 3 →
      p ^ n ∈ ([27, 243, 343, 1331, 2187, 6859, 12167, 16807, 19683, 29791,
        79507, 103823, 161051, 177147, 205379, 300763, 357911, 493039] : List ℕ) := by
  decide +kernel

/-- Every prime power in the remaining residue class is either prime or
one of eighteen extension-field orders (sixteen positive, two exceptional).-/
theorem q3_prime_power_coverage {q : ℕ} (hq : q < 553736)
    (hpp : IsPrimePow q) (hm : q % 4 = 3) :
    q.Prime ∨ q ∈ ([27, 243, 343, 1331, 2187, 6859, 12167, 16807, 19683, 29791,
      79507, 103823, 161051, 177147, 205379, 300763, 357911, 493039] : List ℕ) := by
  obtain ⟨p, n, hp, hn, rfl⟩ := (isPrimePow_nat_iff q).mp hpp
  by_cases hn1 : n = 1
  · left
    simpa [hn1] using hp
  right
  have hn2 : n ≠ 2 := by
    intro hn2
    subst n
    have hr : p % 4 < 4 := Nat.mod_lt _ (by decide)
    interval_cases hv : p % 4 <;> norm_num [Nat.pow_mod, hv] at hm
  have hn3 : 3 ≤ n := by omega
  have hn20 : n < 20 := by
    by_contra hh
    have hlow : 2 ^ 20 ≤ p ^ n :=
      (Nat.pow_le_pow_left hp.two_le 20).trans (Nat.pow_le_pow_right hp.one_lt.le (by omega))
    norm_num at hlow
    omega
  have hp83 : p < 83 := by
    by_contra hh
    have hlow : 83 ^ 3 ≤ p ^ n :=
      (Nat.pow_le_pow_left (by omega : 83 ≤ p) 3).trans
        (Nat.pow_le_pow_right hp.one_lt.le hn3)
    norm_num at hlow
    omega
  exact q3_extension_grid p (Finset.mem_range.mpr hp83) n (Finset.mem_range.mpr hn20)
    hp (by omega) hq hm

end MagicSquares.Certificates
