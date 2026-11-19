import Tengoku.Erdos278.Erdos278.Towers
import Tengoku.Seed.Data.Nat.Log

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

/-- A finite prefix of digits, least significant first.-/
def radixPrefix (b : ℕ) (u : ℕ → Fin b) : ℕ → ℕ
  | 0 => 0
  | k+1 => radixPrefix b u k + b^k * (u k).val

theorem radix_prefix_bound {b : ℕ} (hb : 0 < b) (u : ℕ → Fin b) (k : ℕ) :
    radixPrefix b u k < b^k := by
  induction k with
  | zero => simp [radixPrefix]
  | succ k ih =>
    have hd := (u k).isLt
    have hp := pow_pos hb k
    simp only [radixPrefix, pow_succ]
    nlinarith

theorem radix_prefix_step_mod {b : ℕ} (hb : 0 < b)
    (u : ℕ → Fin b) (k : ℕ) :
    radixPrefix b u (k+1) % b^k = radixPrefix b u k := by
  rw [radixPrefix, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (radix_prefix_bound hb u k)]

theorem radix_prefix_mod {b : ℕ} (hb : 0 < b)
    (u : ℕ → Fin b) {k d : ℕ} (hkd : k ≤ d) :
    radixPrefix b u d % b^k = radixPrefix b u k := by
  induction d, hkd using Nat.le_induction with
  | base => exact Nat.mod_eq_of_lt (radix_prefix_bound hb u k)
  | succ d hkd ih =>
    rw [← Nat.mod_mod_of_dvd (radixPrefix b u (d+1)) (pow_dvd_pow b hkd),
      radix_prefix_step_mod hb, ih]

theorem radix_prefix_eq_iff {b : ℕ} (hb : 0 < b)
    (u v : ℕ → Fin b) (k : ℕ) :
    radixPrefix b u k = radixPrefix b v k ↔ ∀ t < k, u t = v t := by
  induction k with
  | zero => simp [radixPrefix]
  | succ k ih =>
    constructor
    · intro heq
      have hp : radixPrefix b u k = radixPrefix b v k := by
        have h := congrArg (fun x => x % b^k) heq
        simpa only [radix_prefix_step_mod hb] using h
      have hd : u k = v k := by
        apply Fin.ext
        have hbpow := pow_pos hb k
        simp only [radixPrefix, hp] at heq
        nlinarith
      intro t ht
      by_cases htk : t = k
      · simpa [htk] using hd
      · exact ih.mp hp t (by omega)
    · intro h
      simp only [radixPrefix, ih.mpr (fun t ht => h t (by omega)), h k (by omega)]

/-- Every natural residue has a full digit sequence with that prefix.
This is an existence result; it does not assume a correct digit encoder.-/
theorem radix_prefix_represents {b : ℕ} (hb : 0 < b) (a k : ℕ) :
    ∃ u : ℕ → Fin b, radixPrefix b u k = a % b^k := by
  induction k generalizing a with
  | zero => exact ⟨fun _ => ⟨0, hb⟩, by simp only [radixPrefix, pow_zero, Nat.mod_one]⟩
  | succ k ih =>
    obtain ⟨u, hu⟩ := ih a
    let digit : Fin b := ⟨(a / b^k) % b, Nat.mod_lt _ hb⟩
    let v : ℕ → Fin b := fun t => if t = k then digit else u t
    have hv : radixPrefix b v k = radixPrefix b u k :=
      (radix_prefix_eq_iff hb v u k).mpr (fun t ht => by simp [v, ht.ne])
    refine ⟨v, ?_⟩
    rw [radixPrefix, hv, hu]
    simp only [v, ↓reduceIte, digit]
    rw [pow_succ]
    exact Nat.mod_mul.symm

/-- Equality at a shared digit depth is precisely modular equality.-/
theorem radix_prefix_modEq_iff {b : ℕ} (hb : 0 < b)
    (u v : ℕ → Fin b) {k d e : ℕ} (hkd : k ≤ d) (hke : k ≤ e) :
    (radixPrefix b u d : ℤ) ≡ (radixPrefix b v e : ℤ) [ZMOD b^k] ↔
      ∀ t < k, u t = v t := by
  have hnat : radixPrefix b u d ≡ radixPrefix b v e [MOD b^k] ↔
      ∀ t < k, u t = v t := by
    rw [Nat.ModEq, radix_prefix_mod hb u hkd, radix_prefix_mod hb v hke,
      radix_prefix_eq_iff hb]
  exact_mod_cast hnat

end Erdos278
