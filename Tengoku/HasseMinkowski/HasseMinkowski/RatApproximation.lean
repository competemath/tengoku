/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
import Tengoku.Seed.NumberTheory.Padics.PadicNumbers
import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic
import Tengoku.Seed.Data.Nat.Cast.Field
import Tengoku.Seed.Data.Nat.ChineseRemainder
import Tengoku.Seed.Data.Rat.Lemmas
import Tengoku.Seed.Algebra.Order.Archimedean.Basic
import Tengoku.Seed.Topology.MetricSpace.Pseudo.Pi
import Tengoku.Seed.Topology.MetricSpace.Pseudo.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Weak approximation for ℚ

The weak approximation theorem for the rational numbers: a rational number can be found
arbitrarily close (simultaneously) to any prescribed real number and any finite collection of
`p`-adic numbers.  This is the arithmetic input for the high-rank Hasse–Minkowski induction.

The proof is elementary.  Fix tolerances, approximate each `p`-adic coordinate `y_p` by a
rational `c_p`, clear denominators with `D = ∏ p, (c p).den` and use the Chinese remainder
theorem to solve `r ≡ D·c_p (mod p^{m})` for a single integer `r`.  Then `x = r/D` already
matches every `p`-adic coordinate; adding an integer multiple of `N = ∏ p^{m}` (divided by `D`)
preserves the `p`-adic congruences as long as the multiplier is `p`-adically integral, and a
multiplier of the form `s / L^j` with `L` a prime outside the finite set is `p`-adically
integral for every `p` in the set while being dense in `ℝ`.  This gives the real approximation.
-/

namespace Rat

open scoped BigOperators
open scoped Function

/-- The `n`-th prime is prime, as an instance.-/
local instance fact_prime_of_primes (p : Nat.Primes) : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩

/-- The finite embedding of `ℚ` into the product of the completions of `ℚ` at a finite set of
places (which includes `ℝ`).-/
noncomputable abbrev finiteEmbedding (S : Finset Nat.Primes) (x : ℚ) : ℝ × (Π p : S, ℚ_[p]) :=
  ⟨algebraMap ℚ ℝ x, fun p ↦ (algebraMap ℚ ℚ_[p]) x⟩

/-! ### Elementary lemmas -/

-- Theorem: the norm of `p ^ k` in `ℚ_[p]` is `p ^ (-k)` (as a real number).
lemma norm_pow_eq (p : ℕ) [Fact p.Prime] (k : ℕ) :
    ‖(p : ℚ_[p]) ^ k‖ = (p : ℝ) ^ (-(k : ℤ)) := by
  rw [norm_pow, Padic.norm_p, inv_pow, ← zpow_natCast, zpow_neg]

-- Theorem: the norm of a nonzero natural number `D` in `ℚ_[p]` is `p ^ (-v_p(D))`.
lemma norm_natCast_eq (p : ℕ) [Fact p.Prime] {D : ℕ} (hD : D ≠ 0) :
    ‖(D : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p D : ℤ)) := by
  have hD' : (D : ℚ_[p]) ≠ 0 := by
    exact_mod_cast hD
  rw [Padic.norm_eq_zpow_neg_valuation hD', Padic.valuation_natCast]

-- Theorem (per-place estimate): if `D * x - n = p ^ (m + v) * w` with `(n : ℚ) = D * c`,
-- `‖D‖ = p ^ (-v)` and `‖w‖ ≤ 1`, then `‖x - c‖ ≤ p ^ (-m)`.
lemma norm_sub_le (p : ℕ) [Fact p.Prime] {D : ℕ} (hD : D ≠ 0)
    {c x : ℚ} {n : ℤ} (hn : (n : ℚ) = D * c)
    {m v : ℕ} (hv : ‖(D : ℚ_[p])‖ = (p : ℝ) ^ (-(v : ℤ)))
    {w : ℚ} (hval : D * x - n = (p : ℚ) ^ (m + v) * w)
    (hw : ‖(w : ℚ_[p])‖ ≤ 1) :
    ‖((x - c : ℚ) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(m : ℤ)) := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
  have hxc : x - c = ((D : ℚ) * x - n) / D := by
    rw [hn]
    field_simp
  have hcast : ((x - c : ℚ) : ℚ_[p]) =
      (p : ℚ_[p]) ^ (m + v) * (w : ℚ_[p]) * (D : ℚ_[p])⁻¹ := by
    rw [hxc, hval]
    push_cast
    ring
  rw [hcast, norm_mul, norm_mul, norm_pow_eq, norm_inv, hv]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hcomb : (p : ℝ) ^ (-((m + v : ℕ) : ℤ)) * (p : ℝ) ^ ((v : ℕ) : ℤ) =
      (p : ℝ) ^ (-(m : ℤ)) := by
    rw [← zpow_add₀ hp0.ne']
    congr 1
    push_cast
    ring
  calc (p : ℝ) ^ (-((m + v : ℕ) : ℤ)) * ‖(w : ℚ_[p])‖ *
        ((p : ℝ) ^ (-((v : ℕ) : ℤ)))⁻¹
      = ((p : ℝ) ^ (-((m + v : ℕ) : ℤ)) * (p : ℝ) ^ ((v : ℕ) : ℤ)) *
        ‖(w : ℚ_[p])‖ := by
        rw [show ((p : ℝ) ^ (-((v : ℕ) : ℤ)))⁻¹ = (p : ℝ) ^ ((v : ℕ) : ℤ) by
          rw [zpow_neg, inv_inv]]
        ring
    _ = (p : ℝ) ^ (-(m : ℤ)) * ‖(w : ℚ_[p])‖ := by rw [hcomb]
    _ ≤ (p : ℝ) ^ (-(m : ℤ)) * 1 := by
        exact mul_le_mul_of_nonneg_left hw (zpow_nonneg hp0.le _)
    _ = (p : ℝ) ^ (-(m : ℤ)) := mul_one _

-- Theorem (CRT): for pairwise coprime prime powers `(π i) ^ k i` and integer residues `a i`
-- there is an integer `r` congruent to `a i` modulo `(π i) ^ k i` for every `i`.
lemma exists_int_modEq {ι : Type*} (π : ι → Nat.Primes)
    (hπ : Function.Injective π) (t : Finset ι) (k : ι → ℕ) (a : ι → ℤ) :
    ∃ r : ℤ, ∀ i ∈ t, r ≡ a i [ZMOD ((π i : ℕ) : ℤ) ^ (k i)] := by
  classical
  set s : ι → ℕ := fun i ↦ (π i : ℕ) ^ k i with hs
  have hs0 : ∀ i ∈ t, s i ≠ 0 := fun i _ ↦ pow_ne_zero _ (π i).2.ne_zero
  have hpp : Set.Pairwise (↑t : Set ι) (Nat.Coprime on s) := by
    intro i _ j _ hij
    have hne : (π i : ℕ) ≠ (π j : ℕ) := fun h ↦ hij (hπ (Subtype.ext h))
    have hcop : Nat.Coprime (π i : ℕ) (π j : ℕ) :=
      (Nat.Prime.coprime_iff_not_dvd (π i).2).mpr fun hd ↦ by
        rcases (Nat.dvd_prime (π j).2).mp hd with h1 | h2
        · exact (π i).2.ne_one h1
        · exact hne h2
    exact hcop.pow (k i) (k j)
  let a' : ι → ℕ := fun i ↦ (a i % ((s i : ℕ) : ℤ)).toNat
  obtain ⟨r, hr⟩ := Nat.chineseRemainderOfFinset a' s t hs0 hpp
  refine ⟨r, fun i hi ↦ ?_⟩
  have hmod : (s i : ℤ) = ((π i : ℕ) : ℤ) ^ (k i) := by
    rw [hs]; push_cast; ring
  rw [← hmod]
  have hr' : r ≡ a' i [MOD s i] := hr i hi
  have h1 : (r : ℤ) ≡ (a' i : ℤ) [ZMOD (s i : ℤ)] := by
    simpa using (Int.natCast_modEq_iff.mpr hr')
  have hsi : (s i : ℤ) ≠ 0 := by exact_mod_cast hs0 i hi
  have h2 : (a' i : ℤ) = a i % ((s i : ℕ) : ℤ) := by
    simp only [a']
    exact Int.toNat_of_nonneg (Int.emod_nonneg _ hsi)
  have h3 : a i % ((s i : ℕ) : ℤ) ≡ a i [ZMOD (s i : ℤ)] := Int.mod_modEq _ _
  rw [h2] at h1
  exact h1.trans h3

-- Theorem: a grid of spacing `1 / L ^ j` with `L > 1` hits every real to within one step.
lemma exists_int_grid (L : ℝ) (hL : 1 < L) (u : ℝ) (j : ℕ) :
    ∃ s : ℤ, |u - (s : ℝ) / L ^ j| < 1 / L ^ j := by
  refine ⟨⌊u * L ^ j⌋, ?_⟩
  have hLj : (0 : ℝ) < L ^ j := pow_pos (by linarith) j
  have h1 : ((⌊u * L ^ j⌋ : ℤ) : ℝ) ≤ u * L ^ j := Int.floor_le _
  have h2 : u * L ^ j < ((⌊u * L ^ j⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  have h3 : |u * L ^ j - (⌊u * L ^ j⌋ : ℝ)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have heq : u - (⌊u * L ^ j⌋ : ℝ) / L ^ j =
      (u * L ^ j - (⌊u * L ^ j⌋ : ℝ)) / L ^ j := by
    field_simp
  rw [heq, abs_div, abs_of_pos hLj]
  exact div_lt_div_of_pos_right h3 hLj

-- Theorem: if `L` is a prime different from `p`, then `a + b * (c / L ^ j)` is `p`-adically
-- integral for all integers `a`, `b`, `c` and every `j`.
lemma norm_add_mul_div_le_one (p : ℕ) [Fact p.Prime] {L : ℕ} (hL : Nat.Prime L) (hpL : p ≠ L)
    (a : ℤ) (b : ℕ) (c : ℤ) (j : ℕ) :
    ‖(((a : ℚ) + (b : ℚ) * ((c : ℚ) / (L : ℚ) ^ j) : ℚ) : ℚ_[p])‖ ≤ 1 := by
  have hnot : ¬ p ∣ L := by
    intro hd
    rcases (Nat.dvd_prime hL).mp hd with h1 | h2
    · exact (Fact.out : Nat.Prime p).ne_one h1
    · exact hpL h2
  have hLn : ‖(L : ℚ_[p])‖ = 1 := by
    rw [show (L : ℚ_[p]) = ((L : ℚ) : ℚ_[p]) by norm_cast, Padic.eq_padicNorm]
    exact_mod_cast (padicNorm.nat_eq_one_iff L).mpr hnot
  have ha : ‖(a : ℚ_[p])‖ ≤ 1 := by
    rw [show (a : ℚ_[p]) = ((a : ℚ) : ℚ_[p]) by norm_cast, Padic.eq_padicNorm]
    exact_mod_cast (padicNorm.of_int a)
  have hb : ‖(b : ℚ_[p])‖ ≤ 1 := by
    rw [show (b : ℚ_[p]) = ((b : ℚ) : ℚ_[p]) by norm_cast, Padic.eq_padicNorm]
    exact_mod_cast (padicNorm.of_nat b)
  have hc : ‖(c : ℚ_[p])‖ ≤ 1 := by
    rw [show (c : ℚ_[p]) = ((c : ℚ) : ℚ_[p]) by norm_cast, Padic.eq_padicNorm]
    exact_mod_cast (padicNorm.of_int c)
  have hcl : ‖(c : ℚ_[p]) / (L : ℚ_[p]) ^ j‖ ≤ 1 := by
    rw [norm_div, norm_pow, hLn, one_pow, div_one]
    exact hc
  rw [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  refine (Padic.nonarchimedean _ _).trans (max_le ha ?_)
  rw [norm_mul]
  calc ‖(b : ℚ_[p])‖ * ‖(c : ℚ_[p]) / (L : ℚ_[p]) ^ j‖ ≤ 1 * 1 :=
        mul_le_mul hb hcl (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num

/-! ### Weak approximation -/

end Rat
