import Tengoku
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.StrongWeighted
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.CpermEqC
import Tengoku.CongruencePhenomenaLean.CongruenceTheory.WeightedSpecialization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
**Theorem `thm:power-of-two`** ("Explicit power-of-two residue"). Put `α = w₁ + w₂` and
`β = w₂ + w₄`. For every integral weight sequence `w`:

* `A_w(2) ≡ α (mod 2)`,
* `A_w(4) ≡ α² + 2β (mod 4)`,
* `A_w(8) ≡ α⁴ + 4α²β + 4β² (mod 8)`,
* `A_w(2^r) ≡ α^(2^(r-1)) (mod 2^r)` for every `r ≥ 4`.

The proof uses `thm:strong` (as `AwPerm_two_adic_dynamics`) and one finite check of `A_w(4)`.
Levels `r = 3, 4` follow from the lift by finite algebra in `ZMod`, and the induction for
`r ≥ 5` uses nothing else.
-/

namespace CongruenceTheory

open Finset MvPolynomial

/-- `A_w(n+1)` by the falling-factorial recurrence, evaluated at the weights `w`.-/
lemma Aw_succ (w : ℕ → ℤ) (n : ℕ) :
    Aw w (n + 1) = ∑ r ∈ range (n + 1), fall n r * (w (r + 1) * Aw w (n - r)) := by
  unfold Aw
  rw [C_succ, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [map_mul, map_intCast]

lemma Aw_zero (w : ℕ → ℤ) : Aw w 0 = 1 := by simp [Aw, C_zero]

lemma Aw_one (w : ℕ → ℤ) : Aw w 1 = w 1 := by
  rw [Aw_succ]; simp [fall, Aw_zero]

lemma Aw_two (w : ℕ → ℤ) : Aw w 2 = w 1 ^ 2 + w 2 := by
  rw [Aw_succ]
  simp [Finset.sum_range_succ, fall, Aw_one, Aw_zero]
  ring

lemma Aw_eq_AwPerm (w : ℕ → ℤ) (n : ℕ) : Aw w n = AwPerm w n := by
  rw [Aw, AwPerm, Cperm_eq_C]

/-- `A_w(n+n)` is the `n + n`-point enumerator `AwPermSum w n`.-/
lemma Aw_two_mul_eq_AwPermSum (w : ℕ → ℤ) (n : ℕ) : Aw w (n + n) = AwPermSum w n := by
  have h : Fintype.card (Fin n ⊕ Fin n) = n + n := by simp
  rw [Aw_eq_AwPerm, AwPerm, AwPermSum, CpermSum, Cperm_eq_sum_of_card_eq h]

/-! ### The theorem -/

lemma dvd_of_zmod_zero {n : ℕ} [NeZero n] {x : ℤ} (h : ((x : ℤ) : ZMod n) = 0) :
    (n : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd x n).mp h

lemma aux_r1 (a b : ℤ) : (2 : ℤ) ∣ (a ^ 2 + b) - (a + b) := by
  have : (((a ^ 2 + b) - (a + b) : ℤ) : ZMod 2) = 0 := by
    push_cast
    generalize (a : ZMod 2) = x
    generalize (b : ZMod 2) = y
    revert x y; decide
  exact_mod_cast dvd_of_zmod_zero this

/-- Level `r = 1`: `A_w(2) ≡ w₁ + w₂ (mod 2)`.-/
theorem power_of_two_r1 (w : ℕ → ℤ) : (2 : ℤ) ∣ Aw w 2 - (w 1 + w 2) := by
  rw [Aw_two]; exact aux_r1 _ _

/-! ### Corollary: the residue is `0` or `1` -/

end CongruenceTheory
