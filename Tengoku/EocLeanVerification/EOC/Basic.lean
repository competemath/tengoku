import Tengoku.Seed.NumberTheory.Padics.PadicVal.Basic
import Tengoku.Seed.Data.Nat.Prime.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace EOC

/-- `a m = v₂(3m+1)`, the 2-adic valuation driving the accelerated map.-/
noncomputable def a (m : ℕ) : ℕ := padicValNat 2 (3 * m + 1)

/-- The accelerated Collatz map on (odd, positive) naturals.-/
noncomputable def T (m : ℕ) : ℕ := (3 * m + 1) / 2 ^ a m

/-- Lemma 3.10 (Affine closure), valuation part, **unrestricted**:
`v₂(3(4m+1)+1) = 2 + v₂(3m+1)` for every `m : ℕ`.
@isnad1 id=eq.0h1v.s5.c6ecf43efb44 from=translated src=- shape=de48ea10 vocab=4ffa8cef
-/
theorem affineClosure_val (m : ℕ) :
    a (4 * m + 1) = 2 + a m := by
  have hkey : 3 * (4 * m + 1) + 1 = 2 ^ 2 * (3 * m + 1) := by ring
  unfold a
  rw [hkey, padicValNat.mul (by norm_num) (by omega),
      padicValNat_base_pow (by norm_num) 2]

/-- Lemma 3.10 (Affine closure), map part, **unrestricted**: `T(4m+1) = T(m)`.
@isnad1 id=eq.0h1v.s5.0f81ff9ad750 from=translated src=- shape=3fae17ef vocab=47efddb3
-/
theorem affineClosure_T (m : ℕ) :
    T (4 * m + 1) = T m := by
  have hkey : 3 * (4 * m + 1) + 1 = 2 ^ 2 * (3 * m + 1) := by ring
  have hval : a (4 * m + 1) = 2 + a m := affineClosure_val m
  obtain ⟨k, hk0⟩ := (pow_padicValNat_dvd : 2 ^ a m ∣ 3 * m + 1)
  -- Force the folded form `a m` (rather than the unfolded `padicValNat 2 (3*m+1)`
  -- that `hk0` actually carries) so later `rw`s match syntactically.
  have hk : 3 * m + 1 = 2 ^ a m * k := hk0
  have hTm : T m = k := by
    unfold T
    rw [hk, Nat.mul_div_cancel_left k (by positivity)]
  have hTm' : T (4 * m + 1) = k := by
    unfold T
    rw [hkey, hval, pow_add, hk, ← mul_assoc,
        Nat.mul_div_cancel_left k (by positivity)]
  rw [hTm, hTm']

/-- **Paper-faithful restatement of Lemma 3.10**, exactly at the paper's stated
hypothesis "for every odd `m ≥ 1`." In `ℕ`, `Odd m` already forces `m ≥ 1`
(0 is even), so `Odd m` alone is the literal hypothesis.
@isnad1 id=eq.1h1v.s5.ee9abdeb685c from=translated src=- shape=ca24a2a9 vocab=238c47bb
-/
theorem affineClosure_val_odd (m : ℕ) (_hm : Odd m) :
    a (4 * m + 1) = 2 + a m :=
  affineClosure_val m

/--
@isnad1 id=eq.1h1v.s5.88a5d9a39a00 from=translated src=- shape=f5287516 vocab=50e1f40f
-/
theorem affineClosure_T_odd (m : ℕ) (_hm : Odd m) :
    T (4 * m + 1) = T m :=
  affineClosure_T m

end EOC
