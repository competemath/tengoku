/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
module

public import Tengoku

/-!
# LeanPool.SelbergSieve4.ForMathlib.ProdsAntidiagonal
-/

@[expose] public section

open scoped ArithmeticFunction.omega

namespace Nat

/-- Alias for the multiplicative antidiagonal indexed by `Fin d`. -/
abbrev finMulAntidiagonal (d n : ℕ) : Finset (Fin d → ℕ) :=
  finMulAntidiag d n

/-- Membership in the multiplicative antidiagonal.
@isnad1 id=iff.0h3v.s6.1d4996b4f085 from=translated src=- shape=90d8b0d9 vocab=ea85bcdd
-/
theorem mem_finMulAntidiagonal {d n : ℕ} {f : Fin d → ℕ} :
    f ∈ finMulAntidiagonal d n ↔ ∏ i, f i = n ∧ n ≠ 0 :=
  mem_finMulAntidiag

/--
@isnad1 id=eq.2h3v.s6.9c0131ff878e from=translated src=- shape=219c2036 vocab=652de101
-/
theorem finMulAntidiagonal_univ_eq {d m n : ℕ} (hmn : m ∣ n) (hn : n ≠ 0) :
    finMulAntidiagonal d m =
      (Fintype.piFinset fun _ : Fin d => n.divisors).filter (fun f => ∏ i, f i = m) :=
  finMulAntidiag_eq_piFinset_divisors_filter hmn hn

/--
@isnad1 id=eq.1h2v.s5.5be4149e0fa8 from=translated src=- shape=f7d9538f vocab=97bf67a5
-/
theorem card_finMulAntidiagonal {d n : ℕ} (hn : Squarefree n) :
    (finMulAntidiagonal d n).card = d ^ ω n := by
  simpa [finMulAntidiagonal] using card_finMulAntidiag_of_squarefree (d := d) hn

end Nat
