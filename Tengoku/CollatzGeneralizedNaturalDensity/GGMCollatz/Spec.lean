import Tengoku.CollatzGeneralizedNaturalDensity.GGMCollatz.Statement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Specification tests for the definitions (worked example `(3, 4, [2, 1])`)

Checks with `decide` (`decide +kernel` for `S`) that the top-level definitions take the intended values (early
detection of vacuous or wrong statements). `native_decide` is not used. `C(1) = 4·1 + 2 = 6`, `C(6) = 2`, `C~(1) = 6/3 = 2`, `S(1) = 6/3 = 2`, `S(2) = (8 + 1)/9 = 1`,
`C(2) = 4·2 + 1 = 9`, `C(7) = 30`, `S(7) = 30/3 = 10`.
-/

namespace GGMCollatz

open Family

/-! The three examples for `S` used to be checked with `native_decide` (which adds the axiom `Lean.ofReduceBool`,
trusting the compiled evaluator). After a referee pointed this out, they were replaced by `decide +kernel`, which checks
them by kernel reduction (no additional axioms). Plain `decide` does not work: the `padicValNat` inside `S` is defined in
Mathlib via `Nat.maxPowDvdDiv.go` (well-founded recursion, `termination_by n / p`), and definitions by well-founded
recursion are not unfolded by the elaborator's reduction (they are treated as irreducible), so the `Decidable` instance
gets stuck before reducing to `isTrue`/`isFalse` (raising `set_option maxRecDepth` does not help). The kernel can unfold
`WellFounded.fix`, so `decide +kernel` closes these goals immediately for small values. -/

/-! ### Values of `C_min`, and non-vacuity of the left-hand side of (A) (proofs taken from an independent review
of the statements)

Every orbit of the worked example `(3, 4, [2, 1])` enters the cycle with minimum 1 or the cycle with minimum 7;
7 is a periodic point of period 16. -/

/--
@isnad1 id=isperiod.0h0v.s3.16bcc90b6565 from=translated src=- shape=549de884 vocab=619a2bcd
-/
theorem per7 : Function.IsPeriodicPt example34.C 16 7 := by
  unfold Function.IsPeriodicPt Function.IsFixedPt; decide

/--
@isnad1 id=le.0h1v.s4.c0290547c5e5 from=translated src=- shape=2228bc53 vocab=ea0b64fa
-/
theorem orb7 (k : ℕ) : 7 ≤ example34.C^[k] 7 := by
  rw [← per7.iterate_mod_apply k]
  have hk : k % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have h : ∀ j < 16, 7 ≤ example34.C^[j] 7 := by decide
  exact h _ hk

/--
@isnad1 id=eq.0h0v.s3.4e7113673477 from=translated src=- shape=904d2e91 vocab=b2490ffb
-/
theorem cmin7 : example34.Cmin 7 = 7 := by
  unfold Family.Cmin
  apply le_antisymm
  · exact Nat.sInf_le ⟨0, rfl⟩
  · apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨k, rfl⟩
    exact orb7 k

/--
@isnad1 id=eq.0h0v.s3.f84de3f36d76 from=translated src=- shape=904d2e91 vocab=b2490ffb
-/
theorem cmin5 : example34.Cmin 5 = 5 := by
  unfold Family.Cmin
  apply le_antisymm
  · exact Nat.sInf_le ⟨0, rfl⟩
  · apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨k, rfl⟩
    show 5 ≤ example34.C^[k] 5
    rcases Nat.lt_or_ge k 2 with hk | hk
    · interval_cases k <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
      rw [Function.iterate_add_apply, show example34.C^[2] 5 = 7 by decide]
      have := orb7 m
      omega

/--
@isnad1 id=le.0h0v.s3.56e9b1b3dcc2 from=translated src=- shape=904d2e91 vocab=f45e87ca
-/
theorem cmin4 : example34.Cmin 4 ≤ 1 := Nat.sInf_le ⟨6, by decide⟩

end GGMCollatz
