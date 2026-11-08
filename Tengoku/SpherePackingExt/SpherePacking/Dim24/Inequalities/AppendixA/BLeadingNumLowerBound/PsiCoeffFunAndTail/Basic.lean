module
public import Tengoku.SpherePackingExt.SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.Basic
import Tengoku.SpherePackingExt.SpherePacking.Dim24.Inequalities.AppendixA.BLeadingNumLowerBound.PsiRSeriesSetup.SparseCoeffs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
### Convolution tools for `psiCoeffFun`

This file defines the "shift by one" operation `shift1Fun` on coefficient functions `ℕ → ℤ` and
proves the corresponding identity on `rseries`. It also records basic algebraic facts about
`powConvZ` (power via repeated `convZ`) and polynomial growth bounds for the resulting coefficients.
-/

open scoped BigOperators

noncomputable section

namespace SpherePacking.Dim24.AppendixA

/-! ## Shift and `rseries` -/

/-- Shift a coefficient function by one place: `shift1Fun a 0 = 0` and `shift1Fun a (n+1) = a n`.-/
@[expose] public def shift1Fun (a : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => a n

lemma convZ_eq_sum_range (a b : ℕ → ℤ) (n : ℕ) :
    convZ a b n = ∑ k ∈ Finset.range (n + 1), a k * b (n - k) := by
  simpa [convZ, Nat.succ_eq_add_one] using
    (Finset.Nat.sum_antidiagonal_eq_sum_range_succ (f := fun i j => a i * b j) n)

lemma convZ_oneCoeffFun_left (a : ℕ → ℤ) (n : ℕ) : convZ oneCoeffFun a n = a n := by
  rw [convZ_eq_sum_range]
  have h0 : 0 ∈ Finset.range (n + 1) := by simp
  refine
    (Finset.sum_eq_single_of_mem (s := Finset.range (n + 1))
      (f := fun k : ℕ => oneCoeffFun k * a (n - k)) (a := 0) h0 ?_).trans ?_
  · intro k hk hkne
    have hk0 : k ≠ 0 := hkne
    simp [oneCoeffFun, hk0]
  · simp [oneCoeffFun]

end SpherePacking.Dim24.AppendixA
