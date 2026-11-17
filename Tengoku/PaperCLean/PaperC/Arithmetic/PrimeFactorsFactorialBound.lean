import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Data.Finset.Sort
import Tengoku.Seed.Data.Nat.Factorization.Basic
import Tengoku.Seed.Data.Nat.Factorial.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A factorial bound for the number of distinct prime factors

The elementary inequality

`(#{p : p ∣ n})! ≤ n`

is strong enough to recover every fixed-base reciprocal-power consequence
normally deduced from the classical estimate
`ω(n) = O(log n / log log n)`.  The advantage of this formulation is that
Mathlib already proves that a factorial eventually dominates every fixed
exponential.
-/

namespace PaperC
namespace PrimeFactorsFactorialBound

open scoped BigOperators Nat

/--
Maximum of `ω(n)` over the finite polynomial-height box `0 ≤ n ≤ X^E`.-/
noncomputable def polynomialHeightOmega
    (X E : ℕ) : ℕ := by
  classical
  let values :=
    (Finset.range (X ^ E + 1)).image
      (fun n : ℕ ↦ n.primeFactors.card)
  exact values.max' <| by
    refine ⟨0, ?_⟩
    exact Finset.mem_image.mpr
      ⟨0, by simp, by simp⟩

/-- Every integer in the polynomial-height box is controlled by its maximum.
@isnad1 id=le.1h3v.s5.66202437bc70 from=translated src=- shape=80c1a00d vocab=72bc1156
-/
theorem primeFactors_card_le_polynomialHeightOmega
    {X E n : ℕ} (hn : n ≤ X ^ E) :
    n.primeFactors.card ≤ polynomialHeightOmega X E := by
  classical
  let values :=
    (Finset.range (X ^ E + 1)).image
      (fun q : ℕ ↦ q.primeFactors.card)
  have hnonempty : values.Nonempty := by
    refine ⟨0, ?_⟩
    exact Finset.mem_image.mpr
      ⟨0, by simp, by simp⟩
  change n.primeFactors.card ≤ values.max' hnonempty
  apply Finset.le_max'
  exact Finset.mem_image.mpr
    ⟨n, Finset.mem_range.mpr (by omega), rfl⟩

/-- A witness realizes the polynomial-height maximum.
@isnad1 id=ex.0h2v.s5.74cd89400ea9 from=translated src=- shape=d01c47f1 vocab=72bc1156
-/
theorem exists_primeFactors_card_eq_polynomialHeightOmega
    (X E : ℕ) :
    ∃ n ≤ X ^ E,
      n.primeFactors.card = polynomialHeightOmega X E := by
  classical
  let values :=
    (Finset.range (X ^ E + 1)).image
      (fun q : ℕ ↦ q.primeFactors.card)
  have hnonempty : values.Nonempty := by
    refine ⟨0, ?_⟩
    exact Finset.mem_image.mpr
      ⟨0, by simp, by simp⟩
  have hmem :
      values.max' hnonempty ∈ values :=
    Finset.max'_mem values hnonempty
  obtain ⟨n, hn, heq⟩ :=
    Finset.mem_image.mp hmem
  refine ⟨n, ?_, ?_⟩
  · exact Nat.le_of_lt_succ
      (Finset.mem_range.mp hn)
  · change n.primeFactors.card =
      values.max' hnonempty
    exact heq

/--
The worst distinct-prime-factor count is monotone under inclusion of the
underlying polynomial-height boxes.
@isnad1 id=le.1h4v.s5.ca40626a1af4 from=translated src=- shape=beec6bc6 vocab=a79b28fb
-/
theorem polynomialHeightOmega_mono_of_pow_le
    {X E Y F : ℕ} (hbox : X ^ E ≤ Y ^ F) :
    polynomialHeightOmega X E ≤
      polynomialHeightOmega Y F := by
  obtain ⟨n, hn, homega⟩ :=
    exists_primeFactors_card_eq_polynomialHeightOmega X E
  rw [← homega]
  exact
    primeFactors_card_le_polynomialHeightOmega
      (hn.trans hbox)

end PrimeFactorsFactorialBound
end PaperC
