import Tengoku.HallRay.HallRay.ContinuedFraction.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Lagrange spectrum

The two-sided continued-fraction presentation of the Lagrange spectrum.

Planned contents:

* positive-integer sequences indexed by `ℤ`;
* the local value `λ_i`;
* the Lagrange value defined by a limsup;
* the Lagrange spectrum `L`.
-/

namespace HallRay
namespace Lagrange

open ContinuedFraction

/-- A two-sided sequence of positive partial quotients.-/
abbrev BiSequence := ℤ → PartialQuotient

/-- Partial quotients to the right of position `i`.-/
def rightDigits (A : BiSequence) (i : ℤ) (n : ℕ) : PartialQuotient :=
  A (i + (n + 1 : ℕ))

/-- Partial quotients to the left of position `i`, read in reverse order.-/
def leftDigits (A : BiSequence) (i : ℤ) (n : ℕ) : PartialQuotient :=
  A (i - (n + 1 : ℕ))

/--
The local Lagrange value

`λᵢ(A) = [aᵢ; aᵢ₊₁, ...] + [0; aᵢ₋₁, ...]`.-/
noncomputable def lambda (A : BiSequence) (i : ℤ) : ℝ :=
  value (A i).1 (rightDigits A i) + value 0 (leftDigits A i)

/-- The local value split into its central partial quotient and two
fractional tails.
@isnad1 id=eq.0h2v.s5.833bfc549620 from=translated src=- shape=e1d8d19e vocab=9c53aa40
-/
theorem lambda_eq_center_add_tails (A : BiSequence) (i : ℤ) :
    lambda A i =
      (A i).1 + value 0 (rightDigits A i) + value 0 (leftDigits A i) := by
  rw [lambda, value_eq_head_add]

/-- Uniform elementary bounds for a local Lagrange value.
@isnad1 id=mem.0h2v.s6.a0afba5625a6 from=translated src=- shape=31326f35 vocab=6694e484
-/
theorem lambda_mem_Icc (A : BiSequence) (i : ℤ) :
    lambda A i ∈ Set.Icc ((A i).1 : ℝ) ((A i).1 + 2) := by
  rw [lambda_eq_center_add_tails]
  rcases value_zero_mem_Icc (rightDigits A i) with ⟨hr0, hr1⟩
  rcases value_zero_mem_Icc (leftDigits A i) with ⟨hl0, hl1⟩
  constructor <;> linarith

/-- A bound on all partial quotients gives a bound on all local values.
@isnad1 id=le.1h3v.s5.f1b821ccfd30 from=translated src=- shape=5b9ee449 vocab=a711bed9
-/
theorem lambda_le_of_digits_le (A : BiSequence) {M : ℝ}
    (hA : ∀ i, ((A i).1 : ℝ) ≤ M) (i : ℤ) :
    lambda A i ≤ M + 2 := by
  exact (lambda_mem_Icc A i).2.trans (by linarith [hA i])

/-- Local Lagrange values are bounded below, hence are cobounded in the
sense required by the conditionally-complete `limsup` API.
@isnad1 id=iscoboun.0h1v.s4.3c07023b09a8 from=translated src=- shape=6013013f vocab=13a697e3
-/
theorem lambda_isCobounded (A : BiSequence) :
    Filter.IsCoboundedUnder LE.le Filter.atTop
      (fun n : ℕ ↦ lambda A n) := by
  have hrange : BddBelow (Set.range fun n : ℕ ↦ lambda A n) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hcenter : (1 : ℝ) ≤ (A (n : ℤ)).1 := one_le_partialQuotient _
    exact hcenter.trans (lambda_mem_Icc A n).1
  exact (hrange.isBoundedUnder_of_range (f := Filter.atTop)).isCoboundedUnder_flip

/-- The Lagrange value `limsup_{i → ∞} λᵢ(A)`.-/
noncomputable def lagrangeValue (A : BiSequence) : ℝ :=
  Filter.limsup (fun n : ℕ ↦ lambda A n) Filter.atTop

/--
The Lagrange spectrum in its two-sided continued-fraction presentation.

The boundedness condition expresses the finiteness requirement on the
limsup in Definition 1 of `doc/main.tex`.-/
def spectrum : Set ℝ :=
  {ell | ∃ A : BiSequence,
    Filter.IsBoundedUnder LE.le Filter.atTop (fun n : ℕ ↦ lambda A n) ∧
      ell = lagrangeValue A}

end Lagrange
end HallRay
