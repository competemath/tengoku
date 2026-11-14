import Tengoku.Twinprime.TwinPrime.Analytic.CharacterTrivialBounds
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterConductor
import Tengoku.Twinprime.TwinPrime.Analytic.ConductorAbel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From a primitive-character mean to a large-conductor tail

At a primitive modulus greater than one, the centered and uncentered
maxima agree. This identifies the conductor tail with the reciprocal
weight of the uncentered primitive-character mean. The final theorem is
an exact finite bridge from an explicitly supplied quadratic mean bound;
it does not establish that mean bound or a distribution theorem.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- Centering disappears for primitive characters only above modulus one.
@isnad1 id=eq.1h2v.s6.c8fd8ba37ee1 from=translated src=- shape=c0604666 vocab=58b8314b
-/
theorem primitiveCharacterMass_eq_sum_characterPsiMax (T r : ℕ) (hr : 1 < r) :
    primitiveCharacterMass T r =
      ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
        characterPsiMax T χ := by
  unfold primitiveCharacterMass
  apply sum_congr rfl
  intro χ hχ
  exact primitive_characterMaxError_eq_characterPsiMax hr T χ (mem_filter.mp hχ).2

/-- The uncentered primitive-character mean weight at one modulus.-/
def primitiveCharacterPsiWeight (T r : ℕ) : ℝ :=
  (r : ℝ) / Nat.totient r *
    ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
      characterPsiMax T χ

/--
@isnad1 id=le.0h2v.s4.fe8ebc5f9d2a from=translated src=- shape=5ffe46ab vocab=5a4fe606
-/
theorem primitiveCharacterPsiWeight_nonneg (T r : ℕ) :
    0 ≤ primitiveCharacterPsiWeight T r := by
  unfold primitiveCharacterPsiWeight
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg _))
    (sum_nonneg fun χ _ => characterPsiMax_nonneg T χ)

/-- The cumulative coefficient sum is exactly the actual weighted mean,
including its uncentered modulus-one contribution.
@isnad1 id=eq.0h2v.s7.715aee19fd76 from=translated src=- shape=b8d18003 vocab=461caef2
-/
theorem coefficientSum_primitiveCharacterPsiWeight (T R : ℕ) :
    coefficientSum (primitiveCharacterPsiWeight T) R =
      ∑ r ∈ Icc 1 R, (r : ℝ) / Nat.totient r *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive),
          characterPsiMax T χ := by
  have hI : Ioc 0 R = Icc 1 R := by
    ext r
    simp only [mem_Ioc, mem_Icc]
    omega
  simp only [coefficientSum, primitiveCharacterPsiWeight, hI]

/-- Dividing the mean weight by a positive nonprincipal modulus recovers
the centered mass divided by its totient.
@isnad1 id=eq.1h2v.s5.c0cfc5d66528 from=translated src=- shape=57ed9320 vocab=536f2f18
-/
theorem primitiveCharacterPsiWeight_div_eq (T r : ℕ) (hr : 1 < r) :
    primitiveCharacterPsiWeight T r / r = primitiveCharacterMass T r / Nat.totient r := by
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_of_lt hr).ne'
  rw [primitiveCharacterPsiWeight, primitiveCharacterMass_eq_sum_characterPsiMax T r hr]
  field_simp

/-- A quadratic bound for the actual primitive-character mean yields the
large-conductor tail. The cutoff excludes the centered conductor-one term,
and the cumulative hypothesis is required only between the two endpoints.
@isnad1 id=le.6h6v.s8.2e7d9c8172b3 from=translated src=- shape=6273d4d5 vocab=01347288
-/
theorem sum_primitiveCharacterMass_div_totient_le_of_quadratic_mean
    (T R₀ Q : ℕ) (hR₀ : 1 ≤ R₀) (hRQ : R₀ ≤ Q) (A B D : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hmean : ∀ r ∈ Icc R₀ Q,
      (∑ q ∈ Icc 1 r, (q : ℝ) / Nat.totient q *
        ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
          characterPsiMax T χ) ≤ A + B * r + D * (r : ℝ) ^ 2) :
    (∑ r ∈ Ioc R₀ Q, primitiveCharacterMass T r / Nat.totient r) ≤
      A / R₀ + B * (1 + Real.log ((Q : ℝ) / R₀)) + 2 * D * Q := by
  have hS : ∀ r ∈ Icc R₀ Q,
      coefficientSum (primitiveCharacterPsiWeight T) r ≤ A + B * r + D * (r : ℝ) ^ 2 := by
    intro r hr
    rw [coefficientSum_primitiveCharacterPsiWeight]
    exact hmean r hr
  calc
    _ = ∑ r ∈ Ioc R₀ Q, primitiveCharacterPsiWeight T r / r := by
      apply sum_congr rfl
      intro r hr
      exact (primitiveCharacterPsiWeight_div_eq T r (hR₀.trans_lt (mem_Ioc.mp hr).1)).symm
    _ ≤ _ := sum_Ioc_div_le_of_cumulative_quadratic (primitiveCharacterPsiWeight T)
      (primitiveCharacterPsiWeight_nonneg T) R₀ Q hR₀ hRQ A B D hA hB hD hS

end TwinPrime.Analytic
