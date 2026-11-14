import Tengoku.Twinprime.TwinPrime.Analytic.PrimitiveCharacterCounting
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterConductor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A finite small-conductor bound from a uniform centered input

The number of primitive characters at a positive modulus is at most its
totient. A common bound for their centered maxima therefore gives one
copy of that bound per conductor. The final sum is clipped at the actual
modulus limit and includes empty ranges. The common bound is an explicit
hypothesis; no Siegel--Walfisz estimate is proved here.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- At a positive conductor, exact character counting cancels the totient
denominator in a uniform centered-character bound.-/
theorem primitiveCharacterMass_div_totient_le (T r : ℕ) (hr : 0 < r)
    (E : ℝ) (hE : 0 ≤ E)
    (hχ : ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive → characterMaxError T χ ≤ E) :
    primitiveCharacterMass T r / Nat.totient r ≤ E := by
  have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr
  apply (div_le_iff₀ hφ).mpr
  calc
    _ ≤ ∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive), E := by
      unfold primitiveCharacterMass
      exact sum_le_sum fun χ hmem => hχ χ (mem_filter.mp hmem).2
    _ = (((univ : Finset (DirichletCharacter ℂ r)).filter
        (fun χ => χ.IsPrimitive)).card : ℝ) * E := by simp
    _ ≤ (Nat.totient r : ℝ) * E :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_primitiveCharacters_le_totient r hr) hE
    _ = _ := mul_comm _ _

/-- A uniform bound on all primitive centered maxima through `R₀` controls
the small-conductor sum at every modulus limit, including zero cutoffs.-/
theorem sum_small_primitiveCharacterMass_le (T R₀ Q : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hsmall : ∀ r ∈ Icc 1 R₀, ∀ χ : DirichletCharacter ℂ r,
      χ.IsPrimitive → characterMaxError T χ ≤ E) :
    (∑ r ∈ Icc 1 (min R₀ Q), primitiveCharacterMass T r / Nat.totient r) ≤
      (R₀ : ℝ) * E := by
  have hcard : (Icc 1 (min R₀ Q)).card ≤ R₀ := by
    simp only [Nat.card_Icc]
    omega
  calc
    _ ≤ ∑ _r ∈ Icc 1 (min R₀ Q), E := by
      apply sum_le_sum
      intro r hr
      have hrpos : 0 < r := (mem_Icc.mp hr).1
      have hrR : r ∈ Icc 1 R₀ :=
        mem_Icc.mpr ⟨(mem_Icc.mp hr).1, (mem_Icc.mp hr).2.trans (min_le_left _ _)⟩
      exact primitiveCharacterMass_div_totient_le T r hrpos E hE (hsmall r hrR)
    _ = ((Icc 1 (min R₀ Q)).card : ℝ) * E := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hE

end TwinPrime.Analytic
