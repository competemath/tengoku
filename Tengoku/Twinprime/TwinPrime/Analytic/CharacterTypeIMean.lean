import Tengoku.Twinprime.TwinPrime.Analytic.CharacterTypeIBounds
import Tengoku.Twinprime.TwinPrime.Analytic.PrimitiveCharacterCounting
import Tengoku.Twinprime.TwinPrime.Analytic.CharacterVaughanMean

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite Vaughan first moments for primitive characters

Exact character counts and the primitive interval bounds control the two
Type I maxima over moduli at least two. The low term has a constant budget.
Modulus one is bounded separately by `T log T`. Combining these bounds with
the proved Type II mean gives an explicit uncentered character mean value.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/--
@isnad1 id=le.0h3v.s7.92c8708aec4c from=translated src=- shape=945dda05 vocab=e7c432ba
-/
theorem primitive_character_vaughanI1_maximal_mean_le (R U T : ℕ) :
    (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterVaughanI1Max U T χ)) ≤
      2 * (U : ℝ) * (R : ℝ) ^ 2 * Real.sqrt R * (1 + Real.log R) * Real.log T := by
  have hT := Real.log_natCast_nonneg T
  have h := sum_weighted_primitive_le_sum_budget R (fun _ χ => characterVaughanI1Max U T χ)
    (fun q => 2 * (U : ℝ) * Real.sqrt q * (1 + Real.log q) * Real.log T)
    (fun q _ => by have := Real.log_natCast_nonneg q; positivity)
    (fun q hq χ hχ => characterVaughanI1Max_le
      (by have := (mem_Icc.mp hq).1; omega) U T χ hχ)
  calc
    _ ≤ ∑ q ∈ Icc 2 R, (q : ℝ) *
        (2 * (U : ℝ) * Real.sqrt q * (1 + Real.log q) * Real.log T) := h
    _ = (2 * (U : ℝ) * Real.log T) *
        (∑ q ∈ Icc 2 R, (q : ℝ) * Real.sqrt q * (1 + Real.log q)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ (2 * (U : ℝ) * Real.log T) *
        ((R : ℝ) ^ 2 * Real.sqrt R * (1 + Real.log R)) :=
      mul_le_mul_of_nonneg_left (sum_modulus_sqrt_log_le R) (by positivity)
    _ = _ := by ring

/--
@isnad1 id=le.0h4v.s7.19466835c76d from=translated src=- shape=f7da556a vocab=81b007cb
-/
theorem primitive_character_vaughanI2_maximal_mean_le (R U V T : ℕ) :
    (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        characterVaughanI2Max U V T χ)) ≤
      ((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ) *
        (R : ℝ) ^ 2 * Real.sqrt R * (1 + Real.log R) := by
  have hUV := Real.log_natCast_nonneg (U * V)
  have h := sum_weighted_primitive_le_sum_budget R (fun _ χ => characterVaughanI2Max U V T χ)
    (fun q => ((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ) * Real.sqrt q * (1 + Real.log q))
    (fun q _ => by have := Real.log_natCast_nonneg q; positivity)
    (fun q hq χ hχ => characterVaughanI2Max_le
      (by have := (mem_Icc.mp hq).1; omega) U V T χ hχ)
  calc
    _ ≤ ∑ q ∈ Icc 2 R, (q : ℝ) *
        (((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ) * Real.sqrt q * (1 + Real.log q)) := h
    _ = (((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ)) *
        (∑ q ∈ Icc 2 R, (q : ℝ) * Real.sqrt q * (1 + Real.log q)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring
    _ ≤ (((U * V : ℕ) : ℝ) * Real.log (U * V : ℕ)) *
        ((R : ℝ) ^ 2 * Real.sqrt R * (1 + Real.log R)) :=
      mul_le_mul_of_nonneg_left (sum_modulus_sqrt_log_le R) (by positivity)
    _ = _ := by ring

/-- The low von Mangoldt term's common budget, averaged over primitive characters.
@isnad1 id=le.0h2v.s7.6352962f98f1 from=translated src=- shape=0120bd8f vocab=d728c240
-/
theorem primitive_character_low_mean_le (R V : ℕ) :
    (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
      (∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive),
        (V : ℝ) * Real.log V)) ≤ (V : ℝ) * Real.log V * (R : ℝ) ^ 2 := by
  have hV := Real.log_natCast_nonneg V
  have h := sum_weighted_primitive_le_const R (fun _ _ => (V : ℝ) * Real.log V)
    ((V : ℝ) * Real.log V) (by positivity) (fun _ _ _ _ => le_rfl)
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

/-- Separate the positive-modulus interval at one, including the empty range.
@isnad1 id=le.1h2v.s6.0b468677cc8d from=translated src=- shape=68f1d7eb vocab=8a8f060c
-/
theorem sum_Icc_one_le_first_add_sum_Icc_two (R : ℕ) (f : ℕ → ℝ) (hf : 0 ≤ f 1) :
    (∑ q ∈ Icc 1 R, f q) ≤ f 1 + ∑ q ∈ Icc 2 R, f q := by
  by_cases hR : R = 0
  · subst R
    simpa using hf
  · have hI : Icc 1 R = insert 1 (Icc 2 R) := by
      ext q
      simp only [mem_Icc, mem_insert]
      omega
    rw [hI, sum_insert (by simp)]

end TwinPrime.Analytic
