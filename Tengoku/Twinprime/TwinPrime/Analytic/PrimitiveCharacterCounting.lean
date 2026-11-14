import Tengoku.Twinprime.TwinPrime.Analytic.CharacterBilinear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite weighted counts of primitive characters

The exact cardinality of all complex Dirichlet characters bounds the
primitive subset. Its weight `q/φ(q)` leaves at most `q` at each positive
modulus. These finite counts turn pointwise character bounds into first
moments without any distribution assumption.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- The exact character count, specialized to complex-valued characters.-/
theorem card_dirichletCharacter_eq_totient (q : ℕ) (hq : 0 < q) :
    Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  simpa only [Nat.card_eq_fintype_card] using
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q

/-- Primitive characters form a subset of the `φ(q)` complex characters.-/
theorem card_primitiveCharacters_le_totient (q : ℕ) (hq : 0 < q) :
    ((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive)).card ≤
      Nat.totient q := by
  calc
    _ ≤ Fintype.card (DirichletCharacter ℂ q) := by
      simpa only [card_univ] using
        card_filter_le univ (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
    _ = _ := card_dirichletCharacter_eq_totient q hq

/-- The weighted primitive count is at most the modulus.-/
theorem weighted_primitive_count_le (q : ℕ) (hq : 0 < q) :
    (q : ℝ) / Nat.totient q *
      (((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive)).card : ℝ) ≤
        (q : ℝ) := by
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  calc
    _ ≤ (q : ℝ) / Nat.totient q * Nat.totient q :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast card_primitiveCharacters_le_totient q hq)
        (by positivity)
    _ = _ := by field_simp

/-- A nonnegative pointwise budget yields a weighted mean at one positive modulus.-/
theorem weighted_sum_primitive_le (q : ℕ) (hq : 0 < q)
    (F : DirichletCharacter ℂ q → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hF : ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → F χ ≤ A) :
    (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), F χ) ≤
        (q : ℝ) * A := by
  calc
    _ ≤ (q : ℝ) / Nat.totient q *
        (∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), A) :=
      mul_le_mul_of_nonneg_left (sum_le_sum fun χ hχ => hF χ (mem_filter.mp hχ).2)
        (by positivity)
    _ = ((q : ℝ) / Nat.totient q *
        (((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive)).card : ℝ)) * A := by
      simp only [sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (weighted_primitive_count_le q hq) hA

/-- Sum modulus-dependent budgets over the nontrivial modulus range.-/
theorem sum_weighted_primitive_le_sum_budget (R : ℕ)
    (F : (q : ℕ) → DirichletCharacter ℂ q → ℝ) (A : ℕ → ℝ)
    (hA : ∀ q ∈ Icc 2 R, 0 ≤ A q)
    (hF : ∀ q ∈ Icc 2 R, ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → F q χ ≤ A q) :
    (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), F q χ)) ≤
        ∑ q ∈ Icc 2 R, (q : ℝ) * A q := by
  apply sum_le_sum
  intro q hq
  exact weighted_sum_primitive_le q (by have := (mem_Icc.mp hq).1; omega)
    (F q) (A q) (hA q hq) (hF q hq)

/-- A convenient elementary square budget for the sum of the moduli.-/
theorem sum_modulus_Icc_two_le_sq (R : ℕ) :
    (∑ q ∈ Icc 2 R, (q : ℝ)) ≤ (R : ℝ) ^ 2 := by
  have hcard : (Icc 2 R).card ≤ R := by
    rw [Nat.card_Icc]
    omega
  calc
    _ ≤ ∑ _q ∈ Icc 2 R, (R : ℝ) :=
      sum_le_sum fun q hq => by exact_mod_cast (mem_Icc.mp hq).2
    _ = ((Icc 2 R).card : ℝ) * R := by simp
    _ ≤ (R : ℝ) * R := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)
    _ = _ := by ring

/-- A common nonnegative budget costs at most `R²` over the primitive family.-/
theorem sum_weighted_primitive_le_const (R : ℕ)
    (F : (q : ℕ) → DirichletCharacter ℂ q → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hF : ∀ q ∈ Icc 2 R, ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → F q χ ≤ A) :
    (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
      (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), F q χ)) ≤
        (R : ℝ) ^ 2 * A := by
  calc
    _ ≤ ∑ q ∈ Icc 2 R, (q : ℝ) * A :=
      sum_weighted_primitive_le_sum_budget R F (fun _ => A) (fun _ _ => hA) hF
    _ = (∑ q ∈ Icc 2 R, (q : ℝ)) * A := (sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_modulus_Icc_two_le_sq R) hA

/-- The weighted primitive cardinalities have total at most `R²`.-/
theorem sum_weighted_primitive_card_le_sq (R : ℕ) :
    (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
      (((univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive)).card : ℝ)) ≤
        (R : ℝ) ^ 2 := by
  apply (sum_le_sum (fun q hq => weighted_primitive_count_le q
    (by have := (mem_Icc.mp hq).1; omega))).trans
  exact sum_modulus_Icc_two_le_sq R

/-- The same count written as a sum of unit budgets over primitive characters.-/
theorem sum_weighted_primitive_count_le_sq (R : ℕ) :
    (∑ q ∈ Icc 2 R, (q : ℝ) / Nat.totient q *
      (∑ _χ ∈ (univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => χ.IsPrimitive), (1 : ℝ))) ≤
        (R : ℝ) ^ 2 := by
  simpa only [sum_const, nsmul_eq_mul, mul_one] using sum_weighted_primitive_card_le_sq R

/-- The scalar Pólya--Vinogradov budget summed over moduli; empty ranges are included.-/
theorem sum_modulus_sqrt_log_le (R : ℕ) :
    (∑ q ∈ Icc 2 R, (q : ℝ) * Real.sqrt q * (1 + Real.log q)) ≤
      (R : ℝ) ^ 2 * Real.sqrt R * (1 + Real.log R) := by
  have hR : 0 ≤ Real.sqrt R * (1 + Real.log R) := by
    have := Real.log_natCast_nonneg R
    positivity
  calc
    _ ≤ ∑ q ∈ Icc 2 R, (q : ℝ) * (Real.sqrt R * (1 + Real.log R)) := by
      apply sum_le_sum
      intro q hq
      have hq0 : (0 : ℝ) < q := by
        exact_mod_cast (show 0 < q by have := (mem_Icc.mp hq).1; omega)
      have hqR : (q : ℝ) ≤ R := by exact_mod_cast (mem_Icc.mp hq).2
      have hlog : Real.log (q : ℝ) ≤ Real.log R := Real.log_le_log hq0 hqR
      have hqlog := Real.log_natCast_nonneg q
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hq0.le
      exact mul_le_mul (Real.sqrt_le_sqrt hqR) (by linarith)
        (by linarith) (Real.sqrt_nonneg _)
    _ = (∑ q ∈ Icc 2 R, (q : ℝ)) * (Real.sqrt R * (1 + Real.log R)) := (sum_mul _ _ _).symm
    _ ≤ (R : ℝ) ^ 2 * (Real.sqrt R * (1 + Real.log R)) :=
      mul_le_mul_of_nonneg_right (sum_modulus_Icc_two_le_sq R) hR
    _ = _ := by ring

end TwinPrime.Analytic
