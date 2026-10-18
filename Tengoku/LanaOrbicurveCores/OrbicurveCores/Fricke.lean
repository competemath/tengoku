/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Trace identities in `SL(2, R)` (Fricke)

For `A, B ∈ SL(2, R)` over a commutative ring `R`, with `x = tr A`, `y = tr B`, `z = tr AB`:

* `tr A⁻¹ = tr A`, `tr (A⁻¹ B) = xy - z`, `tr (A A B) = xz - y`;
* **Fricke's identity** `tr [A, B] = x² + y² + z² - xyz - 2`
  (`OrbicurveCores.trace_commutator`); so `[A, B]` has trace `-2` (the commutator is parabolic,
  as for a once-punctured torus group) iff `x² + y² + z² = xyz`;
* `tr (Aⁿ) = Vₙ(tr A)`, where `Vₙ` (`OrbicurveCores.lucas`) is the monic integral polynomial with
  `V₀ = 2`, `V₁ = X`, `Vₙ₊₂ = X Vₙ₊₁ - Vₙ` (`OrbicurveCores.trace_pow`). This is used to show
  that traces of elements some power of which is integral are algebraic integers.
-/

open Matrix Polynomial

namespace OrbicurveCores

variable {R : Type*} [CommRing R]

local notation "SL2" => Matrix.SpecialLinearGroup (Fin 2) R

/-- The trace of an element of `SL(2, R)`. -/
abbrev tr (A : SL2) : R := trace (A : Matrix (Fin 2) (Fin 2) R)

lemma tr_def (A : SL2) : tr A = A 0 0 + A 1 1 := by
  simp [tr, trace_fin_two]

@[simp]
lemma tr_one : tr (1 : SL2) = 2 := by
  simp [tr_def]
  norm_num

/-- The polynomials `Vₙ` with `V₀ = 2`, `V₁ = X`, `Vₙ₊₂ = X Vₙ₊₁ - Vₙ`, so that
`tr (Aⁿ) = Vₙ(tr A)` for `A ∈ SL(2, R)`. -/
noncomputable def lucas : ℕ → ℤ[X]
  | 0 => 2
  | 1 => X
  | n + 2 => X * lucas (n + 1) - lucas n

lemma lucas_add_two (n : ℕ) : lucas (n + 2) = X * lucas (n + 1) - lucas n := rfl

lemma lucas_monic_natDegree (n : ℕ) :
    (lucas (n + 1)).Monic ∧ (lucas (n + 1)).natDegree = n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [lucas]
    | 1 =>
      have h : lucas 2 = X ^ 2 - C 2 := by
        simp [lucas, pow_two]
      rw [h]
      exact ⟨monic_X_pow_sub_C _ (by norm_num), natDegree_X_pow_sub_C⟩
    | m + 2 =>
      obtain ⟨hm1, hd1⟩ := ih (m + 1) (by lia)
      obtain ⟨hm0, hd0⟩ := ih m (by lia)
      have hXm : (X * lucas (m + 2)).Monic := monic_X.mul hm1
      have hXd : (X * lucas (m + 2)).natDegree = m + 3 := by
        rw [natDegree_mul monic_X.ne_zero hm1.ne_zero, hd1, natDegree_X]; ring
      have hlt : (lucas (m + 1)).degree < (X * lucas (m + 2)).degree := by
        rw [degree_eq_natDegree hm0.ne_zero, degree_eq_natDegree hXm.ne_zero, hd0, hXd]
        exact_mod_cast (by lia : m + 1 < m + 3)
      refine ⟨?_, ?_⟩
      · rw [show m + 2 + 1 = (m + 1) + 2 by ring, lucas_add_two]
        exact hXm.sub_of_left hlt
      · rw [show m + 2 + 1 = (m + 1) + 2 by ring, lucas_add_two,
          natDegree_sub_eq_left_of_natDegree_lt, hXd]
        rw [hXd, hd0]; lia

lemma lucas_monic {n : ℕ} (hn : 0 < n) : (lucas n).Monic := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  simpa using (lucas_monic_natDegree m).1

end OrbicurveCores
