import Tengoku.Twinprime.TwinPrime.Analytic.LFunctionZeroValue
import Tengoku.Seed.Algebra.Order.Field.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Uniform nonvanishing constants for finitely many conductors

Qualitative nonvanishing at one and finiteness of the character groups give
positive uniform constants on every finite conductor range. The existing
derivative bound also gives a positive gap from one for every real primitive
zero in that range. No quantitative dependence of these constants on the
conductor cutoff is claimed.
-/

noncomputable section

namespace TwinPrime.Analytic

/-- A positive lower bound for all nonprincipal characters of one modulus.
The statement also covers moduli with no nonprincipal characters.
@isnad1 id=ex.0h1v.s6.361cc0c335db from=translated src=- shape=65700d79 vocab=d602e9a9
-/
theorem exists_pos_le_norm_LFunction_one (q : ℕ) [NeZero q] :
    ∃ c : ℝ, 0 < c ∧ ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      c ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  classical
  obtain ⟨c, hc, hbound⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : {χ : DirichletCharacter ℂ q // χ ≠ 1} => (0 : ℝ))
    (y := fun χ => ‖DirichletCharacter.LFunction χ.1 1‖)
    (fun χ => norm_pos_iff.mpr (DirichletCharacter.LFunction_apply_one_ne_zero χ.2))
  refine ⟨c, hc, fun χ hχ => ?_⟩
  simpa only [zero_add] using (hbound ⟨χ, hχ⟩).le

/-- A single positive lower bound for all positive conductors at most `Q`.
The `NeZero` binder restricts the modulus to the positive natural numbers.
@isnad1 id=ex.0h1v.s6.d951be0d8e4c from=translated src=- shape=863f39a8 vocab=d602e9a9
-/
theorem exists_pos_le_norm_LFunction_one_of_conductor_le (Q : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q], q ≤ Q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        c ≤ ‖DirichletCharacter.LFunction χ 1‖ := by
  induction Q with
  | zero =>
      refine ⟨1, by norm_num, ?_⟩
      intro q hq hq0 χ hχ
      exact False.elim (NeZero.ne q (Nat.eq_zero_of_le_zero hq0))
  | succ Q ih =>
      obtain ⟨c, hc, hbound⟩ := ih
      obtain ⟨d, hd, hlast⟩ := exists_pos_le_norm_LFunction_one (Q + 1)
      refine ⟨min c d, lt_min hc hd, ?_⟩
      intro q hq hqQ χ hχ
      by_cases heq : q = Q + 1
      · subst q
        exact (min_le_right c d).trans (hlast χ hχ)
      · exact (min_le_left c d).trans (hbound q (by omega) χ hχ)

/-- The coarse derivative budget is monotone over positive conductors.
@isnad1 id=le.2h2v.s7.2d649f3e678a from=translated src=- shape=c5e2a3ac vocab=70b21fec
-/
theorem primitiveLFunction_real_derivative_budget_le {q Q : ℕ}
    (hq : 0 < q) (hqQ : q ≤ Q) :
    4 + 14 * Real.sqrt q * (1 + Real.log q) ≤
      4 + 14 * Real.sqrt Q * (1 + Real.log Q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hqQR : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hlogq := Real.log_natCast_nonneg q
  have hlogQ := Real.log_natCast_nonneg Q
  have hsqrt := Real.sqrt_le_sqrt hqQR
  have hlog := Real.log_le_log hq0 hqQR
  gcongr

/-- Every actual real zero of a primitive character in a finite conductor
range stays a positive uniform distance to the left of one.
@isnad1 id=ex.0h1v.s6.2c24e204ca38 from=translated src=- shape=f318d5f5 vocab=426567d4
-/
theorem exists_pos_le_primitive_real_zero_gap_of_conductor_le (Q : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (q : ℕ) [NeZero q], 1 < q → q ≤ Q →
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ β : ℝ,
        DirichletCharacter.LFunction χ (β : ℂ) = 0 → δ ≤ 1 - β := by
  obtain ⟨c, hc, hbound⟩ := exists_pos_le_norm_LFunction_one_of_conductor_le Q
  let C : ℝ := 4 + 14 * Real.sqrt Q * (1 + Real.log Q)
  have hC : 0 < C := by
    have := Real.log_natCast_nonneg Q
    dsimp [C]
    positivity
  refine ⟨min (1 / 4) (c / C), lt_min (by norm_num) (div_pos hc hC), ?_⟩
  intro q hq hq1 hqQ χ hχ β hzero
  by_cases hβ : 3 / 4 ≤ β
  · have hχne := primitive_character_ne_one hq1 χ hχ
    have hβ1 : β ≤ 1 := by
      by_contra h
      have hn := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
        (s := (β : ℂ)) (Or.inl hχne)
        (by simp only [Complex.ofReal_re]; linarith)
      exact hn hzero
    have hv := norm_LFunction_one_le_gap_budget hq1 χ hχ β hβ hβ1 hzero
    have hb := primitiveLFunction_real_derivative_budget_le (by omega : 0 < q) hqQ
    have hval := hbound q hqQ χ hχne
    have hcC : c ≤ C * (1 - β) := hval.trans (hv.trans
      (mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hβ1)))
    exact (min_le_right (1 / 4) (c / C)).trans ((div_le_iff₀ hC).mpr (by
      simpa only [mul_comm] using hcC))
  · exact (min_le_left (1 / 4) (c / C)).trans (by linarith)

end TwinPrime.Analytic
