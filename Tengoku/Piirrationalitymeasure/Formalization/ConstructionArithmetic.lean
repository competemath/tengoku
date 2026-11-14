import Tengoku.Piirrationalitymeasure.Formalization.ConstructionCoefficientData

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Integer chamber margins and arbitrarily large even denominators in (6.61). -/

namespace PiIrrationality

def constructionTwoSaving (b c : ℕ) : ℕ := 5 * b - 5 * (c / 2)

theorem construction_integer_margins {a b c : ℕ} (hc : 0 < c)
    (hp : Admissible (constructionParameter a b c)) :
    1 ≤ a + b - c ∧ 1 ≤ 2 * b - c ∧ 7 * b ≤ 5 * c - 1 ∧
      1 ≤ constructionDegree a b c - c ∧
      2 * a < constructionDegree a b c ∧ b < constructionDegree a b c ∧
      c < constructionDegree a b c := by
  have h := construction_admissible_inequalities hc hp
  dsimp [constructionDegree]
  omega

theorem constructionTwoSaving_cast {a b c : ℕ} (hc : 0 < c) (he : Even c)
    (hp : Admissible (constructionParameter a b c)) :
    (constructionTwoSaving b c : ℝ) = 5 * (b : ℝ) - 5 * c / 2 := by
  have h := construction_admissible_inequalities hc hp
  have hdiv : c / 2 * 2 = c := Nat.div_mul_cancel he.two_dvd
  have hle : 5 * (c / 2) ≤ 5 * b := by omega
  have hdiv' : (c / 2 : ℕ) * (2 : ℝ) = c := by exact_mod_cast hdiv
  simp only [constructionTwoSaving, Nat.cast_sub hle, Nat.cast_mul, Nat.cast_ofNat]
  linarith

theorem constructionTwoSaving_bounds {a b c : ℕ} (hc : 0 < c) (he : Even c)
    (hp : Admissible (constructionParameter a b c)) :
    0 < constructionTwoSaving b c ∧
      2 * constructionTwoSaving b c < 3 * b := by
  have h := construction_admissible_inequalities hc hp
  have hdiv : c / 2 * 2 = c := Nat.div_mul_cancel he.two_dvd
  unfold constructionTwoSaving
  omega

theorem rational_pair_even_denominator {x y : ℚ} (hx : 0 < x) (hy : 0 < y) (N : ℕ) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ N < c ∧ Even c ∧
      constructionParameter a b c = ((x : ℝ), (y : ℝ)) := by
  let a := x.num.toNat * y.den * 2 * (N + 1)
  let b := y.num.toNat * x.den * 2 * (N + 1)
  let c := x.den * y.den * 2 * (N + 1)
  have hxnum : 0 < x.num := Rat.num_pos.mpr hx
  have hynum : 0 < y.num := Rat.num_pos.mpr hy
  have hxa : 0 < x.num.toNat := by omega
  have hya : 0 < y.num.toNat := by omega
  have hxd : 0 < x.den := x.den_pos
  have hyd : 0 < y.den := y.den_pos
  have hcd : 1 ≤ x.den * y.den * 2 := by
    have : 0 < x.den * y.den * 2 := by positivity
    omega
  refine ⟨a, b, c, by dsimp [a]; positivity, by dsimp [b]; positivity,
    ?_, ?_, ?_⟩
  · dsimp [c]
    nlinarith
  · exact ⟨x.den * y.den * (N + 1), by dsimp [c]; ring⟩
  · have hxcast : (x.num.toNat : ℝ) = x.num := by
      exact_mod_cast Int.toNat_of_nonneg hxnum.le
    have hycast : (y.num.toNat : ℝ) = y.num := by
      exact_mod_cast Int.toNat_of_nonneg hynum.le
    have hxd' : (x.den : ℝ) ≠ 0 := by positivity
    have hyd' : (y.den : ℝ) ≠ 0 := by positivity
    have hN : (N : ℝ) + 1 ≠ 0 := by positivity
    apply Prod.ext <;> dsimp [constructionParameter, a, b, c]
    · push_cast
      rw [hxcast, Rat.cast_def]
      field_simp
    · push_cast
      rw [hycast, Rat.cast_def]
      field_simp

theorem admissible_rational_construction {x y : ℚ}
    (hp : Admissible ((x : ℝ), (y : ℝ))) (N : ℕ) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ N < c ∧ Even c ∧
      constructionParameter a b c = ((x : ℝ), (y : ℝ)) ∧
      1 ≤ a + b - c ∧ 1 ≤ 2 * b - c ∧ 7 * b ≤ 5 * c - 1 ∧
      1 ≤ constructionDegree a b c - c := by
  have hx : 0 < x := by
    have : (0 : ℝ) < x := by rcases hp with ⟨h1, h2, h3, h4⟩; dsimp at *; linarith
    exact_mod_cast this
  have hy : 0 < y := by
    have : (0 : ℝ) < y := by rcases hp with ⟨h1, h2, h3, h4⟩; dsimp at *; linarith
    exact_mod_cast this
  obtain ⟨a, b, c, ha, hb, hc, he, hrep⟩ := rational_pair_even_denominator hx hy N
  have hm := construction_integer_margins (by omega : 0 < c) (hrep ▸ hp)
  exact ⟨a, b, c, ha, hb, hc, he, hrep, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1⟩

end PiIrrationality
