import Tengoku.Piirrationalitymeasure.Formalization.PhaseSigns

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Descartes' rule applied to the transformed phase polynomial in (A.20).
The root count includes multiplicities.
-/

namespace PiIrrationality

theorem phaseTransformedPolynomial_ne_zero (e : ℝ) :
    phaseTransformedPolynomial e ≠ 0 := by
  intro h
  have hc := phaseTransformedPolynomial_coeff_six e
  rw [h] at hc
  norm_num [phaseC6] at hc

theorem phaseTransformedPolynomial_natDegree (e : ℝ) :
    (phaseTransformedPolynomial e).natDegree = 6 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · unfold phaseTransformedPolynomial
    compute_degree!
  · rw [phaseTransformedPolynomial_coeff_six]
    exact (phaseC6_neg e).ne

theorem phaseTransformedPolynomial_coeffList (e : ℝ) :
    (phaseTransformedPolynomial e).coeffList =
      [phaseC6 e, phaseC5 e, phaseC4 e, phaseC3 e, phaseC2 e, phaseC1 e, phaseC0 e] := by
  rw [Polynomial.coeffList,
    Polynomial.withBotSucc_degree_eq_natDegree_add_one (phaseTransformedPolynomial_ne_zero e),
    phaseTransformedPolynomial_natDegree]
  norm_num [List.range_succ, phaseTransformedPolynomial]

theorem phaseTransformedPolynomial_signVariations {e : ℝ}
    (he : (9 : ℝ) / 10 < e) (he1 : e < 1) :
    (phaseTransformedPolynomial e).signVariations = 1 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := phase_transformed_signs he he1
  rw [Polynomial.signVariations, phaseTransformedPolynomial_coeffList]
  norm_num [sign_pos h0, sign_pos h1, sign_pos h2, sign_pos h3,
    sign_neg h4, sign_neg h5, sign_neg h6, List.destutter, List.destutter']

theorem phaseTransformedPolynomial_positive_root_count {e : ℝ}
    (he : (9 : ℝ) / 10 < e) (he1 : e < 1) :
    (phaseTransformedPolynomial e).roots.countP (0 < ·) ≤ 1 := by
  have h := (phaseTransformedPolynomial e).roots_countP_pos_le_signVariations
  rwa [phaseTransformedPolynomial_signVariations he he1] at h

theorem phaseTransformedPolynomial_positive_root_unique {e x y : ℝ}
    (he : (9 : ℝ) / 10 < e) (he1 : e < 1) (hx : 0 < x) (hy : 0 < y)
    (hpx : (phaseTransformedPolynomial e).eval x = 0)
    (hpy : (phaseTransformedPolynomial e).eval y = 0) : x = y := by
  classical
  let roots := (phaseTransformedPolynomial e).roots.filter (0 < ·)
  have hxmem : x ∈ roots := by
    simp [roots, Polynomial.mem_roots (phaseTransformedPolynomial_ne_zero e),
      Polynomial.IsRoot, hpx, hx]
  have hymem : y ∈ roots := by
    simp [roots, Polynomial.mem_roots (phaseTransformedPolynomial_ne_zero e),
      Polynomial.IsRoot, hpy, hy]
  have hcard : roots.card ≤ 1 := by
    simpa only [Multiset.countP_eq_card_filter] using
      phaseTransformedPolynomial_positive_root_count he he1
  have hpos : 0 < roots.card := Multiset.card_pos_iff_exists_mem.mpr ⟨x, hxmem⟩
  obtain ⟨z, hz⟩ := Multiset.card_eq_one.mp (show roots.card = 1 by omega)
  rw [hz, Multiset.mem_singleton] at hxmem hymem
  exact hxmem.trans hymem.symm

end PiIrrationality
