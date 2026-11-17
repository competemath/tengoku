import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Algebra.DeterminantQuadraticBasic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The map Φ of Lemma H.7

The linear map Φ sends `X_i X_j` (the paper's `a_i a_j`) to `T^(i+j)` when
`i + j ≥ p - 1` and to zero otherwise. In characteristic `p` it kills the 2x2
Toeplitz minors and the coordinates of `a^2`, hence the degree-two part of `G_0`.
-/

noncomputable section
open scoped BigOperators

namespace AlternatingAnalytic.DeterminantQuadratic

variable (K : Type*) [Field K] (p : ℕ)

/-- Discard the powers below `p - 1` after substituting `X_i = T^i`.-/
def phi : Poly K p →ₗ[K] Polynomial K :=
  (LinearMap.id - Polynomial.modByMonicHom (Polynomial.X ^ (p - 1))).comp
    (MvPolynomial.aeval (fun i : Fin p => (Polynomial.X : Polynomial K) ^ i.val)).toLinearMap

/--
@isnad1 id=eq.0h4v.s9.23a18b8b6b11 from=translated src=- shape=1157460c vocab=ddba2369
-/
theorem phi_X_mul_X (i j : Fin p) :
    phi K p (MvPolynomial.X i * MvPolynomial.X j) =
      if p - 1 ≤ i.val + j.val then (Polynomial.X : Polynomial K) ^ (i.val + j.val)
      else 0 := by
  simp only [phi, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    AlgHom.toLinearMap_apply, map_mul, MvPolynomial.aeval_X]
  rw [← pow_add]
  change _ - _ %ₘ (Polynomial.X ^ (p - 1)) = _
  split_ifs with h
  · rw [(Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow _)).2
      (pow_dvd_pow _ h), sub_zero]
  · rw [(Polynomial.modByMonic_eq_self_iff (Polynomial.monic_X_pow _)).2
      (by simp only [Polynomial.degree_X_pow]; exact_mod_cast (Nat.lt_of_not_ge h)), sub_self]

/--
@isnad1 id=eq.0h6v.s8.e37503af05c0 from=translated src=- shape=a9361bb1 vocab=9aebc8f7
-/
theorem phi_minor (r s i j : Fin p) : phi K p (minor K p r s i j) = 0 := by
  have hr := r.isLt
  have hs := s.isLt
  unfold minor toeplitz
  split_ifs <;> simp only [mul_zero, zero_mul, map_sub, map_zero, sub_zero, zero_sub]
  all_goals try simp only [map_neg, phi_X_mul_X]
  all_goals try split_ifs
  all_goals try simp only [sub_self, neg_zero]
  all_goals first | (apply sub_eq_zero.mpr; congr 1; omega) | (exfalso; omega)

variable [CharP K p] [Fact p.Prime]

/--
@isnad1 id=eq.0h3v.s8.0799e50f2d35 from=translated src=- shape=67c5f4ab vocab=18f3011a
-/
theorem phi_squareCoordinate (r : Fin p) : phi K p (squareCoordinate K p r) = 0 := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hr := r.isLt
  unfold squareCoordinate
  simp only [map_sum]
  by_cases htop : r.val = p - 1
  · have hi (i : Fin p) :
        (∑ j : Fin p, phi K p
          (if i.val + j.val = r.val then MvPolynomial.X i * MvPolynomial.X j else 0)) =
          (Polynomial.X : Polynomial K) ^ (p - 1) := by
      let j : Fin p := ⟨p - 1 - i.val, by omega⟩
      rw [Finset.sum_eq_single j]
      · have hij : i.val + j.val = r.val := by dsimp [j]; omega
        simp only [phi_X_mul_X, hij, htop, le_refl, ite_true]
      · intro b _ hb
        have hib : ¬ i.val + b.val = r.val := by
          intro h
          apply hb
          apply Fin.ext
          dsimp [j]
          omega
        simp [hib]
      · simp
    simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  · apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    split_ifs with hij
    · rw [phi_X_mul_X, ite_eq_right (by omega)]
    · exact map_zero _

/--
@isnad1 id=eq.1h3v.s9.a03bf882979e from=translated src=- shape=6257a0ca vocab=7ba2efa9
-/
theorem phi_eq_zero_of_mem_quadraticSpan {P : Poly K p}
    (hP : P ∈ quadraticSpan K p) : phi K p P = 0 := by
  apply Submodule.span_induction (p := fun P _ => phi K p P = 0) ?_ ?_ ?_ ?_ hP
  · intro Q hQ
    rcases hQ with ⟨r, s, i, j, rfl⟩ | ⟨r, rfl⟩
    · exact phi_minor K p r s i j
    · exact phi_squareCoordinate K p r
  · exact map_zero _
  · intro x y _ _ hx hy
    simp [map_add, hx, hy]
  · intro a x _ hx
    simp [map_smul, hx]

end AlternatingAnalytic.DeterminantQuadratic
