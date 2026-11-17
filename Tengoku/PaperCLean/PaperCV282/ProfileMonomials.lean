import Tengoku.Seed.Analysis.MeanInequalities

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Numerical assembly of the three-term profile

These are inequalities between the explicit monomials, independent of
arithmetic population estimates. They record precisely the weighted
arithmetic-geometric mean step from (3.3) to (3.4), and the domination
of each row of the assembly table. They do not assert that an unproved
sector satisfies its proposed row.
-/

namespace PaperC.V282.ProfileMonomials

noncomputable section

/-- The three distinct monomials in the raw relation profile.-/
def rawProfile (M Q : ℝ) : ℝ :=
  M ^ (3 / (2 : ℝ)) * Q ^ (1 / (6 : ℝ)) +
    M * Q ^ (2 / (3 : ℝ)) + M ^ (2 / (3 : ℝ)) * Q

/-- The two-term profile after interpolation, with the exponent 5/3 explicit.-/
def coarseProfile (M Q : ℝ) : ℝ := M ^ (5 / (3 : ℝ)) + M ^ (2 / (3 : ℝ)) * Q

/-- The capped three-term expression, keeping the common ceiling separate.-/
def cappedProfile (M Q T : ℝ) : ℝ :=
  M ^ (3 / (2 : ℝ)) * Q ^ (1 / (6 : ℝ)) +
    M * Q ^ (2 / (3 : ℝ)) + M ^ (2 / (3 : ℝ)) * min T Q

/--
@isnad1 id=le.2h2v.s5.808f783aeb71 from=translated src=- shape=6c67d60b vocab=41b510ba
-/
theorem rawProfile_nonneg {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 ≤ Q) :
    0 ≤ rawProfile M Q := by unfold rawProfile; positivity

/--
@isnad1 id=le.2h2v.s5.4d53c6f09f13 from=translated src=- shape=6c67d60b vocab=cc9ba91f
-/
theorem coarseProfile_nonneg {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 ≤ Q) :
    0 ≤ coarseProfile M Q := by unfold coarseProfile; positivity

/--
@isnad1 id=le.3h3v.s5.802eebee5530 from=translated src=- shape=1b4cbc0d vocab=acec1a5b
-/
theorem cappedProfile_nonneg {M Q T : ℝ}
    (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hT : 0 ≤ T) : 0 ≤ cappedProfile M Q T := by
  unfold cappedProfile
  positivity

/-- The first monomial is the displayed weighted geometric mean.
@isnad1 id=eq.2h2v.s7.d88fb5c741d2 from=translated src=- shape=bcf1fc86 vocab=d8b90f1e
-/
theorem shallow_monomial_eq_geometric_mean {M Q : ℝ} (hM : 0 < M) (hQ : 0 ≤ Q) :
    M ^ (3 / (2 : ℝ)) * Q ^ (1 / (6 : ℝ)) =
      (M ^ (5 / (3 : ℝ))) ^ (5 / (6 : ℝ)) *
        (M ^ (2 / (3 : ℝ)) * Q) ^ (1 / (6 : ℝ)) := by
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ M ^ (2 / (3 : ℝ))) hQ]
  rw [← Real.rpow_mul hM.le, ← Real.rpow_mul hM.le, ← mul_assoc, ← Real.rpow_add hM]
  norm_num

/-- The middle monomial is the other weighted geometric mean.
@isnad1 id=eq.2h2v.s7.f3f88d59776f from=translated src=- shape=05998583 vocab=d8b90f1e
-/
theorem moderate_monomial_eq_geometric_mean {M Q : ℝ} (hM : 0 < M) (hQ : 0 ≤ Q) :
    M * Q ^ (2 / (3 : ℝ)) =
      (M ^ (5 / (3 : ℝ))) ^ (1 / (3 : ℝ)) *
        (M ^ (2 / (3 : ℝ)) * Q) ^ (2 / (3 : ℝ)) := by
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ M ^ (2 / (3 : ℝ))) hQ]
  rw [← Real.rpow_mul hM.le, ← Real.rpow_mul hM.le, ← mul_assoc, ← Real.rpow_add hM]
  norm_num

/-- The exact coefficients in the first arithmetic-geometric mean bound.
@isnad1 id=le.2h2v.s7.43f6441ad504 from=translated src=- shape=7a9a6bdf vocab=5c9d27ef
-/
theorem shallow_monomial_le_weighted_sum {M Q : ℝ} (hM : 0 < M) (hQ : 0 ≤ Q) :
    M ^ (3 / (2 : ℝ)) * Q ^ (1 / (6 : ℝ)) ≤
      (5 / (6 : ℝ)) * M ^ (5 / (3 : ℝ)) +
        (1 / (6 : ℝ)) * (M ^ (2 / (3 : ℝ)) * Q) := by
  rw [shallow_monomial_eq_geometric_mean hM hQ]
  exact Real.geom_mean_le_arith_mean2_weighted (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by norm_num)

/-- The exact coefficients in the second arithmetic-geometric mean bound.
@isnad1 id=le.2h2v.s7.cef960da53bc from=translated src=- shape=fd2b4a46 vocab=5c9d27ef
-/
theorem moderate_monomial_le_weighted_sum {M Q : ℝ} (hM : 0 < M) (hQ : 0 ≤ Q) :
    M * Q ^ (2 / (3 : ℝ)) ≤
      (1 / (3 : ℝ)) * M ^ (5 / (3 : ℝ)) +
        (2 / (3 : ℝ)) * (M ^ (2 / (3 : ℝ)) * Q) := by
  rw [moderate_monomial_eq_geometric_mean hM hQ]
  exact Real.geom_mean_le_arith_mean2_weighted (by norm_num) (by norm_num)
    (by positivity) (by positivity) (by norm_num)

/-- The interpolation step of Theorem 3.1, with an explicit uniform constant.
@isnad1 id=le.2h2v.s5.63b8713cc516 from=translated src=- shape=bc2ccdf0 vocab=d6a1b717
-/
theorem rawProfile_le_two_coarseProfile {M Q : ℝ} (hM : 0 < M) (hQ : 0 ≤ Q) :
    rawProfile M Q ≤ 2 * coarseProfile M Q := by
  have hfirst := shallow_monomial_le_weighted_sum hM hQ
  have hsecond := moderate_monomial_le_weighted_sum hM hQ
  have hnonnegA : 0 ≤ M ^ (5 / (3 : ℝ)) := by positivity
  have hnonnegB : 0 ≤ M ^ (2 / (3 : ℝ)) * Q := by positivity
  unfold rawProfile coarseProfile
  linarith

/-- The cap acts monotonically in its ceiling.
@isnad1 id=le.2h4v.s5.d330cb656146 from=translated src=- shape=f8642053 vocab=acec1a5b
-/
theorem cappedProfile_mono_cap {M Q S T : ℝ} (hM : 0 ≤ M) (hST : S ≤ T) :
    cappedProfile M Q S ≤ cappedProfile M Q T := by
  unfold cappedProfile
  gcongr

/-- The capped expression is always bounded by the uncapped expression.
@isnad1 id=le.1h3v.s4.dafa7e5764d4 from=translated src=- shape=9eb25403 vocab=2efe027d
-/
theorem cappedProfile_le_rawProfile {M Q T : ℝ} (hM : 0 ≤ M) :
    cappedProfile M Q T ≤ rawProfile M Q := by
  unfold cappedProfile rawProfile
  gcongr
  exact min_le_right _ _

/-- Once the ceiling reaches the word space, the two expressions agree exactly.
@isnad1 id=eq.1h3v.s4.1b9fb6fff795 from=translated src=- shape=b4126a04 vocab=2efe027d
-/
theorem cappedProfile_eq_rawProfile_of_word_le_cap {M Q T : ℝ} (hQT : Q ≤ T) :
    cappedProfile M Q T = rawProfile M Q := by simp [cappedProfile, rawProfile, min_eq_right hQT]

/-- The sparse-host correction fits into the first monomial.
@isnad1 id=le.2h2v.s7.40be08b7f97e from=translated src=- shape=37324720 vocab=d46e17f2
-/
theorem host_monomial_le_shallow {M Q : ℝ} (hM : 0 ≤ M) (hQ : 1 ≤ Q) :
    M ^ (3 / (2 : ℝ)) ≤ M ^ (3 / (2 : ℝ)) * Q ^ (1 / (6 : ℝ)) := by
  exact le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hQ (by norm_num))

/-- Both rational height populations fit into the middle monomial.
@isnad1 id=le.2h2v.s7.a126c9fbc739 from=translated src=- shape=5f47c921 vocab=e624faf6
-/
theorem rational_monomials_le_two_moderate {M Q : ℝ} (hM : 0 ≤ M) (hQ : 1 ≤ Q) :
    M * Q ^ (1 / (2 : ℝ)) + M * Q ^ (1 / (3 : ℝ)) ≤
      2 * (M * Q ^ (2 / (3 : ℝ))) := by
  have hhalf := Real.rpow_le_rpow_of_exponent_le hQ (by norm_num : (1 / (2 : ℝ)) ≤ 2 / 3)
  have hthird := Real.rpow_le_rpow_of_exponent_le hQ (by norm_num : (1 / (3 : ℝ)) ≤ 2 / 3)
  nlinarith

/-- The many-defect monomial is absorbed by the terminal main term.
@isnad1 id=le.2h2v.s6.a6391012af6e from=translated src=- shape=739e91ab vocab=d46e17f2
-/
theorem defects_monomial_le_terminal {M Q : ℝ} (hM : 1 ≤ M) (hQ : 0 ≤ Q) :
    M ^ (1 / (2 : ℝ)) * Q ≤ M ^ (2 / (3 : ℝ)) * Q := by
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hM (by norm_num)) hQ

/-- The exceptional terminal stratum fits into the middle monomial.
@isnad1 id=le.2h2v.s7.bb8b42f7c885 from=translated src=- shape=eef3fe7f vocab=d46e17f2
-/
theorem exceptional_terminal_le_moderate {M Q : ℝ} (hM : 1 ≤ M) (hQ : 0 ≤ Q) :
    M ^ (3 / (4 : ℝ)) * Q ^ (2 / (3 : ℝ)) ≤ M * Q ^ (2 / (3 : ℝ)) := by
  have hp : M ^ (3 / (4 : ℝ)) ≤ M := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hM (by norm_num : (3 / (4 : ℝ)) ≤ 1)
  exact mul_le_mul_of_nonneg_right hp (by positivity)

end
end PaperC.V282.ProfileMonomials
