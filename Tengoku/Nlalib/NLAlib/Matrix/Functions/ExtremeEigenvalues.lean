import Tengoku.Nlalib.NLAlib.Matrix.Functions.ExpLog
import Tengoku.Seed.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Tengoku.Seed.Data.Real.Pointwise

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extreme eigenvalues: scaling, identity, positivity and norm deviations

Elementary API for `lambdaMax` and `lambdaMin` on `Matrix d d 𝕜`, `[RCLike 𝕜]`, over any finite
index type:

* positive scaling and the identity: `lambdaMax_smul_of_pos`, `lambdaMin_smul_of_pos`,
  `lambdaMax_one`, `lambdaMin_one`;
* positive semidefinite matrices: `lambdaMin_nonneg_of_posSemidef`,
  `lambdaMax_le_trace_of_posSemidef`;
* a norm deviation from the identity is an extreme-eigenvalue deviation:
  `lambdaMin_le_or_le_lambdaMax_of_le_norm_sub_one`.

`lambdaMin_le_or_le_lambdaMax_of_le_norm_sub_one` is stated over `ℂ` (its proof is the
C*-algebra fact that `‖H − I‖` or `−‖H − I‖` lies in the spectrum).
Tropp 2015, §2.1. Atlas: helpers for `matrix-chernoff-sampling`, `leverage-sampling-ose`.
-/

open scoped Pointwise
open scoped Matrix Matrix.Norms.L2Operator ComplexOrder

noncomputable section

namespace NLAlib

section Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {d : Type*} [Fintype d] [DecidableEq d]

/-- `λmax(c A) = c λmax(A)` for `c > 0`. Tropp 2015, §2.1; atlas `matrix-chernoff-sampling`
(helper).
@isnad1 id=eq.1h4v.s6.57253bdf941b from=translated src=- shape=215a7f55 vocab=c64b3ec6
-/
theorem lambdaMax_smul_of_pos (A : Matrix d d 𝕜) {c : ℝ} (hc : 0 < c) :
    lambdaMax (c • A) = c * lambdaMax A := by
  have h := spectrum.unit_smul_eq_smul (R := ℝ) A (Units.mk0 c hc.ne')
  rw [Units.smul_def, Units.val_mk0] at h
  rw [lambdaMax, h, Units.smul_def, Units.val_mk0, Real.sSup_smul_of_nonneg hc.le, smul_eq_mul,
    lambdaMax]

/-- Nonnegative scalar multiplication, including zero, commutes with the
largest eigenvalue in nonempty dimension.
@isnad1 id=eq.1h4v.s6.320b6ca4eef6 from=translated src=- shape=89deb748 vocab=2d0ae5a5
-/
theorem lambdaMax_smul_of_nonneg [Nonempty d] (A : Matrix d d 𝕜) {c : ℝ} (hc : 0 ≤ c) :
    lambdaMax (c • A) = c * lambdaMax A := by
  rcases eq_or_lt_of_le hc with hzero | hpos
  · rw [← hzero]
    simp [lambdaMax, spectrum.zero_eq]
  · exact lambdaMax_smul_of_pos A hpos

/-- `λmin(c A) = c λmin(A)` for `c > 0`. Tropp 2015, §2.1; atlas `matrix-chernoff-sampling`
(helper).
@isnad1 id=eq.1h4v.s6.68895c4280a7 from=translated src=- shape=215a7f55 vocab=56355a1c
-/
theorem lambdaMin_smul_of_pos (A : Matrix d d 𝕜) {c : ℝ} (hc : 0 < c) :
    lambdaMin (c • A) = c * lambdaMin A := by
  have h := spectrum.unit_smul_eq_smul (R := ℝ) A (Units.mk0 c hc.ne')
  rw [Units.smul_def, Units.val_mk0] at h
  rw [lambdaMin, h, Units.smul_def, Units.val_mk0, Real.sInf_smul_of_nonneg hc.le, smul_eq_mul,
    lambdaMin]

/-- Negation exchanges the largest and smallest real spectral values.
The total identity also includes empty dimension.
@isnad1 id=eq.0h3v.s6.d1ecfdc7b9d8 from=translated src=- shape=e35d44d8 vocab=e86111b9
-/
@[simp] theorem lambdaMax_neg (A : Matrix d d 𝕜) : lambdaMax (-A) = -lambdaMin A := by
  rw [lambdaMax, ← spectrum.neg_eq, Real.sSup_neg, lambdaMin]

/-- Negation exchanges the smallest and largest real spectral values.
The total identity also includes empty dimension.
@isnad1 id=eq.0h3v.s6.1d6f98f8d4d0 from=translated src=- shape=e35d44d8 vocab=e86111b9
-/
@[simp] theorem lambdaMin_neg (A : Matrix d d 𝕜) : lambdaMin (-A) = -lambdaMax A := by
  rw [lambdaMin, ← spectrum.neg_eq, Real.sInf_neg, lambdaMax]

/-- `λmax(I) = 1` for a nonempty index type. Tropp 2015, §2.1; atlas
`matrix-chernoff-sampling` (helper).
@isnad1 id=eq.0h2v.s6.25e76764d690 from=translated src=- shape=2f8dc985 vocab=4bfcec44
-/
@[simp] theorem lambdaMax_one [Nonempty d] : lambdaMax (1 : Matrix d d 𝕜) = 1 := by
  rw [lambdaMax, spectrum.one_eq, csSup_singleton]

/-- `λmin(I) = 1` for a nonempty index type. Tropp 2015, §2.1; atlas
`matrix-chernoff-sampling` (helper).
@isnad1 id=eq.0h2v.s6.797242511686 from=translated src=- shape=2f8dc985 vocab=3cc411ad
-/
@[simp] theorem lambdaMin_one [Nonempty d] : lambdaMin (1 : Matrix d d 𝕜) = 1 := by
  rw [lambdaMin, spectrum.one_eq, csInf_singleton]

end Spectral

/-- A positive semidefinite matrix has nonnegative minimum eigenvalue.
Source: the finite spectral theorem; supports `leverage-sampling-ose`.
@isnad1 id=le.1h3v.s5.7778c8b87bac from=translated src=- shape=2c975406 vocab=ab69fbcd
-/
theorem lambdaMin_nonneg_of_posSemidef {𝕜 : Type*} [RCLike 𝕜] {d : Type*} [Fintype d]
    [DecidableEq d] [Nonempty d] {P : Matrix d d 𝕜} (hP : P.PosSemidef) : 0 ≤ lambdaMin P := by
  rw [lambdaMin, hP.isHermitian.spectrum_real_eq_range_eigenvalues]
  exact le_csInf (Set.range_nonempty _) (by rintro _ ⟨i, rfl⟩; exact hP.eigenvalues_nonneg i)

/-- A positive semidefinite matrix has maximum eigenvalue at most its real trace.
Source: the finite spectral theorem; supports `leverage-sampling-ose`.
@isnad1 id=le.1h3v.s7.61d23165fa8e from=translated src=- shape=02043e91 vocab=2b96aca2
-/
theorem lambdaMax_le_trace_of_posSemidef {𝕜 : Type*} [RCLike 𝕜] {d : Type*} [Fintype d]
    [DecidableEq d] [Nonempty d] {P : Matrix d d 𝕜} (hP : P.PosSemidef) :
    lambdaMax P ≤ RCLike.re P.trace := by
  have htrace : RCLike.re P.trace = ∑ i, hP.isHermitian.eigenvalues i := by
    rw [hP.isHermitian.trace_eq_sum_eigenvalues]
    simp
  rw [lambdaMax, hP.isHermitian.spectrum_real_eq_range_eigenvalues, htrace]
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨i, rfl⟩
  exact Finset.single_le_sum (fun j _ => hP.eigenvalues_nonneg j) (Finset.mem_univ i)

end NLAlib
