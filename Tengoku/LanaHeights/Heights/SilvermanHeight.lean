import Tengoku.LanaHeights.Heights.ArchimedeanAlgebraicRealization
import Tengoku.LanaHeights.Heights.ModularJFibers
import Tengoku.LanaHeights.Heights.WeilHeight

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option linter.style.header false

/-!
# Silverman's formula-defined elliptic-curve height

This file defines the finite-plus-archimedean expression in Silverman's
Proposition 1.1 from explicit realization certificates. It does not construct
an Arakelov/Faltings height and does not yet prove that the expression agrees
with one. In particular, this is not an arbitrary real supplied by a
certificate.
-/

open scoped NumberField UpperHalfPlane
open NumberField

namespace Heights

/-- The logarithm of the absolute norm of an integral ideal.

Height formulae should use this only together with a proof that the ideal is
not `⊥`; `absNorm_pos_of_ne_bot` records the resulting strict positivity. -/
noncomputable def logIdealNorm
    {K : Type*} [Field K] [NumberField K] (I : Ideal (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm I)

/-- A nonzero integral ideal has strictly positive absolute norm, so its norm
is a legitimate logarithm argument.
@isnad1 id=lt.1h2v.s8.e6bb0a3102d1 from=translated src=- shape=e6d4aee3 vocab=45666427
-/
theorem absNorm_pos_of_ne_bot
    {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 < (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)

/-- The logarithmic norm of the unit ideal vanishes.
@isnad1 id=eq.0h1v.s6.4ecb3c1b209c from=translated src=- shape=066f9b3f vocab=635f925f
-/
@[simp] theorem logIdealNorm_top
    {K : Type*} [Field K] [NumberField K] :
    logIdealNorm (⊤ : Ideal (𝓞 K)) = 0 := by
  simp [logIdealNorm]

/-- The logarithmic norm of a nonzero integral ideal is nonnegative.
@isnad1 id=le.1h2v.s6.192095ac365b from=translated src=- shape=fc5417e1 vocab=13969f3d
-/
theorem logIdealNorm_nonneg
    {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    0 ≤ logIdealNorm I := by
  apply Real.log_nonneg
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr hI)

/-- Silverman's finite-plus-archimedean elliptic-curve height expression.

The finite term is the norm of the certified minimal-discriminant ideal. The
archimedean term uses actual period ratios and the actual modular discriminant,
including `(2π) ^ 12`, and the whole expression is divided by `12 [K : ℚ]`.
Both inputs can now be constructed over every number field. The archimedean
input is the minimal `j`-compatible data of `ArchimedeanPeriodData`; it is
proved separately to determine an algebraic variable change from the explicit
lattice curve to the embedded input curve. No Arakelov or integration-based
analytic interpretation is asserted. -/
noncomputable def silvermanHeight
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (p : ArchimedeanPeriodData K W) : ℝ :=
  (logIdealNorm m.ideal -
      ∑ v : InfinitePlace K,
        (v.mult : ℝ) * Real.log
          (‖silvermanModularDiscriminant (p.τ v)‖ * (p.τ v).im ^ 6)) /
    (12 * (Module.finrank ℚ K : ℝ))

/-- The formula-defined height is independent of the qualifying period data.
This is canonicity of the displayed modular expression. The parameters do
algebraically realize the embedded curve, but no period-integration or
Arakelov interpretation is used here.
@isnad1 id=eq.0h5v.s5.893c1d88e74a from=translated src=- shape=d994ae99 vocab=7ac1d712
-/
theorem silvermanHeight_periodData_independent
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (m : GlobalMinimalDiscriminantData K W)
    (p q : ArchimedeanPeriodData K W) :
    silvermanHeight W m p = silvermanHeight W m q := by
  have hsum :
      (∑ v : InfinitePlace K,
        (v.mult : ℝ) * Real.log
          (‖silvermanModularDiscriminant (p.τ v)‖ * (p.τ v).im ^ 6)) =
      ∑ v : InfinitePlace K,
        (v.mult : ℝ) * Real.log
          (‖silvermanModularDiscriminant (q.τ v)‖ * (q.τ v).im ^ 6) := by
    apply Finset.sum_congr rfl
    intro v _hv
    have hj : modularJ (p.τ v) = modularJ (q.τ v) :=
      (p.j_eq v).symm.trans (q.j_eq v)
    rw [silvermanModularDiscriminant_norm_mul_im_pow_eq_of_modularJ_eq
      (p.τ v) (q.τ v) hj]
  rw [silvermanHeight, silvermanHeight, hsum]

/-- Silverman's formula-defined height using the chosen global
minimal-discriminant data and supplied archimedean data. The value is
independent of this supplied data by `silvermanHeight_periodData_independent`. -/
noncomputable def silvermanHeightOfPeriods
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ArchimedeanPeriodData K W) : ℝ :=
  silvermanHeight W (globalMinimalDiscriminantData W) p

/-- Silverman's formula-defined height using classical choices of both the
global minimal-discriminant data and the `j`-compatible archimedean data. The
formula is choice-independent, and the archimedean parameter algebraically
realizes the embedded curve. This is still not claimed to be an independently
constructed Arakelov Faltings height: period integration and the Hodge metric
have not been formalized. -/
noncomputable def silvermanHeightOfCurve
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic] : ℝ :=
  silvermanHeightOfPeriods W (archimedeanPeriodData W)

/-- Every qualifying period datum computes the canonical formula-defined
curve height.
@isnad1 id=eq.0h3v.s5.c137655d1ec4 from=translated src=- shape=99c00841 vocab=64e9c26a
-/
theorem silvermanHeightOfPeriods_eq_silvermanHeightOfCurve
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ArchimedeanPeriodData K W) :
    silvermanHeightOfPeriods W p = silvermanHeightOfCurve W :=
  silvermanHeight_periodData_independent W (globalMinimalDiscriminantData W)
    p (archimedeanPeriodData W)

/-- Every archimedean logarithm argument in `silvermanHeight` is strictly
positive.
@isnad1 id=lt.0h4v.s6.cf08a225a68d from=translated src=- shape=f4cc813c vocab=d833d1b7
-/
theorem silvermanHeight_archimedean_log_arg_pos
    {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ArchimedeanPeriodData K W) (v : InfinitePlace K) :
    0 < ‖silvermanModularDiscriminant (p.τ v)‖ * (p.τ v).im ^ 6 := by
  exact mul_pos (silvermanModularDiscriminant_norm_pos _)
    (pow_pos (p.τ v).im_pos _)

/-- The denominator in `silvermanHeight` is strictly positive.
@isnad1 id=lt.0h1v.s6.b67aaa683efd from=translated src=- shape=3e992223 vocab=9d3bf0e7
-/
theorem silvermanHeight_denominator_pos
    (K : Type*) [Field K] [NumberField K] :
    (0 : ℝ) < 12 * Module.finrank ℚ K := by
  exact mul_pos (by norm_num) (numberFieldDegree_pos K)

end Heights
