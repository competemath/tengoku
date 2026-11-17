import Tengoku.SingularityCompleteLean.Singularity.Operators
import Tengoku.Seed.Analysis.Normed.Algebra.Spectrum
import Tengoku.Seed.Analysis.Normed.Operator.Banach

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Spectral control by a quadratic-form bound

The modulus of the quadratic form, rather than the operator norm, controls the
spectrum. Lax--Milgram/coercivity supplies the resolvent outside the quadratic
bound. This works for non-self-adjoint operators and is suitable for the
non-lazy right Markov operator.
-/

noncomputable section
open scoped InnerProductSpace

namespace Singularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- A quadratic bound gives coercivity of every normalized resolvent.
@isnad1 id=coercive.1h4v.s10.20637cb5ceca from=translated src=- shape=e2c8ed05 vocab=5e6b6ec7
-/
theorem quadratic_bound_coercive (P : E →L[ℂ] E) (q : ℝ)
    (hP : ∀ v, ‖inner ℂ (P v) v‖ ≤ q * ‖v‖ ^ 2) (a : ℂ) :
    Coercive (1 - a • P) (1 - ‖a‖ * q) := by
  intro v
  have h := mul_le_mul_of_nonneg_left (hP v) (norm_nonneg a)
  have hr := Complex.re_le_norm (inner ℂ (a • P v) v)
  rw [inner_smul_left, norm_mul, Complex.norm_conj] at hr
  change (1 - ‖a‖ * q) * ‖v‖ ^ 2 ≤
    (inner ℂ (v - a • P v) v).re
  have hself : (inner ℂ v v).re = ‖v‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  rw [inner_sub_left, Complex.sub_re, hself, inner_smul_left]
  nlinarith

/-- Coercivity makes the normalized resolvent an invertible bounded operator.
@isnad1 id=isunit.2h4v.s10.3545601fa2ba from=translated src=- shape=23ef85d3 vocab=d688c591
-/
theorem quadratic_bound_isUnit (P : E →L[ℂ] E) (q : ℝ)
    (hP : ∀ v, ‖inner ℂ (P v) v‖ ≤ q * ‖v‖ ^ 2) (a : ℂ)
    (ha : ‖a‖ * q < 1) : IsUnit (1 - a • P) := by
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  exact ((quadratic_bound_coercive P q hP a).equiv (by linarith)).bijective

/-- Every complex number outside the quadratic bound lies in the resolvent set.
@isnad1 id=mem.3h4v.s8.e215621d3800 from=translated src=- shape=56afa466 vocab=b424150e
-/
theorem quadratic_bound_resolvent (P : E →L[ℂ] E) {q : ℝ} (hq : 0 ≤ q)
    (hP : ∀ v, ‖inner ℂ (P v) v‖ ≤ q * ‖v‖ ^ 2) {k : ℂ} (hk : q < ‖k‖) :
    k ∈ resolventSet ℂ P := by
  have hk0 : k ≠ 0 := norm_pos_iff.mp (hq.trans_lt hk)
  have hunit := quadratic_bound_isUnit P q hP k⁻¹ (by
    rw [norm_inv, inv_mul_lt_iff₀ (hq.trans_lt hk), mul_one]
    exact hk)
  apply spectrum.mem_resolventSet_iff.mpr
  have he : algebraMap ℂ (E →L[ℂ] E) k - P = k • (1 - k⁻¹ • P) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hk0, one_smul,
      Algebra.algebraMap_eq_smul_one]
  rw [he]
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  obtain ⟨hinj, hsurj⟩ := ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  constructor
  · intro v w hvw
    apply hinj
    exact (smul_right_injective _ hk0) hvw
  · intro w
    obtain ⟨v, hv⟩ := hsurj (k⁻¹ • w)
    refine ⟨v, ?_⟩
    change k • ((1 - k⁻¹ • P) v) = w
    rw [hv, smul_smul, mul_inv_cancel₀ hk0, one_smul]

/-- Every spectral value is bounded by the modulus bound on the quadratic form.
@isnad1 id=le.3h4v.s8.05276bcde791 from=translated src=- shape=a9fa6415 vocab=e9801cf5
-/
theorem quadratic_bound_spectrum (P : E →L[ℂ] E) {q : ℝ} (hq : 0 ≤ q)
    (hP : ∀ v, ‖inner ℂ (P v) v‖ ≤ q * ‖v‖ ^ 2) {k : ℂ}
    (hk : k ∈ spectrum ℂ P) : ‖k‖ ≤ q := by
  by_contra h
  exact hk (quadratic_bound_resolvent P hq hP (lt_of_not_ge h))

end Singularity
