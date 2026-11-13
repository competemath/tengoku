import Tengoku.Seed.MeasureTheory.Integral.Pi
import Tengoku.Nlalib.NLAlib.Matrix.Basic.Orthonormal
import Tengoku.Nlalib.NLAlib.Probability.Concentration.QuadraticForms.QuadraticMoments

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Independent tensor-product probes

`khatriRaoProbe` forms one Khatri–Rao row from independent vector factors.
The factors may have different dimensions, and coordinates within a factor
need not be independent. Their joint law is the ordinary finite product
`Measure.pi ν`. Isotropy passes from the factor laws to the tensor probe.

Source: Heidary, *The Sharp Logarithmic Cost of Khatri–Rao Subspace
Embeddings*, equation (1.1) and Section 2.
-/

noncomputable section

open MeasureTheory Matrix

namespace NLAlib

variable {d : ℕ} {n : Fin d → ℕ}

/-- The tensor-product vector whose coordinate at a multi-index is the
product of the corresponding factor coordinates.-/
def khatriRaoProbe (g : ∀ j : Fin d, Fin (n j) → ℝ) :
    (∀ j : Fin d, Fin (n j)) → ℝ := fun a => ∏ j, g j (a j)

/-- Each tensor-product coordinate is a continuous polynomial in the factors.
@isnad1 id=continuo.0h2v.s6.06aceaa73b47 from=translated src=- shape=0150200e vocab=8f741fa1
-/
theorem continuous_khatriRaoProbe :
    Continuous (khatriRaoProbe (n := n)) := by
  unfold khatriRaoProbe
  fun_prop

/-- The tensor-product probe is measurable for the product Borel structures.
@isnad1 id=measurab.0h2v.s6.df3057bc3553 from=translated src=- shape=0150200e vocab=fecd3aac
-/
theorem measurable_khatriRaoProbe :
    Measurable (khatriRaoProbe (n := n)) :=
  continuous_khatriRaoProbe.measurable

/-- Splitting off the first mode turns a tensor contraction into a linear
form in its first vector factor.
@isnad1 id=eq.0h5v.s8.926fab07e0b3 from=translated src=- shape=61b3cfcf vocab=b501dcd4
-/
theorem dotProduct_khatriRaoProbe_cons {d : ℕ} {n : Fin (d + 1) → ℕ}
    (a : (∀ j : Fin (d + 1), Fin (n j)) → ℝ)
    (g₀ : Fin (n 0) → ℝ) (g : ∀ j : Fin d, Fin (n j.succ) → ℝ) :
    a ⬝ᵥ khatriRaoProbe (Fin.cons g₀ g) =
      (fun i => ∑ b : ∀ j : Fin d, Fin (n j.succ),
        a (Fin.cons i b) * khatriRaoProbe g b) ⬝ᵥ g₀ := by
  classical
  unfold dotProduct
  rw [← (Fin.consEquiv (fun j => Fin (n j))).sum_comp]
  change (∑ x : Fin (n 0) × (∀ j : Fin d, Fin (n j.succ)),
    a (Fin.cons x.1 x.2) * khatriRaoProbe (Fin.cons g₀ g) (Fin.cons x.1 x.2)) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  simp only [khatriRaoProbe, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

/-- Splitting the first tensor index preserves the squared coefficient norm.
@isnad1 id=eq.0h3v.s8.abe43db6c4c1 from=translated src=- shape=40aa0486 vocab=b64cec44
-/
theorem sum_norm_sq_tensor_slices {d : ℕ} {n : Fin (d + 1) → ℕ}
    (a : (∀ j : Fin (d + 1), Fin (n j)) → ℝ) :
    (∑ i : Fin (n 0), ∑ b : ∀ j : Fin d, Fin (n j.succ), a (Fin.cons i b) ^ 2) =
      ∑ b, a b ^ 2 := by
  classical
  rw [← (Fin.consEquiv (fun j => Fin (n j))).sum_comp]
  change _ = ∑ x : Fin (n 0) × (∀ j : Fin d, Fin (n j.succ)), a (Fin.cons x.1 x.2) ^ 2
  rw [Fintype.sum_prod_type]

/-- Independent isotropic factor laws have isotropic tensor-product probes.
No independence among coordinates of a single factor is needed.
@isnad1 id=eq.1h5v.s8.141512f74780 from=translated src=- shape=5c5afd57 vocab=41573cef
-/
theorem integral_khatriRaoProbe_mul_khatriRaoProbe
    (ν : ∀ j : Fin d, Measure (Fin (n j) → ℝ))
    [∀ j, IsProbabilityMeasure (ν j)]
    (hsecond : ∀ j (a b : Fin (n j)),
      ∫ g, g a * g b ∂ν j = if a = b then 1 else 0)
    (a b : ∀ j : Fin d, Fin (n j)) :
    ∫ g, khatriRaoProbe g a * khatriRaoProbe g b ∂Measure.pi ν =
      if a = b then 1 else 0 := by
  classical
  simp only [khatriRaoProbe, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod
    (fun j (g : Fin (n j) → ℝ) => g (a j) * g (b j))]
  simp only [hsecond]
  by_cases hab : a = b
  · subst b
    simp
  · rw [ite_eq_right hab]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

/-- Every pair of tensor-product coordinates is integrable under isotropic
factor laws. Diagonal second moments equal to one force square integrability.
@isnad1 id=integrab.1h5v.s8.a371a1b75e66 from=translated src=- shape=f696d778 vocab=ff857b40
-/
theorem integrable_khatriRaoProbe_mul_khatriRaoProbe
    (ν : ∀ j : Fin d, Measure (Fin (n j) → ℝ))
    [∀ j, IsProbabilityMeasure (ν j)]
    (hsecond : ∀ j (a b : Fin (n j)),
      ∫ g, g a * g b ∂ν j = if a = b then 1 else 0)
    (a b : ∀ j : Fin d, Fin (n j)) :
    Integrable (fun g => khatriRaoProbe g a * khatriRaoProbe g b) (Measure.pi ν) := by
  have hL2 (a : ∀ j : Fin d, Fin (n j)) :
      MemLp (fun g => khatriRaoProbe g a) 2 (Measure.pi ν) := by
    apply (memLp_two_iff_integrable_sq
      ((measurable_pi_apply a).comp measurable_khatriRaoProbe).aestronglyMeasurable).2
    apply integrable_of_integral_eq_one
    simpa [pow_two] using integral_khatriRaoProbe_mul_khatriRaoProbe ν hsecond a a
  exact (hL2 a).integrable_mul (hL2 b)

/-- Quadratic forms of tensor-product probes have the expected trace whenever
the independent factors are isotropic.
@isnad1 id=eq.1h4v.s8.2dc723dcd503 from=translated src=- shape=a3fe13eb vocab=0bff5913
-/
theorem integral_quadForm_khatriRaoProbe_eq_trace
    (ν : ∀ j : Fin d, Measure (Fin (n j) → ℝ))
    [∀ j, IsProbabilityMeasure (ν j)]
    (hsecond : ∀ j (a b : Fin (n j)),
      ∫ g, g a * g b ∂ν j = if a = b then 1 else 0)
    (A : Matrix (∀ j : Fin d, Fin (n j)) (∀ j : Fin d, Fin (n j)) ℝ) :
    (∫ g, quadForm A (khatriRaoProbe g) ∂Measure.pi ν) = A.trace := by
  exact integral_quadForm_eq_trace_of_second_moments A
    (fun a => ((measurable_pi_apply a).comp measurable_khatriRaoProbe).aemeasurable)
    (integral_khatriRaoProbe_mul_khatriRaoProbe ν hsecond)

/-- Restricting independent isotropic tensor probes to an orthonormal
subspace preserves their identity second-moment matrix.
@isnad1 id=eq.2h7v.s8.6ef319e76a37 from=translated src=- shape=950e29e6 vocab=39c8fff0
-/
theorem integral_projected_khatriRaoProbe_mul_projected_khatriRaoProbe
    (ν : ∀ j : Fin d, Measure (Fin (n j) → ℝ))
    [∀ j, IsProbabilityMeasure (ν j)]
    (hsecond : ∀ j (a b : Fin (n j)),
      ∫ g, g a * g b ∂ν j = if a = b then 1 else 0)
    {r : ℕ} (U : Matrix (∀ j : Fin d, Fin (n j)) (Fin r) ℝ)
    (hU : HasOrthonormalCols U) (i j : Fin r) :
    ∫ g, (Uᵀ *ᵥ khatriRaoProbe g) i * (Uᵀ *ᵥ khatriRaoProbe g) j
        ∂Measure.pi ν = if i = j then 1 else 0 := by
  classical
  let A := Matrix.vecMulVec (fun a => U a i) (fun a => U a j)
  have hpoint (g : ∀ j : Fin d, Fin (n j) → ℝ) :
      (Uᵀ *ᵥ khatriRaoProbe g) i * (Uᵀ *ᵥ khatriRaoProbe g) j =
        quadForm A (khatriRaoProbe g) := by
    simp only [A, quadForm, star_trivial, Matrix.vecMulVec_mulVec,
      dotProduct_smul, op_smul_eq_mul, Matrix.mulVec, Matrix.transpose_apply]
    rw [dotProduct_comm (khatriRaoProbe g) (fun a => U a i)]
  simp_rw [hpoint]
  rw [integral_quadForm_khatriRaoProbe_eq_trace ν hsecond]
  have hU' : Uᵀ * U = 1 := hU
  simpa only [A, Matrix.trace, Matrix.diag, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.one_apply] using congrArg (fun M => M i j) hU'

end NLAlib
