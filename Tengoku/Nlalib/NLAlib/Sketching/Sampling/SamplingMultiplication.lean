import Tengoku.Nlalib.NLAlib.Probability.Sampling.FiniteSampling
import Tengoku.Nlalib.NLAlib.Matrix.Norms.Core
import Tengoku.Nlalib.NLAlib.ForMathlib.Probability.SampleAverage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Sampled approximate matrix multiplication

The actual finite product law of independent column/row draws gives an exact
Frobenius variance identity. Sources: operator re-derivation `sa:amm-variance`
and `sa:amm-theorem`; Drineas–Kannan–Mahoney 2006.
Atlas: `amm-sampling`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal ENNReal Matrix.Norms.Frobenius
namespace NLAlib

/-- A complex outer product has Frobenius norm squared equal to the product of
the two squared Euclidean norms. Source: operator re-derivation `sa:amm-variance`.
(Moved from the deleted `NLAlib.Matrix.Norms.ComplexFrobenius`, foundation change F1.)
@isnad1 id=eq.0h4v.s7.83602ec70730 from=translated src=- shape=55c874a0 vocab=3fd79901
-/
theorem frobenius_norm_sq_vecMulVec {m n : Type*} [Fintype m] [Fintype n]
    (a : m → ℂ) (b : n → ℂ) :
    ‖Matrix.vecMulVec a b‖ ^ 2 = (∑ i, ‖a i‖ ^ 2) * ∑ j, ‖b j‖ ^ 2 := by
  rw [frobenius_norm_sq_eq_sum_norm_sq, Finset.sum_mul_sum]
  simp only [Matrix.vecMulVec_apply, norm_mul, mul_pow]

/-- Embedding a real matrix into complex entries identifies its complex
Frobenius norm squared with `frobSq`. Source: operator re-derivation `sa:amm`.
(Moved from the deleted `NLAlib.Matrix.Norms.ComplexFrobenius`, foundation change F1.)
@isnad1 id=eq.0h3v.s6.c24350232c5e from=translated src=- shape=27475c3c vocab=4f2e46ae
-/
theorem frobenius_norm_sq_map_ofReal_eq_frobSq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : ‖A.map Complex.ofReal‖ ^ 2 = frobSq A := by
  rw [frobenius_norm_sq_eq_sum_norm_sq, frobSq_eq_sum_sq]
  simp only [Matrix.map_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The squared Frobenius error of a finite matrix sample average is exactly
the one-sample variance divided by the sample count. Every expectation is
under the genuine independent product sampling law. Source: operator
re-derivation `sa:amm-variance`; helper for `amm-sampling`.
@isnad1 id=eq.2h6v.s9.91b0da7340ea from=translated src=- shape=c52a7e39 vocab=61bceeaa
-/
theorem integral_frobenius_average_sub_mean_sq
    {ι m n : Type*} [Fintype ι] [Fintype m] [Fintype n]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (p : ι → ℝ≥0) (hp : ∑ i, p i = 1) (Z : ι → Matrix m n ℂ)
    {c : ℕ} (hc : 0 < c) :
    ∫ ω : Fin c → ι,
        ‖(1 / (c : ℝ)) • ∑ j, Z (ω j) - ∑ i, (p i : ℝ) • Z i‖ ^ 2
      ∂Measure.pi (fun _ => finiteSamplingLaw p hp) =
      (1 / (c : ℝ)) * (∑ i, (p i : ℝ) * ‖Z i‖ ^ 2 -
        ‖∑ i, (p i : ℝ) • Z i‖ ^ 2) := by
  classical
  simp_rw [frobenius_norm_sq_eq_sum_norm_sq]
  rw [integral_finsetSum _ (fun _ _ => .of_finite)]
  simp_rw [integral_finsetSum _ (fun _ _ => .of_finite)]
  have hentry : ∀ ω : Fin c → ι, ∀ a b,
      ((1 / (c : ℝ)) • ∑ j, Z (ω j) - ∑ i, (p i : ℝ) • Z i) a b =
      (1 / (c : ℝ)) • ∑ j, Z (ω j) a b - ∑ i, (p i : ℝ) • Z i a b := by
    intro ω a b
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.sum_apply]
  simp_rw [hentry]
  have hscalar : ∀ a b,
      ∫ ω : Fin c → ι,
          ‖(1 / (c : ℝ)) • ∑ j, Z (ω j) a b - ∑ i, (p i : ℝ) • Z i a b‖ ^ 2
        ∂Measure.pi (fun _ => finiteSamplingLaw p hp) =
        (1 / (c : ℝ)) * (∑ i, (p i : ℝ) * ‖Z i a b‖ ^ 2 -
          ‖∑ i, (p i : ℝ) • Z i a b‖ ^ 2) := by
    intro a b
    have h := integral_centered_average_norm_sq_pi (finiteSamplingLaw p hp)
      (fun i => Z i a b) hc
    simpa only [integral_finiteSamplingLaw, smul_eq_mul] using h
  simp_rw [hscalar, Matrix.sum_apply, Matrix.smul_apply]
  simp only [mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
  have hswap : (∑ a, ∑ b, ∑ i, (1 / (c : ℝ)) * ((p i : ℝ) * ‖Z i a b‖ ^ 2)) =
      ∑ i, ∑ a, ∑ b, (1 / (c : ℝ)) * ((p i : ℝ) * ‖Z i a b‖ ^ 2) := by
    calc
      _ = (∑ a, ∑ i, ∑ b, (1 / (c : ℝ)) * ((p i : ℝ) * ‖Z i a b‖ ^ 2)) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm
  rw [hswap]

/-- One inverse-probability rescaled column/row product.
Source: operator re-derivation `sa:amm`. Zero probability uses totalized inverse.-/
def columnRowSample {m n t : Type*} (A : Matrix m n ℂ) (B : Matrix n t ℂ)
    (p : n → ℝ≥0) (i : n) : Matrix m t ℂ :=
  (p i : ℝ)⁻¹ • Matrix.vecMulVec (fun a => A a i) (fun b => B i b)

/-- Sampled columns, rescaled by `1/√(c p_i)`, over `ℝ` or `ℂ` (any `RCLike` field; the
rescaling is a real scalar). Source: operator re-derivation `sa:amm-theorem`.-/
def sampledColumnMatrix {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} (A : Matrix m n 𝕜)
    (p : n → ℝ≥0) {c : ℕ} (ω : Fin c → n) : Matrix m (Fin c) 𝕜 :=
  fun a j => (Real.sqrt ((c : ℝ) * p (ω j)))⁻¹ • A a (ω j)

/-- Sampled rows, rescaled by `1/√(c p_i)`, over `ℝ` or `ℂ` (any `RCLike` field; the
rescaling is a real scalar). Source: operator re-derivation `sa:amm-theorem`.-/
def sampledRowMatrix {𝕜 : Type*} [RCLike 𝕜] {n t : Type*} (B : Matrix n t 𝕜) (p : n → ℝ≥0)
    {c : ℕ} (ω : Fin c → n) : Matrix (Fin c) t 𝕜 :=
  fun j b => (Real.sqrt ((c : ℝ) * p (ω j)))⁻¹ • B (ω j) b

/-- Selecting and rescaling rows commutes with a deterministic linear map on columns.
This identity applies to the literal inverse-probability sampling algorithm.
@isnad1 id=eq.0h9v.s7.30cec5aefeb2 from=translated src=- shape=dcb50dc9 vocab=71dff690
-/
theorem sampledRowMatrix_mul {𝕜 : Type*} [RCLike 𝕜] {m n q : Type*} [Fintype n]
    (A : Matrix m n 𝕜) (D : Matrix n q 𝕜) (p : m → ℝ≥0) {s : ℕ} (ω : Fin s → m) :
    sampledRowMatrix (A * D) p ω = sampledRowMatrix A p ω * D := by
  ext j b
  simp only [sampledRowMatrix, Matrix.mul_apply, Finset.smul_sum, smul_mul_assoc]

/-- The product of the literally sampled and rescaled columns and rows is
the average of the inverse-probability outer products, even for zero-mass
indices. Source: operator re-derivation `sa:amm-theorem`.
@isnad1 id=eq.0h8v.s7.de3af9301540 from=translated src=- shape=46e8b45f vocab=a906dcd5
-/
theorem sampledColumnMatrix_mul_sampledRowMatrix
    {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
    (A : Matrix m n ℂ) (B : Matrix n t ℂ) (p : n → ℝ≥0)
    {c : ℕ} (ω : Fin c → n) :
    sampledColumnMatrix A p ω * sampledRowMatrix B p ω =
      (1 / (c : ℝ)) • ∑ j, columnRowSample A B p (ω j) := by
  classical
  ext a b
  simp only [sampledColumnMatrix, sampledRowMatrix, Matrix.mul_apply, Matrix.smul_apply,
    Matrix.sum_apply, columnRowSample, Matrix.vecMulVec_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hscale : (Real.sqrt ((c : ℝ) * p (ω j)))⁻¹ ^ 2 =
      (1 / (c : ℝ)) * (p (ω j) : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity), mul_inv, one_div]
  simp only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul]
  rw [← sq, hscale]

/-- The inverse-probability column/row sample is unbiased under the actual
finite law. Zero-probability indices are allowed when their outer product is
zero. Source: operator re-derivation `sa:amm`.
@isnad1 id=eq.1h6v.s7.03081ee7d367 from=translated src=- shape=5bc887d6 vocab=110a0978
-/
theorem sum_probability_smul_columnRowSample
    {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
    (A : Matrix m n ℂ) (B : Matrix n t ℂ) (p : n → ℝ≥0)
    (hsupport : ∀ i, p i = 0 → Matrix.vecMulVec (fun a => A a i) (fun b => B i b) = 0) :
    ∑ i, (p i : ℝ) • columnRowSample A B p i = A * B := by
  classical
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, columnRowSample, Matrix.vecMulVec_apply,
    Matrix.mul_apply, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : p i = 0
  · have hzero := congrArg (fun M : Matrix m t ℂ => M a b) (hsupport i hi)
    simpa only [hi, NNReal.coe_zero, inv_zero, mul_zero, zero_smul, Matrix.vecMulVec_apply,
      Matrix.zero_apply] using hzero.symm
  · rw [mul_inv_cancel₀ (show (p i : ℝ) ≠ 0 by exact_mod_cast hi), one_smul]

/-- The second moment of the inverse-probability column/row sample is the
finite sum of squared column and row norms divided by their probabilities.
Source: operator re-derivation `sa:amm`.
@isnad1 id=eq.0h6v.s7.39826f479f53 from=translated src=- shape=1124f938 vocab=6fb30475
-/
theorem sum_probability_mul_frobenius_columnRowSample_sq
    {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
    (A : Matrix m n ℂ) (B : Matrix n t ℂ) (p : n → ℝ≥0) :
    ∑ i, (p i : ℝ) * ‖columnRowSample A B p i‖ ^ 2 =
      ∑ i, ((∑ a, ‖A a i‖ ^ 2) * ∑ b, ‖B i b‖ ^ 2) / p i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [columnRowSample, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (p i).coe_nonneg), mul_pow,
    frobenius_norm_sq_vecMulVec]
  by_cases hi : (p i : ℝ) = 0
  · simp [hi]
  · field_simp

/-- Exact Frobenius mean-square error for independently sampled, literally
rescaled columns and rows, with arbitrary admissible probabilities and
possibly zero probability on zero outer products. This includes complex
matrices and correlated entries of the deterministic factors.
Source: operator re-derivation `sa:amm-variance` and `sa:amm-theorem`.
atlas: amm-sampling (partial)
@isnad1 id=eq.3h7v.s8.895a188f4c0f from=translated src=- shape=5113dbce vocab=55ecb67e
-/
theorem integral_frobenius_sampled_mul_sub_sq
    {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
    [MeasurableSpace n] [MeasurableSingletonClass n]
    (A : Matrix m n ℂ) (B : Matrix n t ℂ) (p : n → ℝ≥0)
    (hp : ∑ i, p i = 1)
    (hsupport : ∀ i, p i = 0 → Matrix.vecMulVec (fun a => A a i) (fun b => B i b) = 0)
    {c : ℕ} (hc : 0 < c) :
    ∫ ω : Fin c → n, ‖sampledColumnMatrix A p ω * sampledRowMatrix B p ω - A * B‖ ^ 2
      ∂Measure.pi (fun _ => finiteSamplingLaw p hp) =
      (1 / (c : ℝ)) *
        (∑ i, ((∑ a, ‖A a i‖ ^ 2) * ∑ b, ‖B i b‖ ^ 2) / p i - ‖A * B‖ ^ 2) := by
  simp_rw [sampledColumnMatrix_mul_sampledRowMatrix]
  have h := integral_frobenius_average_sub_mean_sq p hp (columnRowSample A B p) hc
  rwa [sum_probability_smul_columnRowSample A B p hsupport,
    sum_probability_mul_frobenius_columnRowSample_sq] at h

/-- The product of a column's Euclidean norm and its corresponding row norm,
which specifies the variance-minimizing finite sampling law.
Source: operator re-derivation `sa:amm-theorem`.-/
def columnRowWeight {m n t 𝕜 : Type*} [Fintype m] [Fintype t] [NormedAddCommGroup 𝕜]
    (A : Matrix m n 𝕜) (B : Matrix n t 𝕜) (i : n) : ℝ :=
  Real.sqrt (∑ a, ‖A a i‖ ^ 2) * Real.sqrt (∑ b, ‖B i b‖ ^ 2)

/-- Column/row weights are nonnegative.
Source: operator re-derivation `sa:amm-theorem`.
@isnad1 id=le.0h7v.s5.da08725c05f7 from=translated src=- shape=ec49d41d vocab=24b0f62e
-/
theorem columnRowWeight_nonneg {m n t 𝕜 : Type*} [Fintype m] [Fintype t] [NormedAddCommGroup 𝕜]
    (A : Matrix m n 𝕜) (B : Matrix n t 𝕜) (i : n) : 0 ≤ columnRowWeight A B i := by
  unfold columnRowWeight
  positivity

/-- The square of a column/row weight is the outer product's squared Frobenius
norm. Source: operator re-derivation `sa:amm-variance`.
@isnad1 id=eq.0h7v.s7.5d63b7a97286 from=translated src=- shape=da1cb557 vocab=8c224d40
-/
theorem columnRowWeight_sq {m n t 𝕜 : Type*} [Fintype m] [Fintype t] [NormedAddCommGroup 𝕜]
    (A : Matrix m n 𝕜) (B : Matrix n t 𝕜) (i : n) :
    columnRowWeight A B i ^ 2 = (∑ a, ‖A a i‖ ^ 2) * ∑ b, ‖B i b‖ ^ 2 := by
  rw [columnRowWeight, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

/-- A zero column/row weight means that its literal outer product is zero.
Source: operator re-derivation `sa:amm-theorem`.
@isnad1 id=eq.1h6v.s6.16ec99b374f5 from=translated src=- shape=fad10231 vocab=449149e5
-/
theorem vecMulVec_eq_zero_of_columnRowWeight_eq_zero
    {m n t : Type*} [Fintype m] [Fintype t]
    (A : Matrix m n ℂ) (B : Matrix n t ℂ) (i : n)
    (hi : columnRowWeight A B i = 0) :
    Matrix.vecMulVec (fun a => A a i) (fun b => B i b) = 0 := by
  have hn : ‖Matrix.vecMulVec (fun a => A a i) (fun b => B i b)‖ ^ 2 = 0 := by
    rw [frobenius_norm_sq_vecMulVec, ← columnRowWeight_sq, hi, zero_pow (by decide)]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

/-- The normalized column/row weights as nonnegative real probabilities.
The accompanying sum-to-one theorem applies when the total weight is positive.
Source: operator re-derivation `sa:amm-theorem`.-/
def columnRowProbabilities {m n t 𝕜 : Type*} [Fintype m] [Fintype n] [Fintype t]
    [NormedAddCommGroup 𝕜] (A : Matrix m n 𝕜) (B : Matrix n t 𝕜) : n → ℝ≥0 := fun i =>
  Real.toNNReal (columnRowWeight A B i / ∑ j, columnRowWeight A B j)

/-- Positive total weight makes the normalized sampling probabilities sum to one.
Source: operator re-derivation `sa:amm-theorem`.
@isnad1 id=eq.1h6v.s6.3341d72c52ca from=translated src=- shape=c0f5d0da vocab=32b5c76e
-/
theorem sum_columnRowProbabilities {m n t 𝕜 : Type*} [Fintype m] [Fintype n] [Fintype t]
    [NormedAddCommGroup 𝕜] (A : Matrix m n 𝕜) (B : Matrix n t 𝕜)
    (hW : 0 < ∑ i, columnRowWeight A B i) : ∑ i, columnRowProbabilities A B i = 1 := by
  apply NNReal.coe_injective
  rw [NNReal.coe_sum, NNReal.coe_one]
  simp only [columnRowProbabilities, Real.coe_toNNReal _
    (div_nonneg (columnRowWeight_nonneg A B _) hW.le)]
  rw [← Finset.sum_div, div_self hW.ne']

/-- Cauchy–Schwarz bounds the squared total column/row weight by the product
of the factor Frobenius norms squared. Source: operator re-derivation `sa:amm-theorem`.
@isnad1 id=le.0h5v.s7.1fbc2d097a7b from=translated src=- shape=2555febb vocab=46423ccd
-/
theorem sum_columnRowWeight_sq_le
    {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
    (A : Matrix m n ℂ) (B : Matrix n t ℂ) :
    (∑ i, columnRowWeight A B i) ^ 2 ≤ ‖A‖ ^ 2 * ‖B‖ ^ 2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => Finset.sum_nonneg (fun a _ => sq_nonneg ‖A a i‖))
    (fun i _ => Finset.sum_nonneg (fun b _ => sq_nonneg ‖B i b‖))
    (fun i _ => (columnRowWeight_sq A B i).le)
  rw [frobenius_norm_sq_eq_sum_norm_sq, frobenius_norm_sq_eq_sum_norm_sq,
    Finset.sum_comm (f := fun a i => ‖A a i‖ ^ 2)]
  exact h

/-- With normalized column/row weights, the genuine sampled and rescaled
product has exact mean-square error `(W² − ‖AB‖F²)/c`, bounded by
`‖A‖F² ‖B‖F²/c`. Complex matrices, zero-weight support, and repeated draws
are included; the sample count is positive as in the source.
Source: operator re-derivation `sa:amm-theorem`; Drineas–Kannan–Mahoney 2006.
atlas: amm-sampling
@isnad1 id=and.2h6v.s9.958beff9ead5 from=translated src=- shape=4a168d66 vocab=efda6c53
-/
theorem integral_frobenius_sampled_mul_sub_sq_of_columnRowProbabilities
    {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
    [MeasurableSpace n] [MeasurableSingletonClass n]
    (A : Matrix m n ℂ) (B : Matrix n t ℂ)
    (hW : 0 < ∑ i, columnRowWeight A B i) {c : ℕ} (hc : 0 < c) :
    (∫ ω : Fin c → n,
      ‖sampledColumnMatrix A (columnRowProbabilities A B) ω *
        sampledRowMatrix B (columnRowProbabilities A B) ω - A * B‖ ^ 2
      ∂Measure.pi (fun _ => finiteSamplingLaw (columnRowProbabilities A B)
        (sum_columnRowProbabilities A B hW))) =
      ((∑ i, columnRowWeight A B i) ^ 2 - ‖A * B‖ ^ 2) / (c : ℝ) ∧
    (∫ ω : Fin c → n,
      ‖sampledColumnMatrix A (columnRowProbabilities A B) ω *
        sampledRowMatrix B (columnRowProbabilities A B) ω - A * B‖ ^ 2
      ∂Measure.pi (fun _ => finiteSamplingLaw (columnRowProbabilities A B)
        (sum_columnRowProbabilities A B hW))) ≤ ‖A‖ ^ 2 * ‖B‖ ^ 2 / (c : ℝ) := by
  classical
  have hp : ∀ i, (columnRowProbabilities A B i : ℝ) =
      columnRowWeight A B i / ∑ j, columnRowWeight A B j := by
    intro i
    exact Real.coe_toNNReal _ (div_nonneg (columnRowWeight_nonneg A B i) hW.le)
  have hsupp : ∀ i, columnRowProbabilities A B i = 0 →
      Matrix.vecMulVec (fun a => A a i) (fun b => B i b) = 0 := by
    intro i hi
    apply vecMulVec_eq_zero_of_columnRowWeight_eq_zero A B i
    have hzero : (columnRowProbabilities A B i : ℝ) = 0 := by rw [hi]; rfl
    rw [hp i, div_eq_zero_iff] at hzero
    exact hzero.resolve_right hW.ne'
  have hmom : (∑ i, ((∑ a, ‖A a i‖ ^ 2) * ∑ b, ‖B i b‖ ^ 2) /
      columnRowProbabilities A B i) = (∑ i, columnRowWeight A B i) ^ 2 := by
    simp_rw [← columnRowWeight_sq, hp]
    have hterm : ∀ i, columnRowWeight A B i ^ 2 /
        (columnRowWeight A B i / ∑ j, columnRowWeight A B j) =
        (∑ j, columnRowWeight A B j) * columnRowWeight A B i := by
      intro i
      by_cases hi : columnRowWeight A B i = 0
      · simp [hi]
      · field_simp
    simp_rw [hterm]
    rw [← Finset.mul_sum, pow_two]
  have heq := integral_frobenius_sampled_mul_sub_sq A B (columnRowProbabilities A B)
    (sum_columnRowProbabilities A B hW) hsupp hc
  rw [hmom, one_div_mul_eq_div] at heq
  refine ⟨heq, ?_⟩
  rw [heq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (sub_le_self _ (sq_nonneg _)).trans (sum_columnRowWeight_sq_le A B)

/-- If all column/row weights vanish, then the product itself is zero and the
zero output is exact without normalizing a zero law. This includes an empty
shared index type. Source: operator re-derivation `sa:amm-theorem`.
atlas: amm-sampling
@isnad1 id=eq.1h5v.s6.b7d5f9b86edd from=translated src=- shape=6e61dcdc vocab=ec8ef2fc
-/
theorem mul_eq_zero_of_sum_columnRowWeight_eq_zero
    {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
    (A : Matrix m n ℂ) (B : Matrix n t ℂ) (hW : ∑ i, columnRowWeight A B i = 0) :
    A * B = 0 := by
  have hw : ∀ i, columnRowWeight A B i = 0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => columnRowWeight_nonneg A B i)).mp hW
    exact fun i => hh i (Finset.mem_univ i)
  have h := sum_probability_smul_columnRowSample A B (fun _ => (0 : ℝ≥0))
    (fun i _ => vecMulVec_eq_zero_of_columnRowWeight_eq_zero A B i (hw i))
  simpa using h.symm

/-- Real column sampling embeds into the complex sampling construction.
Source: operator re-derivation `sa:amm-theorem`.
@isnad1 id=eq.0h6v.s5.6fa1f75a86f2 from=translated src=- shape=84f697c5 vocab=d9cababb
-/
theorem sampledColumnMatrix_map_ofReal {m n : Type*}
    (A : Matrix m n ℝ) (p : n → ℝ≥0) {c : ℕ} (ω : Fin c → n) :
    sampledColumnMatrix (A.map Complex.ofReal) p ω =
      (sampledColumnMatrix A p ω).map Complex.ofReal := by
  ext a j
  simp [sampledColumnMatrix, Matrix.map_apply, Complex.real_smul]

/-- Real row sampling embeds into the complex sampling construction.
Source: operator re-derivation `sa:amm-theorem`.
@isnad1 id=eq.0h6v.s5.02cbd01f10c6 from=translated src=- shape=114e5a02 vocab=98a239c5
-/
theorem sampledRowMatrix_map_ofReal {n t : Type*}
    (B : Matrix n t ℝ) (p : n → ℝ≥0) {c : ℕ} (ω : Fin c → n) :
    sampledRowMatrix (B.map Complex.ofReal) p ω =
      (sampledRowMatrix B p ω).map Complex.ofReal := by
  ext j b
  simp [sampledRowMatrix, Matrix.map_apply, Complex.real_smul]

/-- The real normalized column/row sampling law has the same exact error
identity and Frobenius upper bound, stated using NLAlib's `frobSq`.
Source: operator re-derivation `sa:amm-theorem`.
atlas: amm-sampling
@isnad1 id=and.2h6v.s9.d36710e38e40 from=translated src=- shape=edc2ccc2 vocab=3872e3ba
-/
theorem integral_frobSq_sampled_mul_sub_of_columnRowProbabilities
    {m n t : Type*} [Fintype m] [Fintype n] [Fintype t]
    [MeasurableSpace n] [MeasurableSingletonClass n]
    (A : Matrix m n ℝ) (B : Matrix n t ℝ)
    (hW : 0 < ∑ i, columnRowWeight A B i) {c : ℕ} (hc : 0 < c) :
    (∫ ω : Fin c → n,
      frobSq (sampledColumnMatrix A (columnRowProbabilities A B) ω *
        sampledRowMatrix B (columnRowProbabilities A B) ω - A * B)
      ∂Measure.pi (fun _ => finiteSamplingLaw (columnRowProbabilities A B)
        (sum_columnRowProbabilities A B hW))) =
      ((∑ i, columnRowWeight A B i) ^ 2 - frobSq (A * B)) / (c : ℝ) ∧
    (∫ ω : Fin c → n,
      frobSq (sampledColumnMatrix A (columnRowProbabilities A B) ω *
        sampledRowMatrix B (columnRowProbabilities A B) ω - A * B)
      ∂Measure.pi (fun _ => finiteSamplingLaw (columnRowProbabilities A B)
        (sum_columnRowProbabilities A B hW))) ≤ frobSq A * frobSq B / (c : ℝ) := by
  have hw : columnRowWeight (A.map Complex.ofReal) (B.map Complex.ofReal) =
      columnRowWeight A B := by
    funext i
    simp [columnRowWeight, Matrix.map_apply]
  have hp : columnRowProbabilities (A.map Complex.ofReal) (B.map Complex.ofReal) =
      columnRowProbabilities A B := by
    unfold columnRowProbabilities
    rw [hw]
  have h := integral_frobenius_sampled_mul_sub_sq_of_columnRowProbabilities
    (A.map Complex.ofReal) (B.map Complex.ofReal) (by rwa [hw]) hc
  simp only [hp, hw, sampledColumnMatrix_map_ofReal, sampledRowMatrix_map_ofReal] at h
  have hmap : ∀ X : Matrix m (Fin c) ℝ, ∀ Y : Matrix (Fin c) t ℝ,
      X.map Complex.ofReal * Y.map Complex.ofReal -
        A.map Complex.ofReal * B.map Complex.ofReal =
        (X * Y - A * B).map Complex.ofReal := by
    intro X Y
    ext a b
    simp [Matrix.mul_apply, Matrix.map_apply, Complex.ofReal_sum]
  simp_rw [hmap, frobenius_norm_sq_map_ofReal_eq_frobSq] at h
  have hAB : A.map Complex.ofReal * B.map Complex.ofReal =
      (A * B).map Complex.ofReal := (Matrix.map_mul (f := Complex.ofRealHom)).symm
  rwa [hAB, frobenius_norm_sq_map_ofReal_eq_frobSq] at h

/-- With zero samples the literal sampled product is zero; no positive-count
variance formula is asserted. Source: the boundary convention of `sa:amm-theorem`.
@isnad1 id=eq.0h7v.s6.e10484bf888a from=translated src=- shape=18a5f097 vocab=3214c678
-/
theorem sampledColumnMatrix_mul_sampledRowMatrix_zero_samples
    {m n t : Type*} (A : Matrix m n ℂ) (B : Matrix n t ℂ) (p : n → ℝ≥0)
    (ω : Fin 0 → n) : sampledColumnMatrix A p ω * sampledRowMatrix B p ω = 0 := by
  ext a b
  simp [Matrix.mul_apply]

end NLAlib
