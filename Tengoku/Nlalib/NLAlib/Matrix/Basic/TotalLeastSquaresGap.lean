import Tengoku.Nlalib.NLAlib.Matrix.Basic.TotalLeastSquaresInfimum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!+# Strict-gap total least squares

A data-Gram minimum strictly above the augmented-Gram minimum makes the
shifted data Gram positive definite. The first block of every minimum
eigenvector then gives the explicit unique finite TLS solution.

Source: Golub–Van Loan (2013), §5.5; matrix-toolkit re-derivation §29.
Atlas: `total-least-squares-svd`.
-/
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*}
  [Fintype m] [Fintype n] [DecidableEq n] [Nonempty n]

/-- Multiplication by the augmented data matrix separates its data and
right-hand-side blocks.
@isnad1 id=eq.0h6v.s7.c5c090b400f0 from=translated src=- shape=1e6bb04f vocab=3d66fb6b
-/
theorem tlsDataMatrix_mulVec (A : Matrix m n 𝕜) (b : m → 𝕜) (v : n ⊕ Unit → 𝕜) :
    tlsDataMatrix A b *ᵥ v = A *ᵥ (v ∘ Sum.inl) + v (Sum.inr ()) • b := by
  rw [tlsDataMatrix, Matrix.fromCols_mulVec]
  congr 1
  ext i
  simp [Matrix.mulVec, dotProduct, smul_eq_mul, mul_comm]

/-- The first block of a minimum augmented-Gram eigenvector equation.
@isnad1 id=eq.1h6v.s9.de4f2798f0fd from=translated src=- shape=3217be91 vocab=9edb90c6
-/
theorem tls_minimum_eigenvector_first_block (A : Matrix m n 𝕜) (b : m → 𝕜)
    (v : n ⊕ Unit → 𝕜)
    (he : ((tlsDataMatrix A b)ᴴ * tlsDataMatrix A b) *ᵥ v = (tlsValue A b : 𝕜) • v) :
    (Aᴴ * A - (tlsValue A b : 𝕜) • 1) *ᵥ (v ∘ Sum.inl) =
      -(v (Sum.inr ()) • (Aᴴ *ᵥ b)) := by
  have hh : Aᴴ *ᵥ (tlsDataMatrix A b *ᵥ v) = (tlsValue A b : 𝕜) • (v ∘ Sum.inl) := by
    rw [← Matrix.mulVec_mulVec] at he
    ext i
    exact congrFun he (Sum.inl i)
  rw [tlsDataMatrix_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec] at hh
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  linear_combination hh

/-- Under the strict gap no nonzero minimum eigenvector can have a zero
last coordinate. The inverse is justified by a positive definite matrix.
@isnad1 id=ne.3h6v.s8.53b3bf7650e1 from=translated src=- shape=f258f43f vocab=e331fcc0
-/
theorem tls_minimum_eigenvector_last_ne_zero_of_gap (A : Matrix m n 𝕜) (b : m → 𝕜)
    (hgap : tlsValue A b < lambdaMin (Aᴴ * A)) (v : n ⊕ Unit → 𝕜)
    (hv : v ≠ 0)
    (he : ((tlsDataMatrix A b)ᴴ * tlsDataMatrix A b) *ᵥ v = (tlsValue A b : 𝕜) • v) :
    v (Sum.inr ()) ≠ 0 := by
  have hP := (Matrix.isHermitian_conjTranspose_mul_self A).posDef_sub_smul_one_of_lt_lambdaMin hgap
  intro hz
  have hh := tls_minimum_eigenvector_first_block A b v he
  rw [hz, zero_smul, neg_zero] at hh
  have hhead : v ∘ Sum.inl = 0 := Matrix.mulVec_injective_iff_isUnit.mpr hP.isUnit
    (by simpa only [Matrix.mulVec_zero] using hh)
  apply hv
  ext i
  cases i with
  | inl i => exact congrFun hhead i
  | inr i => cases i; exact hz

/-- Every minimum eigenvector chart point is the strict-gap inverse
formula. The denominator is explicitly proved nonzero first.
@isnad1 id=eq.3h6v.s9.3e784c68a01d from=translated src=- shape=2d148d1f vocab=686e5594
-/
theorem tlsSolutionOfVector_eq_inverse_of_gap (A : Matrix m n 𝕜) (b : m → 𝕜)
    (hgap : tlsValue A b < lambdaMin (Aᴴ * A)) (v : n ⊕ Unit → 𝕜) (hv : v ≠ 0)
    (he : ((tlsDataMatrix A b)ᴴ * tlsDataMatrix A b) *ᵥ v = (tlsValue A b : 𝕜) • v) :
    tlsSolutionOfVector v = (Aᴴ * A - (tlsValue A b : 𝕜) • 1)⁻¹ *ᵥ (Aᴴ *ᵥ b) := by
  let P := Aᴴ * A - (tlsValue A b : 𝕜) • 1
  have hP : P.PosDef :=
    (Matrix.isHermitian_conjTranspose_mul_self A).posDef_sub_smul_one_of_lt_lambdaMin hgap
  have hlast := tls_minimum_eigenvector_last_ne_zero_of_gap A b hgap v hv he
  have hh := congrArg (fun w => P⁻¹ *ᵥ w) (tls_minimum_eigenvector_first_block A b v he)
  change P⁻¹ *ᵥ (P *ᵥ (v ∘ Sum.inl)) = P⁻¹ *ᵥ (-(v (Sum.inr ()) • (Aᴴ *ᵥ b))) at hh
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit),
    Matrix.one_mulVec, Matrix.mulVec_neg, Matrix.mulVec_smul] at hh
  ext i
  have hi := congrFun hh i
  change -v (Sum.inl i) / v (Sum.inr ()) = (P⁻¹ *ᵥ (Aᴴ *ᵥ b)) i
  change v (Sum.inl i) = -(v (Sum.inr ()) * (P⁻¹ *ᵥ (Aᴴ *ᵥ b)) i) at hi
  rw [hi]
  field_simp

/-- The strict gap guarantees attainment and gives precisely one TLS
solution, equal to the classical shifted normal inverse formula.
atlas: total-least-squares-svd (partial)
@isnad1 id=iff.1h6v.s9.6b1cd5178fe2 from=translated src=- shape=5a8ce78d vocab=532004c8
-/
theorem isTLSOptimal_iff_eq_inverse_of_gap (A : Matrix m n 𝕜) (b : m → 𝕜)
    (hgap : tlsValue A b < lambdaMin (Aᴴ * A)) (x : n → 𝕜) :
    IsTLSOptimal A b x ↔ x = (Aᴴ * A - (tlsValue A b : 𝕜) • 1)⁻¹ *ᵥ (Aᴴ *ᵥ b) := by
  constructor
  · intro hx
    obtain ⟨v, hv, _, he, hchart⟩ := (isTLSOptimal_iff_minimum_eigenvector_chart A b x).mp hx
    have hv0 : v ≠ 0 := by intro hh; simp [hh] at hv
    exact hchart.trans (tlsSolutionOfVector_eq_inverse_of_gap A b hgap v hv0 he)
  · intro hx
    obtain ⟨v, hv, he⟩ := (Matrix.isHermitian_conjTranspose_mul_self (tlsDataMatrix A b)).exists_unit_lambdaMin_eigenvector
    have hv0 : v ≠ 0 := by intro hh; simp [hh] at hv
    have hl := tls_minimum_eigenvector_last_ne_zero_of_gap A b hgap v hv0 he
    apply (isTLSOptimal_iff_minimum_eigenvector_chart A b x).mpr
    exact ⟨v, hv, hl, he, hx.trans (tlsSolutionOfVector_eq_inverse_of_gap A b hgap v hv0 he).symm⟩

end NLAlib
