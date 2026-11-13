import Tengoku.Nlalib.NLAlib.Matrix.Basic.RankOneCorrection
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.HermitianMinimum
import Tengoku.Seed.Data.Matrix.ColumnRowPartitioned

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!+# Total least squares and the minimum-eigenvector chart

The data correction is one augmented matrix `[E f]`. A finite solution
corresponds precisely to a direction with nonzero last coordinate.
Minimum eigenvalues are taken on the full augmented domain, retaining
all zero eigenvalues and the whole minimum eigenspace.

Source: Golub–Van Loan (2013), §5.5; matrix-toolkit re-derivation §29.
Atlas: `total-least-squares-svd`.
-/
noncomputable section
open Matrix
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

/-- The augmented data matrix `[A b]`.-/
def tlsDataMatrix (A : Matrix m n 𝕜) (b : m → 𝕜) : Matrix m (n ⊕ Unit) 𝕜 :=
  Matrix.fromCols A (Matrix.replicateCol Unit b)

/-- The full-domain smallest augmented Gram eigenvalue.-/
def tlsValue (A : Matrix m n 𝕜) (b : m → 𝕜) : ℝ :=
  lambdaMin ((tlsDataMatrix A b)ᴴ * tlsDataMatrix A b)

/-- The finite-solution chart direction `(x,-1)`.-/
def tlsDirection (x : n → 𝕜) : n ⊕ Unit → 𝕜 := Sum.elim x (fun _ => -1)

/-- The affine solution associated with a nonzero last coordinate. Uses
are always guarded by that explicit nonzero-coordinate hypothesis.-/
def tlsSolutionOfVector (v : n ⊕ Unit → 𝕜) : n → 𝕜 :=
  fun i => -v (Sum.inl i) / v (Sum.inr ())

/-- Normalize a nonzero coordinate vector in its Euclidean norm.-/
def unitNormalize {ι : Type*} [Fintype ι] (v : ι → 𝕜) : ι → 𝕜 :=
  ((‖WithLp.toLp 2 v‖ : 𝕜)⁻¹) • v

/-- A normalized nonzero vector has Euclidean norm one.
@isnad1 id=eq.1h3v.s6.b58ac67c121a from=translated src=- shape=a85c183a vocab=c54ffcc8
-/
theorem norm_unitNormalize {ι : Type*} [Fintype ι] (v : ι → 𝕜) (hv : v ≠ 0) :
    ‖WithLp.toLp 2 (unitNormalize v)‖ = 1 := by
  have hn : ‖WithLp.toLp 2 v‖ ≠ 0 := by
    intro hz
    exact hv (congrArg WithLp.ofLp (norm_eq_zero.mp hz))
  simp [unitNormalize, WithLp.toLp_smul, norm_smul, norm_inv, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hn]

/-- Normalization preserves any nonzero coordinate.
@isnad1 id=ne.1h4v.s6.f59539e979b5 from=translated src=- shape=b4b92ed7 vocab=beb49326
-/
theorem unitNormalize_apply_ne_zero {ι : Type*} [Fintype ι] (v : ι → 𝕜)
    (i : ι) (hi : v i ≠ 0) : unitNormalize v i ≠ 0 := by
  have hv : v ≠ 0 := fun hh => hi (congrFun hh i)
  have hn : (‖WithLp.toLp 2 v‖ : 𝕜) ≠ 0 := by
    have hnorm : ‖WithLp.toLp 2 v‖ ≠ 0 := by
      intro hz; exact hv (congrArg WithLp.ofLp (norm_eq_zero.mp hz))
    exact_mod_cast hnorm
  exact mul_ne_zero (inv_ne_zero hn) hi

/-- Multiplication of a direction by a nonzero scalar preserves its chart point.
@isnad1 id=eq.1h4v.s6.ef424da8f512 from=translated src=- shape=056ec6e5 vocab=2b8e1120
-/
theorem tlsSolutionOfVector_smul (v : n ⊕ Unit → 𝕜) (a : 𝕜) (ha : a ≠ 0) :
    tlsSolutionOfVector (a • v) = tlsSolutionOfVector v := by
  ext i
  simp only [tlsSolutionOfVector, Pi.smul_apply, smul_eq_mul]
  field_simp

/-- A nonzero last coordinate gives precisely the finite chart direction.
@isnad1 id=eq.1h3v.s7.0a5801a8de96 from=translated src=- shape=64d91ae1 vocab=02718cb5
-/
theorem tlsDirection_solutionOfVector (v : n ⊕ Unit → 𝕜) (hv : v (Sum.inr ()) ≠ 0) :
    tlsDirection (tlsSolutionOfVector v) = -(v (Sum.inr ()))⁻¹ • v := by
  ext i
  cases i with
  | inl i => simp [tlsDirection, tlsSolutionOfVector, div_eq_mul_inv, mul_comm]
  | inr i => cases i; simp [tlsDirection, hv]

/-- Normalizing a finite chart direction returns the same finite solution.
@isnad1 id=eq.0h3v.s5.c8e9c64a8a73 from=translated src=- shape=23cc11af vocab=9ca1c6c4
-/
theorem tlsSolutionOfVector_unitNormalize_direction (x : n → 𝕜) :
    tlsSolutionOfVector (unitNormalize (tlsDirection x)) = x := by
  have hv : tlsDirection x ≠ 0 := by
    intro hh
    have he := congrFun hh (Sum.inr ())
    simpa [tlsDirection] using he
  have hn : (‖WithLp.toLp 2 (tlsDirection x)‖ : 𝕜) ≠ 0 := by
    have hh : ‖WithLp.toLp 2 (tlsDirection x)‖ ≠ 0 := by
      intro hz; exact hv (congrArg WithLp.ofLp (norm_eq_zero.mp hz))
    exact_mod_cast hh
  rw [unitNormalize, tlsSolutionOfVector_smul _ _ (inv_ne_zero hn)]
  ext i
  simp [tlsDirection, tlsSolutionOfVector]

/-- The actual total-least-squares correction constraint.-/
def IsTLSFeasible (A : Matrix m n 𝕜) (b : m → 𝕜) (x : n → 𝕜)
    (D : Matrix m (n ⊕ Unit) 𝕜) : Prop :=
  (tlsDataMatrix A b + D) *ᵥ tlsDirection x = 0

/-- The augmented constraint is exactly `(A+E)x=b+f`.
@isnad1 id=iff.0h8v.s7.2f251039de12 from=translated src=- shape=a49d8ca1 vocab=f36aa408
-/
theorem isTLSFeasible_fromCols_iff (A E : Matrix m n 𝕜) (b f : m → 𝕜) (x : n → 𝕜) :
    IsTLSFeasible A b x (Matrix.fromCols E (Matrix.replicateCol Unit f)) ↔
      (A + E) *ᵥ x = b + f := by
  simp only [IsTLSFeasible, tlsDataMatrix, tlsDirection, Matrix.add_mulVec,
    Matrix.fromCols_mulVec_sumElim]
  have hb : Matrix.replicateCol Unit b *ᵥ (fun _ => (-1 : 𝕜)) = -b := by
    ext i; simp [Matrix.mulVec, dotProduct]
  have hf : Matrix.replicateCol Unit f *ᵥ (fun _ => (-1 : 𝕜)) = -f := by
    ext i; simp [Matrix.mulVec, dotProduct]
  rw [hb, hf]
  constructor <;> intro hh <;> linear_combination hh

/-- A unit nonzero-last-coordinate direction produces an actually feasible
finite solution using the rank-one correction.
@isnad1 id=istlsfea.2h6v.s7.507b5e8900d4 from=translated src=- shape=d8d25d96 vocab=63ac3662
-/
theorem isTLSFeasible_rankOneCancel (A : Matrix m n 𝕜) (b : m → 𝕜)
    (v : n ⊕ Unit → 𝕜) (hv : ‖WithLp.toLp 2 v‖ = 1) (hlast : v (Sum.inr ()) ≠ 0) :
    IsTLSFeasible A b (tlsSolutionOfVector v) (rankOneCancel (tlsDataMatrix A b) v) := by
  rw [IsTLSFeasible, tlsDirection_solutionOfVector v hlast, Matrix.mulVec_smul,
    Matrix.add_mulVec, rankOneCancel_mulVec _ v hv, add_neg_cancel, smul_zero]

/-- Every finite feasible correction costs at least the full-domain
smallest Gram eigenvalue.
atlas: total-least-squares-svd (partial)
@isnad1 id=le.1h7v.s6.4edfe96278e2 from=translated src=- shape=6e445316 vocab=15cf31ae
-/
theorem tlsValue_le_frobSq_of_feasible (A : Matrix m n 𝕜) (b : m → 𝕜)
    (x : n → 𝕜) (D : Matrix m (n ⊕ Unit) 𝕜) (hD : IsTLSFeasible A b x D) :
    tlsValue A b ≤ frobSq D := by
  let v := unitNormalize (tlsDirection x)
  have hw : tlsDirection x ≠ 0 := by
    intro hh; have he := congrFun hh (Sum.inr ()); simpa [tlsDirection] using he
  have hv : ‖WithLp.toLp 2 v‖ = 1 := norm_unitNormalize _ hw
  have hz : (tlsDataMatrix A b + D) *ᵥ v = 0 := by
    change (tlsDataMatrix A b + D) *ᵥ unitNormalize (tlsDirection x) = 0
    rw [unitNormalize, Matrix.mulVec_smul, hD, smul_zero]
  have hcan : D *ᵥ v = -(tlsDataMatrix A b *ᵥ v) := by
    rw [Matrix.add_mulVec] at hz
    linear_combination hz
  exact (lambdaMin_gram_le_norm_mulVec_sq (tlsDataMatrix A b) hv).trans
    (frobSq_correction_minimum_iff (tlsDataMatrix A b) D v hv hcan).1

/-- Finite TLS optimality means actual feasibility with the sharp cost.-/
def IsTLSOptimal (A : Matrix m n 𝕜) (b : m → 𝕜) (x : n → 𝕜) : Prop :=
  ∃ D : Matrix m (n ⊕ Unit) 𝕜, IsTLSFeasible A b x D ∧ frobSq D = tlsValue A b

/-- All finite TLS optima are precisely the nonzero-last-coordinate
vectors in the entire minimum eigenspace. Repeated minimum eigenvalues
are included, and no division by a zero last coordinate is used.
atlas: total-least-squares-svd (partial)
@isnad1 id=iff.0h6v.s8.3777417aee30 from=translated src=- shape=72d57485 vocab=d9e74674
-/
theorem isTLSOptimal_iff_minimum_eigenvector_chart (A : Matrix m n 𝕜) (b : m → 𝕜)
    (x : n → 𝕜) : IsTLSOptimal A b x ↔
    ∃ v : n ⊕ Unit → 𝕜, ‖WithLp.toLp 2 v‖ = 1 ∧ v (Sum.inr ()) ≠ 0 ∧
      ((tlsDataMatrix A b)ᴴ * tlsDataMatrix A b) *ᵥ v = (tlsValue A b : 𝕜) • v ∧
      x = tlsSolutionOfVector v := by
  constructor
  · rintro ⟨D, hD, hcost⟩
    let v := unitNormalize (tlsDirection x)
    have hw : tlsDirection x ≠ 0 := by
      intro hh; have he := congrFun hh (Sum.inr ()); simpa [tlsDirection] using he
    have hv : ‖WithLp.toLp 2 v‖ = 1 := norm_unitNormalize _ hw
    have hlast : v (Sum.inr ()) ≠ 0 := unitNormalize_apply_ne_zero _ _ (by simp [tlsDirection])
    have hz : (tlsDataMatrix A b + D) *ᵥ v = 0 := by
      change (tlsDataMatrix A b + D) *ᵥ unitNormalize (tlsDirection x) = 0
      rw [unitNormalize, Matrix.mulVec_smul, hD, smul_zero]
    have hcan : D *ᵥ v = -(tlsDataMatrix A b *ᵥ v) := by
      rw [Matrix.add_mulVec] at hz; linear_combination hz
    have he : ‖WithLp.toLp 2 (tlsDataMatrix A b *ᵥ v)‖ ^ 2 = tlsValue A b :=
      le_antisymm (hcost ▸ (frobSq_correction_minimum_iff _ D v hv hcan).1)
        (lambdaMin_gram_le_norm_mulVec_sq _ hv)
    exact ⟨v, hv, hlast, (norm_mulVec_sq_eq_lambdaMin_gram_iff _ hv).mp he,
      (tlsSolutionOfVector_unitNormalize_direction x).symm⟩
  · rintro ⟨v, hv, hlast, he, rfl⟩
    exact ⟨rankOneCancel (tlsDataMatrix A b) v,
      isTLSFeasible_rankOneCancel A b v hv hlast,
      (frobSq_rankOneCancel _ v hv).trans ((norm_mulVec_sq_eq_lambdaMin_gram_iff _ hv).mpr he)⟩

/-- TLS attainment is equivalent to the minimum eigenspace meeting the
finite-solution chart. This remains valid when the minimum is repeated.
atlas: total-least-squares-svd (partial)
@isnad1 id=iff.0h5v.s8.20d7a1a320d4 from=translated src=- shape=704c9395 vocab=8de087ff
-/
theorem exists_isTLSOptimal_iff_minimum_eigenvector_last_ne_zero (A : Matrix m n 𝕜) (b : m → 𝕜) :
    (∃ x, IsTLSOptimal A b x) ↔
      ∃ v : n ⊕ Unit → 𝕜, ‖WithLp.toLp 2 v‖ = 1 ∧ v (Sum.inr ()) ≠ 0 ∧
        ((tlsDataMatrix A b)ᴴ * tlsDataMatrix A b) *ᵥ v = (tlsValue A b : 𝕜) • v := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨v, hv, hl, he, _⟩ := (isTLSOptimal_iff_minimum_eigenvector_chart A b x).mp hx
    exact ⟨v, hv, hl, he⟩
  · rintro ⟨v, hv, hl, he⟩
    exact ⟨tlsSolutionOfVector v,
      (isTLSOptimal_iff_minimum_eigenvector_chart A b _).mpr ⟨v, hv, hl, he, rfl⟩⟩

end NLAlib
