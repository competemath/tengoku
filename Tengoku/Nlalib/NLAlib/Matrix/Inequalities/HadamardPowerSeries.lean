import Tengoku.Nlalib.NLAlib.Matrix.Basic.PositiveSemidefiniteSeries
import Tengoku.Seed.Analysis.SpecialFunctions.Exponential

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Positive-coefficient entrywise power series

Every natural Hadamard power is PSD, including the zeroth all-ones power.
Convergent nonnegative-coefficient series preserve PSD membership. The
formal analytic radius supplies the source radius condition, and the
entrywise exponential is a specialization.
Source: Horn--Johnson (2013), Theorems 7.5.3 and 7.5.9;
atlas `schur-product-inequalities`.
-/

noncomputable section
open Matrix Filter
open scoped Matrix MatrixOrder Topology
namespace NLAlib
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n]

/-- Every natural entrywise power of a PSD real matrix is PSD; exponent
zero gives the all-ones matrix. Horn--Johnson (2013), Theorem 7.5.3.
atlas: schur-product-inequalities (partial)
@isnad1 id=possemid.1h3v.s5.cca1c0d3a1c2 from=translated src=- shape=ea264b51 vocab=ed58b1c7
-/
theorem posSemidef_map_pow {A : Matrix n n ℝ} (hA : A.PosSemidef) (k : ℕ) :
    (A.map (fun t => t ^ k)).PosSemidef := by
  induction k with
  | zero =>
    have h := Matrix.posSemidef_vecMulVec_self_star (fun _ : n => (1 : ℝ))
    simpa only [Matrix.map, pow_zero, star_trivial, Matrix.vecMulVec, one_mul] using h
  | succ k ih =>
    have he : A.map (fun t => t ^ (k + 1)) = A.map (fun t => t ^ k) ⊙ A := by
      ext i j
      simp only [Matrix.map_apply, Matrix.hadamard_apply, pow_succ]
    rw [he]
    exact ih.hadamard hA

omit [Fintype n] in
/-- Entrywise scalar convergence is convergence of the corresponding matrix
power series. Horn--Johnson (2013), Section 7.5;
helper for positive-coefficient analytic maps.
@isnad1 id=hassum.1h4v.s7.077ef8bfec15 from=translated src=- shape=108b203a vocab=6fb3e308
-/
theorem hasSum_smul_map_pow_of_hasSum_entries (A : Matrix n n ℝ) (c : ℕ → ℝ) (f : ℝ → ℝ)
    (h : ∀ i j, HasSum (fun k => c k * (A i j) ^ k) (f (A i j))) :
    HasSum (fun k => c k • A.map (fun t => t ^ k)) (A.map f) := by
  change HasSum (fun k => fun i j => c k * (A i j) ^ k) (fun i j => f (A i j))
  rw [Pi.hasSum]
  intro i
  rw [Pi.hasSum]
  intro j
  simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using h i j

/-- Any entrywise convergent power series with nonnegative coefficients
maps PSD real matrices to PSD matrices. The hypotheses state the
scalar series at each entry. Horn--Johnson (2013), Theorem 7.5.3.
atlas: schur-product-inequalities (partial)
@isnad1 id=possemid.3h4v.s6.ab9f22ff87a7 from=translated src=- shape=6bb63303 vocab=93b2cee6
-/
theorem posSemidef_map_of_nonneg_powerSeries {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (f : ℝ → ℝ)
    (h : ∀ i j, HasSum (fun k => c k * (A i j) ^ k) (f (A i j))) :
    (A.map f).PosSemidef :=
  posSemidef_of_hasSum (fun k => (posSemidef_map_pow hA k).smul (hc k))
    (hasSum_smul_map_pow_of_hasSum_entries A c f h)

/-- A scalar formal power series with nonnegative coefficients preserves
PSD membership whenever each matrix entry lies strictly inside its
radius of convergence. This is the source radius condition without a
nonempty maximum convention. Horn--Johnson (2013), Theorem 7.5.3.
atlas: schur-product-inequalities (partial)
@isnad1 id=possemid.3h3v.s7.d1f94b505bcf from=translated src=- shape=792b9160 vocab=b96b86d3
-/
theorem posSemidef_map_ofScalarsSum_of_lt_radius {A : Matrix n n ℝ} (hA : A.PosSemidef)
    (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hr : ∀ i j, (‖A i j‖₊ : ENNReal) < (FormalMultilinearSeries.ofScalars ℝ c).radius) :
    (A.map (FormalMultilinearSeries.ofScalarsSum c)).PosSemidef := by
  apply posSemidef_map_of_nonneg_powerSeries hA c hc
  intro i j
  have hs := (FormalMultilinearSeries.ofScalars ℝ c).hasSum
    (show A i j ∈ Metric.eball 0 (FormalMultilinearSeries.ofScalars ℝ c).radius by
      simpa only [mem_eball_zero_iff, enorm_eq_nnnorm] using hr i j)
  simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    FormalMultilinearSeries.ofScalarsSum] using hs

omit [Fintype n] in
/-- The exponential power series converges entrywise as a matrix series.
Horn--Johnson (2013), Section 7.5; helper for exponential positivity.
@isnad1 id=hassum.0h2v.s6.315f94920e92 from=translated src=- shape=3f6b318f vocab=7db99597
-/
theorem hasSum_inv_factorial_smul_map_pow (A : Matrix n n ℝ) :
    HasSum (fun k => (k.factorial : ℝ)⁻¹ • A.map (fun t => t ^ k)) (A.map Real.exp) := by
  apply hasSum_smul_map_pow_of_hasSum_entries
  intro i j
  simpa only [Real.exp_eq_exp_ℝ, div_eq_mul_inv, mul_comm] using
    NormedSpace.expSeries_div_hasSum_exp (A i j)

/-- Entrywise exponential preserves PSD membership.
Horn--Johnson (2013), Theorem 7.5.9.
atlas: schur-product-inequalities (partial)
@isnad1 id=possemid.1h2v.s4.92e47c9347e5 from=translated src=- shape=eb68a7c2 vocab=50e71e2f
-/
theorem posSemidef_map_exp {A : Matrix n n ℝ} (hA : A.PosSemidef) :
    (A.map Real.exp).PosSemidef := by
  exact posSemidef_of_hasSum (fun k => (posSemidef_map_pow hA k).smul (by positivity))
    (hasSum_inv_factorial_smul_map_pow A)

/-- Every finite nonnegative exponential feature sum lies below the full
entrywise exponential in Loewner order. Horn--Johnson (2013), Theorem 7.5.9;
helper for the exact strict-positivity characterization.
@isnad1 id=le.1h3v.s6.5e67a866b958 from=translated src=- shape=f3517d02 vocab=9378a8f9
-/
theorem sum_inv_factorial_smul_map_pow_le_map_exp {A : Matrix n n ℝ}
    (hA : A.PosSemidef) (N : ℕ) :
    (∑ k ∈ Finset.range N, (k.factorial : ℝ)⁻¹ • A.map (fun t => t ^ k)) ≤ A.map Real.exp :=
  sum_range_le_of_hasSum_posSemidef (fun k => (posSemidef_map_pow hA k).smul (by positivity))
    (hasSum_inv_factorial_smul_map_pow A) N

end NLAlib
