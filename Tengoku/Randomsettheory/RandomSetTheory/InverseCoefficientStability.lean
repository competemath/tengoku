/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Seed.Analysis.Matrix.Order
import Tengoku.Randomsettheory.RandomSetTheory.HausdorffTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stability of the inverse coefficient map

This file formalizes the deterministic map used to pass from moment sets to
least-squares coefficient sets:

`Phi (Sigma, gamma) = Sigma⁻¹ gamma`.

The covariance block is controlled by the intrinsic Loewner lower bound
`a • 1 ≤ Sigma`, rather than by an informal minimum-eigenvalue predicate.  On
the domain where this bound holds and `‖gamma‖ ≤ G`, `Phi` is Lipschitz for
the product Euclidean norm with the constant

`sqrt 2 * max (1 / a) (G / a²)`.

This is the exact deterministic constant used in the Hausdorff-risk argument
for the identified coefficient set.  The final results give compactness,
Hausdorff transport, closed-convex-hull transport, and convergence transport
for images of compact moment sets.
-/

open Matrix Set Metric Filter Topology
open scoped MatrixOrder Matrix.Norms.L2Operator Pointwise BigOperators

noncomputable section

namespace RandomSetTheory

/-! ## Spectral control of inversion -/

/-- A strictly positive Loewner lower bound makes a real matrix positive
definite.-/
theorem matrix_posDef_of_loewnerLowerBound
    {n : Type*} [DecidableEq n]
    (A : Matrix n n ℝ) {a : ℝ} (ha : 0 < a)
    (hA : a • (1 : Matrix n n ℝ) ≤ A) :
    A.PosDef := by
  have hbase : (a • (1 : Matrix n n ℝ)).PosDef :=
    Matrix.PosDef.one.smul ha
  have hdiff : (A - a • (1 : Matrix n n ℝ)).PosSemidef := hA
  rw [show A = a • (1 : Matrix n n ℝ) + (A - a • 1) by abel]
  exact hbase.add_posSemidef hdiff

/-- In particular, a matrix with a strictly positive Loewner lower bound is
invertible.-/
theorem matrix_isUnit_of_loewnerLowerBound
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) {a : ℝ} (ha : 0 < a)
    (hA : a • (1 : Matrix n n ℝ) ≤ A) :
    IsUnit A :=
  (matrix_posDef_of_loewnerLowerBound A ha hA).isUnit

/-- Determinantal form of the preceding invertibility conclusion.-/
theorem matrix_det_pos_of_loewnerLowerBound
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) {a : ℝ} (ha : 0 < a)
    (hA : a • (1 : Matrix n n ℝ) ≤ A) :
    0 < A.det :=
  (matrix_posDef_of_loewnerLowerBound A ha hA).det_pos

/-- A positive Loewner lower bound controls the `L²` operator norm of the
matrix inverse.-/
theorem matrix_norm_inv_le_of_loewnerLowerBound
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) {a : ℝ} (ha : 0 < a)
    (hA : a • (1 : Matrix n n ℝ) ≤ A) :
    ‖A⁻¹‖ ≤ 1 / a := by
  have hpos : A.PosDef := matrix_posDef_of_loewnerLowerBound A ha hA
  have hspectrum : ∀ x ∈ spectrum ℝ A, a ≤ x := by
    rw [← Algebra.algebraMap_eq_smul_one] at hA
    exact (algebraMap_le_iff_le_spectrum
      hpos.isHermitian.isSelfAdjoint).mp hA
  have hcfc : ‖cfc (fun x : ℝ => x⁻¹) A‖ ≤ 1 / a := by
    apply norm_cfc_le (one_div_nonneg.mpr ha.le)
    intro x hx
    have hxpos : 0 < x := ha.trans_le (hspectrum x hx)
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
    simpa only [one_div] using
      one_div_le_one_div_of_le ha (hspectrum x hx)
  rw [cfc_ringInverse_id (R := ℝ) (a := A) hpos.isUnit
    hpos.isHermitian.isSelfAdjoint] at hcfc
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using hcfc

/-- Resolvent estimate for two matrices satisfying the same positive Loewner
lower bound.-/
theorem matrix_norm_inv_sub_inv_le_of_loewnerLowerBound
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A B : Matrix n n ℝ) {a : ℝ} (ha : 0 < a)
    (hA : a • (1 : Matrix n n ℝ) ≤ A)
    (hB : a • (1 : Matrix n n ℝ) ≤ B) :
    ‖A⁻¹ - B⁻¹‖ ≤ (1 / a) ^ 2 * ‖A - B‖ := by
  have hAp : A.PosDef := matrix_posDef_of_loewnerLowerBound A ha hA
  have hBp : B.PosDef := matrix_posDef_of_loewnerLowerBound B ha hB
  rw [Matrix.inv_sub_inv (iff_of_true hAp.isUnit hBp.isUnit)]
  calc
    ‖A⁻¹ * (B - A) * B⁻¹‖ ≤ ‖A⁻¹ * (B - A)‖ * ‖B⁻¹‖ :=
      Matrix.l2_opNorm_mul _ _
    _ ≤ (‖A⁻¹‖ * ‖B - A‖) * ‖B⁻¹‖ := by
      gcongr
      exact Matrix.l2_opNorm_mul _ _
    _ ≤ ((1 / a) * ‖B - A‖) * (1 / a) := by
      gcongr
      · exact matrix_norm_inv_le_of_loewnerLowerBound A ha hA
      · exact matrix_norm_inv_le_of_loewnerLowerBound B ha hB
    _ = (1 / a) ^ 2 * ‖A - B‖ := by
      rw [norm_sub_rev]
      ring

/-! ## The inverse coefficient map -/

/-- Matrix/vector moment pairs equipped with the product `L²` norm.  The
matrix component carries the `L²` operator norm.-/
abbrev InverseCoefficientMomentSpace (n : Type*) :=
  WithLp 2 (Matrix n n ℝ × EuclideanSpace ℝ n)

/-- The coefficient map `Phi (Sigma, gamma) = Sigma⁻¹ gamma`.  Matrix
inversion is totalized in Lean, but every theorem below restricts this map to
a domain on which `Sigma` is positive definite.-/
def inverseCoefficientMap
    {n : Type*} [Fintype n] [DecidableEq n]
    (x : InverseCoefficientMomentSpace n) : EuclideanSpace ℝ n :=
  WithLp.toLp 2 (x.fst⁻¹ *ᵥ x.snd)

/-- Uniformly invertible moment pairs with a bounded cross-moment vector.-/
def inverseCoefficientDomain
    {n : Type*} [Fintype n] [DecidableEq n]
    (a G : ℝ) : Set (InverseCoefficientMomentSpace n) :=
  {x | a • (1 : Matrix n n ℝ) ≤ x.fst ∧ ‖x.snd‖ ≤ G}

/-- Every matrix component in a positive uniform-invertibility domain is a
unit; this records that the totalized inverse agrees with genuine inversion
on the whole domain.-/
theorem inverseCoefficientDomain_matrix_isUnit
    {n : Type*} [Fintype n] [DecidableEq n]
    {x : InverseCoefficientMomentSpace n} {a G : ℝ}
    (ha : 0 < a) (hx : x ∈ inverseCoefficientDomain (n := n) a G) :
    IsUnit x.fst :=
  matrix_isUnit_of_loewnerLowerBound x.fst ha hx.1

/-- The real-valued Lipschitz constant appearing in the report.-/
def inverseCoefficientLipschitzConstant (a G : ℝ) : ℝ :=
  Real.sqrt 2 * max (1 / a) (G / a ^ 2)

/-- Nonnegative packaging of `inverseCoefficientLipschitzConstant`.-/
def inverseCoefficientLipschitzNN
    (a G : ℝ) (ha : 0 < a) : NNReal :=
  ⟨inverseCoefficientLipschitzConstant a G, by
    unfold inverseCoefficientLipschitzConstant
    exact mul_nonneg (Real.sqrt_nonneg 2)
      ((one_div_nonneg.mpr ha.le).trans (le_max_left _ _))⟩

/-- Analytic two-term estimate before combining the two product coordinates.-/
theorem inverseCoefficientMap_norm_sub_le_add
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A B : Matrix n n ℝ) (b c : n → ℝ) {a G : ℝ}
    (ha : 0 < a)
    (hA : a • (1 : Matrix n n ℝ) ≤ A)
    (hB : a • (1 : Matrix n n ℝ) ≤ B)
    (hc : ‖WithLp.toLp 2 c‖ ≤ G) :
    ‖WithLp.toLp 2 (A⁻¹ *ᵥ b - B⁻¹ *ᵥ c)‖ ≤
      (1 / a) * ‖WithLp.toLp 2 (b - c)‖ +
        (G / a ^ 2) * ‖A - B‖ := by
  have hsplit : A⁻¹ *ᵥ b - B⁻¹ *ᵥ c =
      A⁻¹ *ᵥ (b - c) + (A⁻¹ - B⁻¹) *ᵥ c := by
    rw [Matrix.mulVec_sub, Matrix.sub_mulVec]
    abel
  rw [hsplit, WithLp.toLp_add]
  calc
    _ ≤ ‖WithLp.toLp 2 (A⁻¹ *ᵥ (b - c))‖ +
        ‖WithLp.toLp 2 ((A⁻¹ - B⁻¹) *ᵥ c)‖ := norm_add_le _ _
    _ ≤ (‖A⁻¹‖ * ‖WithLp.toLp 2 (b - c)‖) +
        (‖A⁻¹ - B⁻¹‖ * ‖WithLp.toLp 2 c‖) := by
      gcongr
      · simpa using Matrix.l2_opNorm_mulVec A⁻¹ (WithLp.toLp 2 (b - c))
      · simpa using
          Matrix.l2_opNorm_mulVec (A⁻¹ - B⁻¹) (WithLp.toLp 2 c)
    _ ≤ ((1 / a) * ‖WithLp.toLp 2 (b - c)‖) +
        (((1 / a) ^ 2 * ‖A - B‖) * G) := by
      gcongr
      · exact matrix_norm_inv_le_of_loewnerLowerBound A ha hA
      · exact matrix_norm_inv_sub_inv_le_of_loewnerLowerBound A B ha hA hB
    _ = (1 / a) * ‖WithLp.toLp 2 (b - c)‖ +
        (G / a ^ 2) * ‖A - B‖ := by
      field_simp [ha.ne']

private theorem weighted_two_le_sqrt_two_max
    {u v x y : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    u * y + v * x ≤
      Real.sqrt 2 * max u v * Real.sqrt (x ^ 2 + y ^ 2) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin 2)) ![u, v] ![y, x]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hcs
  have huv : Real.sqrt (u ^ 2 + v ^ 2) ≤ Real.sqrt 2 * max u v := by
    simpa [Complex.norm_def, abs_of_nonneg hu, abs_of_nonneg hv, pow_two] using
      Complex.norm_le_sqrt_two_mul_max (⟨u, v⟩ : ℂ)
  calc
    u * y + v * x ≤
        Real.sqrt (u ^ 2 + v ^ 2) * Real.sqrt (y ^ 2 + x ^ 2) := hcs
    _ ≤ (Real.sqrt 2 * max u v) * Real.sqrt (y ^ 2 + x ^ 2) := by
      gcongr
    _ = Real.sqrt 2 * max u v * Real.sqrt (x ^ 2 + y ^ 2) := by
      ring_nf

/-- Exact pointwise Lipschitz estimate for `Phi`.  The hypothesis only bounds
the second vector, which is sufficient because the resolvent decomposition is
oriented with that vector.-/
theorem inverseCoefficientMap_dist_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {x y : InverseCoefficientMomentSpace n} {a G : ℝ}
    (ha : 0 < a) (hG : 0 ≤ G)
    (hx : x ∈ inverseCoefficientDomain (n := n) a G)
    (hy : y ∈ inverseCoefficientDomain (n := n) a G) :
    dist (inverseCoefficientMap x) (inverseCoefficientMap y) ≤
      inverseCoefficientLipschitzConstant a G * dist x y := by
  have hmain := inverseCoefficientMap_norm_sub_le_add
    x.fst y.fst x.snd.ofLp y.snd.ofLp ha hx.1 hy.1 hy.2
  have hbound := hmain.trans
    (weighted_two_le_sqrt_two_max
      (one_div_nonneg.mpr ha.le) (div_nonneg hG (sq_nonneg a)))
  rw [dist_eq_norm, dist_eq_norm]
  change ‖WithLp.toLp 2 (x.fst⁻¹ *ᵥ x.snd) -
    WithLp.toLp 2 (y.fst⁻¹ *ᵥ y.snd)‖ ≤ _
  rw [← WithLp.toLp_sub]
  rw [WithLp.prod_norm_eq_of_L2]
  change _ ≤ inverseCoefficientLipschitzConstant a G * Real.sqrt
    (‖x.fst - y.fst‖ ^ 2 + ‖x.snd - y.snd‖ ^ 2)
  simpa only [inverseCoefficientLipschitzConstant, WithLp.ofLp_sub,
    WithLp.ofLp_toLp, WithLp.toLp_sub] using hbound

/-- `Phi` is Lipschitz on the uniform-invertibility domain, with exactly the
constant stated in the report.-/
theorem inverseCoefficientMap_lipschitzOnWith
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {a G : ℝ} (ha : 0 < a) (hG : 0 ≤ G) :
    LipschitzOnWith (inverseCoefficientLipschitzNN a G ha)
      inverseCoefficientMap (inverseCoefficientDomain (n := n) a G) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist (inverseCoefficientMap x) (inverseCoefficientMap y) ≤
    inverseCoefficientLipschitzConstant a G * dist x y
  exact inverseCoefficientMap_dist_le ha hG hx hy

/-- `Phi` is continuous on the uniform-invertibility domain.-/
theorem inverseCoefficientMap_continuousOn
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {a G : ℝ} (ha : 0 < a) (hG : 0 ≤ G) :
    ContinuousOn inverseCoefficientMap
      (inverseCoefficientDomain (n := n) a G) :=
  (inverseCoefficientMap_lipschitzOnWith ha hG).continuousOn

/-- Uniform invertibility and the cross-moment envelope also bound every
coefficient vector by `G / a`.-/
theorem inverseCoefficientMap_norm_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {x : InverseCoefficientMomentSpace n} {a G : ℝ}
    (ha : 0 < a)
    (hx : x ∈ inverseCoefficientDomain (n := n) a G) :
    ‖inverseCoefficientMap x‖ ≤ G / a := by
  change ‖WithLp.toLp 2 (x.fst⁻¹ *ᵥ x.snd)‖ ≤ G / a
  calc
    _ ≤ ‖x.fst⁻¹‖ * ‖x.snd‖ := by
      simpa using Matrix.l2_opNorm_mulVec x.fst⁻¹ x.snd
    _ ≤ (1 / a) * G := by
      exact mul_le_mul
        (matrix_norm_inv_le_of_loewnerLowerBound x.fst ha hx.1)
        hx.2 (norm_nonneg _) (one_div_nonneg.mpr ha.le)
    _ = G / a := by ring

/-! ## Compact and Hausdorff images -/

/-- The coefficient set obtained by applying `Phi` to a moment set.-/
def inverseCoefficientImage
    {n : Type*} [Fintype n] [DecidableEq n]
    (K : Set (InverseCoefficientMomentSpace n)) : Set (EuclideanSpace ℝ n) :=
  inverseCoefficientMap '' K

/-- A moment-set coefficient image satisfying the deterministic bounds lies
in the closed ball of radius `G / a`.-/
theorem inverseCoefficientImage_subset_closedBall
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {a G : ℝ} (ha : 0 < a)
    {K : Set (InverseCoefficientMomentSpace n)}
    (hKD : K ⊆ inverseCoefficientDomain (n := n) a G) :
    inverseCoefficientImage K ⊆ closedBall 0 (G / a) := by
  rintro _ ⟨x, hxK, rfl⟩
  simpa [mem_closedBall, dist_zero_right] using
    inverseCoefficientMap_norm_le ha (hKD hxK)

/-- Nonemptiness is preserved by the coefficient map.-/
theorem inverseCoefficientImage_nonempty
    {n : Type*} [Fintype n] [DecidableEq n]
    {K : Set (InverseCoefficientMomentSpace n)} (hK : K.Nonempty) :
    (inverseCoefficientImage K).Nonempty :=
  hK.image inverseCoefficientMap

/-- The identified coefficient set is compact whenever its moment set is
compact and satisfies the uniform inverse and vector bounds.-/
theorem inverseCoefficientImage_isCompact
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {a G : ℝ} (ha : 0 < a) (hG : 0 ≤ G)
    {K : Set (InverseCoefficientMomentSpace n)}
    (hK : IsCompact K)
    (hKD : K ⊆ inverseCoefficientDomain (n := n) a G) :
    IsCompact (inverseCoefficientImage K) := by
  exact hK.image_of_continuousOn
    ((inverseCoefficientMap_continuousOn ha hG).mono hKD)

/-- Closed convexification preserves compactness of an identified coefficient
set in finite dimension.-/
theorem inverseCoefficientImage_closedConvexHull_isCompact
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {a G : ℝ} (ha : 0 < a) (hG : 0 ≤ G)
    {K : Set (InverseCoefficientMomentSpace n)}
    (hK : IsCompact K)
    (hKD : K ⊆ inverseCoefficientDomain (n := n) a G) :
    IsCompact (closedConvexHull ℝ (inverseCoefficientImage K)) :=
  closedConvexHull_compact
    (inverseCoefficientImage_isCompact ha hG hK hKD)

/-- Hausdorff error on compact moment sets transports to coefficient sets
with the exact inverse-map Lipschitz factor.-/
theorem hausdorffDist_inverseCoefficientImage_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {a G : ℝ} (ha : 0 < a) (hG : 0 ≤ G)
    {K L : Set (InverseCoefficientMomentSpace n)}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKD : K ⊆ inverseCoefficientDomain (n := n) a G)
    (hLD : L ⊆ inverseCoefficientDomain (n := n) a G) :
    hausdorffDist (inverseCoefficientImage K) (inverseCoefficientImage L) ≤
      inverseCoefficientLipschitzConstant a G * hausdorffDist K L := by
  exact hausdorffDist_image_le_of_lipschitzOnWith
    ((inverseCoefficientMap_lipschitzOnWith ha hG).mono
      (union_subset hKD hLD)) hK hL hKne hLne

/-- The same Hausdorff bound holds for the closed convex hulls of the two
coefficient images.-/
theorem hausdorffDist_closedConvexHull_inverseCoefficientImage_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {a G : ℝ} (ha : 0 < a) (hG : 0 ≤ G)
    {K L : Set (InverseCoefficientMomentSpace n)}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKD : K ⊆ inverseCoefficientDomain (n := n) a G)
    (hLD : L ⊆ inverseCoefficientDomain (n := n) a G) :
    hausdorffDist
        (closedConvexHull ℝ (inverseCoefficientImage K))
        (closedConvexHull ℝ (inverseCoefficientImage L)) ≤
      inverseCoefficientLipschitzConstant a G * hausdorffDist K L := by
  exact hausdorffDist_closedConvexHull_image_le_of_lipschitzOnWith
    ((inverseCoefficientMap_lipschitzOnWith ha hG).mono
      (union_subset hKD hLD)) hK hL hKne hLne

/-- Uniformly invertible compact moment sets converging in Hausdorff distance
have coefficient images converging in Hausdorff distance.-/
theorem tendsto_hausdorffDist_inverseCoefficientImage
    {n ι : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {l : Filter ι} {a G : ℝ} (ha : 0 < a) (hG : 0 ≤ G)
    {K : ι → Set (InverseCoefficientMomentSpace n)}
    {L : Set (InverseCoefficientMomentSpace n)}
    (hK : ∀ i, IsCompact (K i)) (hL : IsCompact L)
    (hKne : ∀ i, (K i).Nonempty) (hLne : L.Nonempty)
    (hKD : ∀ i, K i ⊆ inverseCoefficientDomain (n := n) a G)
    (hLD : L ⊆ inverseCoefficientDomain (n := n) a G)
    (hKL : Tendsto (fun i => hausdorffDist (K i) L) l (nhds 0)) :
    Tendsto
      (fun i => hausdorffDist (inverseCoefficientImage (K i))
        (inverseCoefficientImage L)) l (nhds 0) := by
  apply tendsto_hausdorffDist_image_of_lipschitzOnWith
    (c := inverseCoefficientLipschitzNN a G ha)
  · intro i
    exact (inverseCoefficientMap_lipschitzOnWith ha hG).mono
      (union_subset (hKD i) hLD)
  · exact hK
  · exact hL
  · exact hKne
  · exact hLne
  · exact hKL

/-- The preceding convergence remains valid after closed convexification of
both coefficient images.-/
theorem tendsto_hausdorffDist_closedConvexHull_inverseCoefficientImage
    {n ι : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {l : Filter ι} {a G : ℝ} (ha : 0 < a) (hG : 0 ≤ G)
    {K : ι → Set (InverseCoefficientMomentSpace n)}
    {L : Set (InverseCoefficientMomentSpace n)}
    (hK : ∀ i, IsCompact (K i)) (hL : IsCompact L)
    (hKne : ∀ i, (K i).Nonempty) (hLne : L.Nonempty)
    (hKD : ∀ i, K i ⊆ inverseCoefficientDomain (n := n) a G)
    (hLD : L ⊆ inverseCoefficientDomain (n := n) a G)
    (hKL : Tendsto (fun i => hausdorffDist (K i) L) l (nhds 0)) :
    Tendsto
      (fun i => hausdorffDist
        (closedConvexHull ℝ (inverseCoefficientImage (K i)))
        (closedConvexHull ℝ (inverseCoefficientImage L))) l (nhds 0) := by
  apply tendsto_hausdorffDist_closedConvexHull_image_of_lipschitzOnWith
    (c := inverseCoefficientLipschitzNN a G ha)
  · intro i
    exact (inverseCoefficientMap_lipschitzOnWith ha hG).mono
      (union_subset (hKD i) hLD)
  · exact hK
  · exact hL
  · exact hKne
  · exact hLne
  · exact hKL

end RandomSetTheory
