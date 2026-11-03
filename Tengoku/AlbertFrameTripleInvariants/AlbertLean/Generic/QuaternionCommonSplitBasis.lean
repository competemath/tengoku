import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionNonscalarBlockNormalizer
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWeightedCommonPlaneAut

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms exists_ordered_sl2_split` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms all_blocks_diagonal` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms splitForward_symplectic` (it only prints; the queue checks the axioms of every declaration). -/

/-! A common SL2 eigenbasis from a three-vector cyclic witness. No entry chart
and no root other than the supplied nonzero discriminant root is used. -/
noncomputable section
namespace AlbertLean.Generic.QuaternionRow.CommonSplitBasis

open BlockEigenbasis NonscalarBlockNormalizer CyclicBlockNormalizer
open WeightedBlockEquations WeightedProjectorGauge
open GroupedBridge SelfAdjointCarrier SymplecticMatrixBridge WordMatrixConnection

variable {K : Type*} [Field K] [CharZero K]

/-- Coefficients of the ordered eigenvectors in the basis `[v,Xv]`.
The first column is rescaled by the inverse of their determinant.-/
def eigenCoefficients (X : Mat2 K) (sigma d : K) : Mat2 K :=
  matrix (-lambdaMinus X sigma / (sigma * d)) (-lambdaPlus X sigma)
    ((sigma * d)⁻¹) 1

/--
@isnad1 id=eq.1h4v.s8.dd5222d68dd9 from=translated src=- shape=be634f4c vocab=99e37430
-/
theorem eigenCoefficients_intertwines (X : Mat2 K) (sigma d : K)
    (hroot : sigma ^ 2 = trace2 X ^ 2 - 4 * determinant X) :
    companion X * eigenCoefficients X sigma d =
      eigenCoefficients X sigma d * eigenvalues X sigma := by
  obtain ⟨hp, hm⟩ := characteristic_roots X sigma hroot
  have hsum : lambdaPlus X sigma + lambdaMinus X sigma = trace2 X := by
    dsimp [lambdaPlus, lambdaMinus]
    ring
  have hprod : lambdaPlus X sigma * lambdaMinus X sigma = determinant X := by
    linear_combination -hp + lambdaPlus X sigma * hsum
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [companion, eigenCoefficients, eigenvalues, matrix, Matrix.mul_apply,
      Fin.sum_univ_two, div_eq_mul_inv] <;>
    simp only [← hprod, ← hsum] <;> ring

/--
@isnad1 id=eq.2h4v.s6.fb805ba97a16 from=translated src=- shape=10731b75 vocab=2d090f4e
-/
theorem eigenCoefficients_det (X : Mat2 K) (sigma d : K)
    (hs : sigma ≠ 0) (hd : d ≠ 0) :
    determinant (eigenCoefficients X sigma d) = d⁻¹ := by
  simp [determinant, eigenCoefficients, matrix, lambdaPlus, lambdaMinus]
  field_simp [hs, hd]
  <;> ring

def cyclicSplitBasis (X : Mat2 K) (sigma : K) (v : Vec2 K) : Mat2 K :=
  cyclicBasisAt X v * eigenCoefficients X sigma (cyclicDet X v)

/--
@isnad1 id=eq.2h4v.s6.92b55b817bd0 from=translated src=- shape=bee22093 vocab=315c77c1
-/
theorem cyclicSplitBasis_det (X : Mat2 K) (sigma : K) (v : Vec2 K)
    (hs : sigma ≠ 0) (hv : cyclicDet X v ≠ 0) :
    determinant (cyclicSplitBasis X sigma v) = 1 := by
  have hdet : determinant (cyclicBasisAt X v) = cyclicDet X v := rfl
  rw [cyclicSplitBasis, determinant_eq_det, Matrix.det_mul,
    ← determinant_eq_det, ← determinant_eq_det, hdet,
    eigenCoefficients_det X sigma (cyclicDet X v) hs hv, mul_inv_cancel₀ hv]

/--
@isnad1 id=eq.1h4v.s8.4cbbd00d467d from=translated src=- shape=444f5609 vocab=fcc4eff5
-/
theorem cyclicSplitBasis_intertwines (X : Mat2 K) (sigma : K) (v : Vec2 K)
    (hroot : sigma ^ 2 = trace2 X ^ 2 - 4 * determinant X) :
    X * cyclicSplitBasis X sigma v =
      cyclicSplitBasis X sigma v * eigenvalues X sigma := by
  rw [cyclicSplitBasis, ← Matrix.mul_assoc, cyclicBasisAt_intertwines,
    Matrix.mul_assoc, eigenCoefficients_intertwines X sigma _ hroot]
  simp only [Matrix.mul_assoc]

def inverseSL (H : Mat2 K) : Mat2 K :=
  matrix (H 1 1) (-H 0 1) (-H 1 0) (H 0 0)

/--
@isnad1 id=eq.1h2v.s7.26c86cac0ce9 from=translated src=- shape=c87c4d39 vocab=aa6d7a1b
-/
theorem inverseSL_mul (H : Mat2 K) (hH : determinant H = 1) :
    inverseSL H * H = 1 := by
  dsimp [determinant] at hH
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseSL, matrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply]
  all_goals ring_nf at hH ⊢ <;> exact hH

/--
@isnad1 id=eq.1h2v.s7.c7e23d9f5bbe from=translated src=- shape=133e8c9f vocab=aa6d7a1b
-/
theorem mul_inverseSL (H : Mat2 K) (hH : determinant H = 1) :
    H * inverseSL H = 1 := by
  dsimp [determinant] at hH
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [inverseSL, matrix, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply]
  all_goals ring_nf at hH ⊢ <;> exact hH

/-- The ordered split basis is constructed; it is not an eigenbasis premise.
@isnad1 id=ex.2h3v.s9.06247cc166de from=translated src=- shape=d6c2f9fa vocab=24c94a7c
-/
theorem exists_ordered_sl2_split (X : Mat2 K) (sigma : K)
    (hs : sigma ≠ 0)
    (hroot : sigma ^ 2 = trace2 X ^ 2 - 4 * determinant X) :
    ∃ H S : Mat2 K,
      determinant H = 1 ∧ H * S = 1 ∧ S * H = 1 ∧
      S * X * H = eigenvalues X sigma := by
  have hd : trace2 X ^ 2 - 4 * determinant X ≠ 0 := by
    rw [← hroot]
    exact pow_ne_zero 2 hs
  obtain ⟨v, _, hv⟩ := exists_three_cyclic X (nonscalar_of_discriminant_ne_zero X hd)
  let H := cyclicSplitBasis X sigma v
  have hH : determinant H = 1 := cyclicSplitBasis_det X sigma v hs hv
  have hi : inverseSL H * H = 1 := inverseSL_mul H hH
  refine ⟨H, inverseSL H, hH, mul_inverseSL H hH, hi, ?_⟩
  rw [Matrix.mul_assoc, cyclicSplitBasis_intertwines X sigma v hroot,
    ← Matrix.mul_assoc, hi, Matrix.one_mul]

/-- Any linear measurement vanishing on `I` and the pivot vanishes on every
labelled block. This is the entire simultaneous-diagonalization propagation.
@isnad1 id=eq.7h7v.s10.4e06d55478d4 from=translated src=- shape=e3a8b81e vocab=55141ef1
-/
theorem all_blocks_killed
    (B : Fin 3 → Fin 3 → Mat2 K) (p q : Fin 3 → K)
    (hp1 : p 1 ≠ 0) (hp2 : p 2 ≠ 0)
    (hd : ∀ i, B i i = q i • (1 : Mat2 K))
    (hr : ∀ i, B i 0 + B i 1 + B i 2 = 0)
    (hc : ∀ j, p 0 • B 0 j + p 1 • B 1 j + p 2 • B 2 j = 0)
    (ell : Mat2 K →ₗ[K] K) (hI : ell 1 = 0) (hX : ell (B 0 1) = 0) :
    ∀ i j, ell (B i j) = 0 := by
  obtain ⟨h02, h21, h20, h10, h12⟩ := scaled_block_equations B p q hd hr hc
  have d (i : Fin 3) : ell (B i i) = 0 := by simp [hd i, hI]
  have z02 : ell (B 0 2) = 0 := by simp [h02, hI, hX]
  have cancel (t : K) (ht : t ≠ 0) (Y : Mat2 K) (he : ell (t • Y) = 0) :
      ell Y = 0 := by
    simpa only [map_smul, smul_eq_mul, mul_eq_zero, ht, false_or] using he
  have z21 : ell (B 2 1) = 0 := cancel _ hp2 _ (by simp [h21, hI, hX])
  have z20 : ell (B 2 0) = 0 := cancel _ hp2 _ (by simp [h20, hI, hX])
  have z10 : ell (B 1 0) = 0 := cancel _ hp1 _ (by simp [h10, hI, hX])
  have z12 : ell (B 1 2) = 0 := cancel _ hp1 _ (by simp [h12, hI, hX])
  intro i j
  fin_cases i <;> fin_cases j
  · exact d 0
  · exact hX
  · exact z02
  · exact z10
  · exact d 1
  · exact z12
  · exact z20
  · exact z21
  · exact d 2

def conjugateEntry (S H : Mat2 K) (r s : Fin 2) : Mat2 K →ₗ[K] K where
  toFun X := (S * X * H) r s
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' t X := by simp [Matrix.mul_smul, Matrix.smul_mul]

/--
@isnad1 id=and.7h9v.s10.5687df351649 from=translated src=- shape=643c0a51 vocab=806fb996
-/
theorem all_blocks_diagonal
    (B : Fin 3 → Fin 3 → Mat2 K) (p q : Fin 3 → K)
    (hp1 : p 1 ≠ 0) (hp2 : p 2 ≠ 0)
    (hd : ∀ i, B i i = q i • (1 : Mat2 K))
    (hr : ∀ i, B i 0 + B i 1 + B i 2 = 0)
    (hc : ∀ j, p 0 • B 0 j + p 1 • B 1 j + p 2 • B 2 j = 0)
    (H S : Mat2 K) (hSH : S * H = 1) (sigma : K)
    (hX : S * B 0 1 * H = eigenvalues (B 0 1) sigma) :
    ∀ i j, (S * B i j * H) 0 1 = 0 ∧ (S * B i j * H) 1 0 = 0 := by
  have zero_entry (r s : Fin 2) (hrs : r ≠ s) :
      ∀ i j, (S * B i j * H) r s = 0 := by
    apply all_blocks_killed B p q hp1 hp2 hd hr hc (conjugateEntry S H r s)
    · simp [conjugateEntry, hSH, Matrix.one_apply, hrs]
    · fin_cases r <;> fin_cases s <;>
        simp [conjugateEntry, hX, eigenvalues, matrix] at hrs ⊢
  exact fun i j => ⟨zero_entry 0 1 (by decide) i j,
    zero_entry 1 0 (by decide) i j⟩

/-- Plane-wise rescaling of the second member only.-/
def planeScale (t : Fin 3 → K) : Vec6 K →ₗ[K] Vec6 K where
  toFun x
    | Sum.inl i => x (Sum.inl i)
    | Sum.inr i => t i * x (Sum.inr i)
  map_add' x y := by funext a; rcases a with i | i <;> simp [mul_add]
  map_smul' a x := by
    funext b
    rcases b with i | i <;> simp <;> ring

/--
@isnad1 id=eq.1h3v.s8.a4a4436dbb74 from=translated src=- shape=474efdc0 vocab=4f3918aa
-/
theorem planeScale_comp (t s : Fin 3 → K) (h : ∀ i, t i * s i = 1) :
    (planeScale t).comp (planeScale s) = LinearMap.id := by
  ext x a
  rcases a with i | i <;> simp [planeScale, ← mul_assoc, h]

/--
@isnad1 id=eq.1h4v.s10.87fd43f67b7c from=translated src=- shape=d154372b vocab=bfb4e235
-/
theorem planeScale_weighted_form (p : Fin 3 → K) (hp : ∀ i, p i ≠ 0)
    (x y : Vec6 K) :
    weightedOmega p (planeScale (fun i => (p i)⁻¹) x)
      (planeScale (fun i => (p i)⁻¹) y) = (omega (K := K)) x y := by
  change (∑ i, p i * (x (Sum.inl i) * ((p i)⁻¹ * y (Sum.inr i)) -
    ((p i)⁻¹ * x (Sum.inr i)) * y (Sum.inl i))) =
    ∑ i, (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i))
  apply Finset.sum_congr rfl
  intro i _
  field_simp [hp i]
  <;> ring

/-- Literal Q=L·commonPlane(H)·diag(1,p_i⁻¹), and its explicit inverse.-/
def splitForward (L : Vec6 K ≃ₗ[K] Vec6 K) (p : Fin 3 → K) (H : Mat2 K) :
    Vec6 K →ₗ[K] Vec6 K :=
  L.toLinearMap.comp ((commonPlaneMap H).comp (planeScale (fun i => (p i)⁻¹)))

def splitBackward (L : Vec6 K ≃ₗ[K] Vec6 K) (p : Fin 3 → K) (S : Mat2 K) :
    Vec6 K →ₗ[K] Vec6 K :=
  (planeScale p).comp ((commonPlaneMap S).comp L.symm.toLinearMap)

/--
@isnad1 id=and.3h5v.s10.7f3150af363e from=translated src=- shape=6d3d0b7e vocab=f188add5
-/
theorem split_inverse (L : Vec6 K ≃ₗ[K] Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i ≠ 0) (H S : Mat2 K) (hHS : H * S = 1) (hSH : S * H = 1) :
    (splitForward L p H).comp (splitBackward L p S) = LinearMap.id ∧
    (splitBackward L p S).comp (splitForward L p H) = LinearMap.id := by
  have hpp := planeScale_comp (fun i => (p i)⁻¹) p
    (fun i => inv_mul_cancel₀ (hp i))
  have hpp' := planeScale_comp p (fun i => (p i)⁻¹)
    (fun i => mul_inv_cancel₀ (hp i))
  have hh := commonPlaneMap_comp H S hHS
  have hh' := commonPlaneMap_comp S H hSH
  constructor
  · apply LinearMap.ext
    intro x
    have hz := LinearMap.congr_fun hpp (commonPlaneMap S (L.symm x))
    have hw := LinearMap.congr_fun hh (L.symm x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hz hw
    change L (commonPlaneMap H
      (planeScale (fun i => (p i)⁻¹) (planeScale p (commonPlaneMap S (L.symm x))))) = x
    rw [hz, hw, L.apply_symm_apply]
  · apply LinearMap.ext
    intro x
    have hz := LinearMap.congr_fun hpp' x
    have hw := LinearMap.congr_fun hh' (planeScale (fun i => (p i)⁻¹) x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hz hw
    change planeScale p (commonPlaneMap S
      (L.symm (L (commonPlaneMap H (planeScale (fun i => (p i)⁻¹) x))))) = x
    rw [L.symm_apply_apply, hw, hz]

/--
@isnad1 id=other.5h6v.s11.589ccaa12a00 from=translated src=- shape=8c7bb1fa vocab=e3b978bc
-/
theorem splitForward_symplectic
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K)) (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v)) (hpne : ∀ i, p i ≠ 0)
    (H : Mat2 K) (hH : determinant H = 1) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    let Q := matrixOfLinear (splitForward L p H)
    Q.transpose * symplecticJ * Q = symplecticJ := by
  dsimp only
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  have hform (x y : Vec6 K) :
      (omega (K := K)) (splitForward L p H x) (splitForward L p H y) =
        (omega (K := K)) x y := by
    change (omega (K := K)) (weightedCoordinateLinear E u v
      (commonPlaneMap H (planeScale (fun i => (p i)⁻¹) x)))
      (weightedCoordinateLinear E u v
      (commonPlaneMap H (planeScale (fun i => (p i)⁻¹) y))) = _
    rw [weightedCoordinate_form E hEidem hEsum u v p hp, commonPlaneMap_form]
    change determinant H * _ = _
    rw [hH, one_mul, planeScale_weighted_form p hpne]
  ext i j
  rw [symplectic_product_entry]
  rw [← matrixAction_basisVector _ i, ← matrixAction_basisVector _ j,
    matrixAction_matrixOfLinear, hform, omega_basisVector]

end AlbertLean.Generic.QuaternionRow.CommonSplitBasis
