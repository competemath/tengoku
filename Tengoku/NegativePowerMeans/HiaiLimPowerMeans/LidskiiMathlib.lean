import Tengoku.NegativePowerMeans.HiaiLimPowerMeans.MatrixTheorem
import Tengoku.Seed.Analysis.InnerProductSpace.SingularValues
import Tengoku.Seed.Data.Fin.Tuple.Sort

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reduction of multiplicative Lidskii

The conditional proof takes `Lidskii` as a named published ingredient.  This
file formalizes the determinant, product, ratio, and proper-prefix reductions
used by its standalone proof.  In particular, equality of the total
logarithmic sums is proved below from determinant multiplicativity.
-/

namespace HiaiLimPowerMeans

open Finset Matrix
open scoped BigOperators ComplexOrder MatrixOrder

/-- The positive square root multiplied by itself is the original matrix.-/
theorem Matrix.PosDef.half_mul_half
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosDef) :
    A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) = A := by
  have h := CFC.rpow_add (a := A) (x := (1 / 2 : ℝ))
    (y := (1 / 2 : ℝ)) hA.isUnit
  norm_num [CFC.rpow_one A hA.posSemidef.nonneg] at h ⊢
  exact h.symm

/-- Determinant identity for the positive relative matrix.-/
theorem det_relative_mul_det
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {B Y : Matrix (Fin n) (Fin n) 𝕜}
    (hY : Y.PosDef) :
    (relativeMatrix Y B).det * Y.det = B.det := by
  let S : Matrix (Fin n) (Fin n) 𝕜 := Y ^ (-(1 / 2 : ℝ))
  have hSYS : S * Y * S = 1 := by
    simpa [S] using Matrix.PosDef.invHalf_conjugate_self hY
  have hdetSYS := congrArg Matrix.det hSYS
  simp only [Matrix.det_mul, Matrix.det_one] at hdetSYS
  calc
    (relativeMatrix Y B).det * Y.det =
        (S.det * B.det * S.det) * Y.det := by
      simp [relativeMatrix, S, Matrix.det_mul]
    _ = (S.det * Y.det * S.det) * B.det := by ring
    _ = B.det := by rw [hdetSYS, one_mul]

/-- Coercing the product of the decreasing eigenvalues gives the determinant.-/
theorem coe_prod_decreasingEigenvalues_eq_det
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosDef) :
    RCLike.ofReal (∏ i, decreasingEigenvalues hA.isHermitian i) = A.det := by
  have hprod :=
    prod_comp_decreasingEigenvalues_eq_eigenvalues hA.isHermitian id
  change (∏ i, decreasingEigenvalues hA.isHermitian i) =
    ∏ i, hA.isHermitian.eigenvalues i at hprod
  rw [hprod]
  rw [show RCLike.ofReal (∏ i, hA.isHermitian.eigenvalues i) =
      ∏ i, RCLike.ofReal (hA.isHermitian.eigenvalues i) by
        exact map_prod (algebraMap ℝ 𝕜) _ Finset.univ]
  exact hA.isHermitian.det_eq_prod_eigenvalues.symm

/-- The product equality, i.e. the full-prefix equality in multiplicative
Lidskii, follows from determinant multiplicativity alone.-/
theorem prod_relative_mul_prod
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {B Y : Matrix (Fin n) (Fin n) 𝕜}
    (hB : B.PosDef) (hY : Y.PosDef) :
    (∏ i, decreasingEigenvalues
      (relativeMatrix_posDef hY hB).isHermitian i) *
        (∏ i, decreasingEigenvalues hY.isHermitian i) =
      ∏ i, decreasingEigenvalues hB.isHermitian i := by
  apply RCLike.ofReal_injective (K := 𝕜)
  rw [RCLike.ofReal_mul,
    coe_prod_decreasingEigenvalues_eq_det (relativeMatrix_posDef hY hB),
    coe_prod_decreasingEigenvalues_eq_det hY,
    coe_prod_decreasingEigenvalues_eq_det hB]
  exact det_relative_mul_det hY

/-- The equality of the total logarithmic sums in multiplicative Lidskii is
therefore already derivable from Mathlib.-/
theorem sum_log_ratio_eq_sum_log_relative
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {B Y : Matrix (Fin n) (Fin n) 𝕜}
    (hB : B.PosDef) (hY : Y.PosDef) :
    (∑ i, (Real.log (decreasingEigenvalues hB.isHermitian i) -
      Real.log (decreasingEigenvalues hY.isHermitian i))) =
      ∑ i, Real.log (decreasingEigenvalues
        (relativeMatrix_posDef hY hB).isHermitian i) := by
  let D : Matrix (Fin n) (Fin n) 𝕜 := relativeMatrix Y B
  have hD : D.PosDef := relativeMatrix_posDef hY hB
  have hb : ∀ i, 0 < decreasingEigenvalues hB.isHermitian i :=
    Matrix.PosDef.decreasingEigenvalues_pos hB
  have hy : ∀ i, 0 < decreasingEigenvalues hY.isHermitian i :=
    Matrix.PosDef.decreasingEigenvalues_pos hY
  have hd : ∀ i, 0 < decreasingEigenvalues hD.isHermitian i :=
    Matrix.PosDef.decreasingEigenvalues_pos hD
  have hprod := prod_relative_mul_prod hB hY
  change (∏ i, decreasingEigenvalues hD.isHermitian i) *
      (∏ i, decreasingEigenvalues hY.isHermitian i) =
    ∏ i, decreasingEigenvalues hB.isHermitian i at hprod
  have hyprod : (∏ i, decreasingEigenvalues hY.isHermitian i) ≠ 0 :=
    (Finset.prod_pos fun i _ ↦ hy i).ne'
  have hratio :
      (∏ i, decreasingEigenvalues hD.isHermitian i) =
        (∏ i, decreasingEigenvalues hB.isHermitian i) /
          ∏ i, decreasingEigenvalues hY.isHermitian i :=
    (eq_div_iff hyprod).2 hprod
  calc
    (∑ i, (Real.log (decreasingEigenvalues hB.isHermitian i) -
        Real.log (decreasingEigenvalues hY.isHermitian i))) =
        Real.log (∏ i, decreasingEigenvalues hB.isHermitian i) -
          Real.log (∏ i, decreasingEigenvalues hY.isHermitian i) := by
      rw [Finset.sum_sub_distrib,
        Real.log_prod (fun i _ ↦ (hb i).ne'),
        Real.log_prod (fun i _ ↦ (hy i).ne')]
    _ = Real.log ((∏ i, decreasingEigenvalues hB.isHermitian i) /
          ∏ i, decreasingEigenvalues hY.isHermitian i) := by
      rw [Real.log_div
        (Finset.prod_ne_zero_iff.mpr fun i _ ↦ (hb i).ne') hyprod]
    _ = Real.log (∏ i, decreasingEigenvalues hD.isHermitian i) := by
      rw [hratio]
    _ = ∑ i, Real.log (decreasingEigenvalues hD.isHermitian i) :=
      Real.log_prod (fun i _ ↦ (hd i).ne')

/-- The part of multiplicative Lidskii not supplied directly by Mathlib:
after decreasing rearrangement of the logarithmic ratio vector, every proper
prefix sum is bounded by the corresponding prefix of the relative spectrum.

The total-sum equality is intentionally absent: it is the theorem proved
above rather than an additional assumption.-/
def LidskiiProperPrefix (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (n : ℕ) [NeZero n]
    (B Y : Matrix (Fin n) (Fin n) 𝕜)
    (hB : B.PosDef) (hY : Y.PosDef),
      ∃ p : Equiv.Perm (Fin n),
        Antitone (fun i ↦
          Real.log (decreasingEigenvalues hB.isHermitian (p i)) -
            Real.log (decreasingEigenvalues hY.isHermitian (p i))) ∧
        ∀ k, k < n →
          prefixSum (fun i ↦
            Real.log (decreasingEigenvalues hB.isHermitian (p i)) -
              Real.log (decreasingEigenvalues hY.isHermitian (p i))) k ≤
            prefixSum (fun i ↦ Real.log (decreasingEigenvalues
              (relativeMatrix_posDef hY hB).isHermitian i)) k

/-- Every finite real vector has an antitone rearrangement.  Mathlib's
`Tuple.sort` sorts increasingly, so it is applied to the negative vector.-/
theorem exists_perm_antitone {n : ℕ} (x : Fin n → ℝ) :
    ∃ p : Equiv.Perm (Fin n), Antitone (fun i ↦ x (p i)) := by
  let p : Equiv.Perm (Fin n) := Tuple.sort (fun i ↦ -x i)
  refine ⟨p, ?_⟩
  have hp : Monotone ((fun i ↦ -x i) ∘ p) :=
    Tuple.monotone_sort (fun i ↦ -x i)
  intro i j hij
  have hpij := hp hij
  change -x (p i) ≤ -x (p j) at hpij
  linarith

/-- The selected-product matrix inequality before choosing the decreasing
rearrangement.  It asks for the product bound along every permutation; only
one such permutation is later selected by `exists_perm_antitone`.-/
def LidskiiSelectedProducts (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (n : ℕ) [NeZero n]
    (B Y : Matrix (Fin n) (Fin n) 𝕜)
    (hB : B.PosDef) (hY : Y.PosDef)
    (p : Equiv.Perm (Fin n))
    (k : ℕ) (_hk0 : 0 < k) (hk : k < n),
      prefixProd (fun i ↦
        decreasingEigenvalues hB.isHermitian (p i) /
          decreasingEigenvalues hY.isHermitian (p i))
          k hk.le ≤
        prefixProd (decreasingEigenvalues
          (relativeMatrix_posDef hY hB).isHermitian) k hk.le

/-- The selected Gram-eigenvalue product inequality used in the reduction.
It is exactly the squared singular-value statement for square matrices, but
avoids any bridge between Mathlib's ordered matrix eigenvalues and its
linear-map singular-value sequence.-/
def SelectedGramProduct (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (n : ℕ)
    (S T : Matrix (Fin n) (Fin n) 𝕜)
    (p : Equiv.Perm (Fin n))
    (k : ℕ) (_hk0 : 0 < k) (hk : k < n),
      prefixProd (fun i ↦ decreasingEigenvalues
        (Matrix.isHermitian_conjTranspose_mul_self (S * T)) (p i))
          k hk.le ≤
        prefixProd (decreasingEigenvalues
          (Matrix.isHermitian_conjTranspose_mul_self S)) k hk.le *
        prefixProd (fun i ↦ decreasingEigenvalues
          (Matrix.isHermitian_conjTranspose_mul_self T) (p i)) k hk.le

/-- Ordered eigenvalues are unchanged when the underlying Hermitian matrices
are equal.  Stating this separately avoids dependent rewriting through the
Hermitian proof argument.-/
lemma decreasingEigenvalues_congr
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A C : Matrix (Fin n) (Fin n) 𝕜}
    (hA : A.IsHermitian) (hC : C.IsHermitian) (h : A = C) :
    decreasingEigenvalues hA = decreasingEigenvalues hC := by
  subst C
  rfl

/-- The selected Gram-eigenvalue inequality implies the exact
selected ratio-product statement needed for multiplicative Lidskii.-/
theorem selectedProducts_of_gram
    {𝕜 : Type*} [RCLike 𝕜]
    (hgram : SelectedGramProduct 𝕜) : LidskiiSelectedProducts 𝕜 := by
  intro n _ B Y hB hY p k hk0 hk
  let R : Matrix (Fin n) (Fin n) 𝕜 := B ^ (1 / 2 : ℝ)
  let Q : Matrix (Fin n) (Fin n) 𝕜 := Y ^ (1 / 2 : ℝ)
  let Z : Matrix (Fin n) (Fin n) 𝕜 := Y ^ (-(1 / 2 : ℝ))
  let S : Matrix (Fin n) (Fin n) 𝕜 := R * Z
  have hRstar : R.conjTranspose = R :=
    (Matrix.PosDef.rpow hB _).isHermitian.eq
  have hQstar : Q.conjTranspose = Q :=
    (Matrix.PosDef.rpow hY _).isHermitian.eq
  have hZstar : Z.conjTranspose = Z :=
    (Matrix.PosDef.rpow hY _).isHermitian.eq
  have hRR : R * R = B := by
    simpa [R] using Matrix.PosDef.half_mul_half hB
  have hQQ : Q * Q = Y := by
    simpa [Q] using Matrix.PosDef.half_mul_half hY
  have hZQ : Z * Q = 1 := by
    simpa [Z, Q] using Matrix.PosDef.invHalf_mul_half hY
  have hST : S * Q = R := by
    simp only [S]
    rw [Matrix.mul_assoc, hZQ, Matrix.mul_one]
  have hSTgram : (S * Q).conjTranspose * (S * Q) = B := by
    rw [hST, hRstar, hRR]
  have hSgram : S.conjTranspose * S = relativeMatrix Y B := by
    simp only [S, Matrix.conjTranspose_mul, hRstar, hZstar]
    calc
      (Z * R) * (R * Z) = Z * (R * R) * Z := by noncomm_ring
      _ = Z * B * Z := by rw [hRR]
      _ = relativeMatrix Y B := rfl
  have hQgram : Q.conjTranspose * Q = Y := by rw [hQstar, hQQ]
  have h := hgram n S Q p k hk0 hk
  have hSTeigs := decreasingEigenvalues_congr
    (Matrix.isHermitian_conjTranspose_mul_self (S * Q)) hB.isHermitian hSTgram
  have hSeigs := decreasingEigenvalues_congr
    (Matrix.isHermitian_conjTranspose_mul_self S)
    (relativeMatrix_posDef hY hB).isHermitian hSgram
  have hQeigs := decreasingEigenvalues_congr
    (Matrix.isHermitian_conjTranspose_mul_self Q) hY.isHermitian hQgram
  rw [hSTeigs, hSeigs, hQeigs] at h
  have hprodY : 0 < prefixProd
      (fun i ↦ decreasingEigenvalues hY.isHermitian (p i)) k hk.le :=
    prefixProd_pos
      (fun i ↦ Matrix.PosDef.decreasingEigenvalues_pos hY _) k hk.le
  rw [prefixProd, prefixProd, Finset.prod_div_distrib]
  apply (div_le_iff₀ hprodY).2
  simpa [prefixProd, mul_comm] using h

/-- A multiplicative reformulation of the remaining proper-prefix step.
It has the same sorting permutation as `LidskiiProperPrefix`, but its analytic
hypothesis is a product inequality rather than a logarithmic sum inequality.

This is the convenient intermediate target for singular-value methods.-/
def LidskiiRatioProducts (𝕜 : Type*) [RCLike 𝕜] : Prop :=
  ∀ (n : ℕ) [NeZero n]
    (B Y : Matrix (Fin n) (Fin n) 𝕜)
    (hB : B.PosDef) (hY : Y.PosDef),
      ∃ p : Equiv.Perm (Fin n),
        Antitone (fun i ↦
          Real.log (decreasingEigenvalues hB.isHermitian (p i)) -
            Real.log (decreasingEigenvalues hY.isHermitian (p i))) ∧
        ∀ (k : ℕ) (_hk0 : 0 < k) (hk : k < n),
          prefixProd (fun i ↦
            decreasingEigenvalues hB.isHermitian (p i) /
              decreasingEigenvalues hY.isHermitian (p i))
              k hk.le ≤
            prefixProd (decreasingEigenvalues
              (relativeMatrix_posDef hY hB).isHermitian) k hk.le

/-- The universal selected-product inequality supplies the rearranged
ratio-product statement using only Mathlib's finite tuple sorting.-/
theorem ratioProducts_of_selectedProducts
    {𝕜 : Type*} [RCLike 𝕜]
    (hselected : LidskiiSelectedProducts 𝕜) : LidskiiRatioProducts 𝕜 := by
  intro n _ B Y hB hY
  let x : Fin n → ℝ := fun i ↦
    Real.log (decreasingEigenvalues hB.isHermitian i) -
      Real.log (decreasingEigenvalues hY.isHermitian i)
  obtain ⟨p, hp⟩ := exists_perm_antitone x
  refine ⟨p, ?_, ?_⟩
  · simpa [x] using hp
  · intro k hk0 hk
    exact hselected n B Y hB hY p k hk0 hk

/-- Removing logarithms loses no content: the selected ratio-product bound
implies every proper-prefix logarithmic inequality.-/
theorem lidskiiProperPrefix_of_ratioProducts
    {𝕜 : Type*} [RCLike 𝕜]
    (hproducts : LidskiiRatioProducts 𝕜) : LidskiiProperPrefix 𝕜 := by
  intro n _ B Y hB hY
  obtain ⟨p, hp, hproduct⟩ := hproducts n B Y hB hY
  refine ⟨p, hp, ?_⟩
  intro k hk
  by_cases hk0 : k = 0
  · subst k
    simp [prefixSum]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hkn : k ≤ n := hk.le
  have hb : ∀ i, 0 < decreasingEigenvalues hB.isHermitian i :=
    Matrix.PosDef.decreasingEigenvalues_pos hB
  have hy : ∀ i, 0 < decreasingEigenvalues hY.isHermitian i :=
    Matrix.PosDef.decreasingEigenvalues_pos hY
  have hd : ∀ i, 0 < decreasingEigenvalues
      (relativeMatrix_posDef hY hB).isHermitian i :=
    Matrix.PosDef.decreasingEigenvalues_pos (relativeMatrix_posDef hY hB)
  rw [prefixSum_eq_sum_fin _ k hkn, prefixSum_eq_sum_fin _ k hkn]
  have hleft :
      (∑ i : Fin k,
        (Real.log (decreasingEigenvalues hB.isHermitian
            (p (Fin.castLE hkn i))) -
          Real.log (decreasingEigenvalues hY.isHermitian
            (p (Fin.castLE hkn i))))) =
        Real.log (prefixProd (fun i ↦
          decreasingEigenvalues hB.isHermitian (p i) /
            decreasingEigenvalues hY.isHermitian (p i)) k hkn) := by
    calc
      _ = ∑ i : Fin k, Real.log
          (decreasingEigenvalues hB.isHermitian (p (Fin.castLE hkn i)) /
            decreasingEigenvalues hY.isHermitian (p (Fin.castLE hkn i))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Real.log_div (hb _).ne' (hy _).ne']
      _ = Real.log (prefixProd (fun i ↦
          decreasingEigenvalues hB.isHermitian (p i) /
            decreasingEigenvalues hY.isHermitian (p i)) k hkn) := by
        rw [prefixProd, Real.log_prod]
        intro i _
        exact (div_pos (hb _) (hy _)).ne'
  have hright :
      (∑ i : Fin k, Real.log (decreasingEigenvalues
        (relativeMatrix_posDef hY hB).isHermitian (Fin.castLE hkn i))) =
        Real.log (prefixProd (decreasingEigenvalues
          (relativeMatrix_posDef hY hB).isHermitian) k hkn) := by
    rw [prefixProd, Real.log_prod]
    intro i _
    exact (hd _).ne'
  rw [hleft, hright]
  exact Real.strictMonoOn_log.monotoneOn
    (prefixProd_pos (fun i ↦ div_pos (hb _) (hy _)) k hkn)
    (prefixProd_pos hd k hkn)
    (hproduct k hkpos hk)

/-- Matrix multiplication becomes composition under `Matrix.toEuclideanLin`.
This elementary compatibility is not currently a named Mathlib theorem.-/
lemma toEuclideanLin_mul
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (A B : Matrix (Fin n) (Fin n) 𝕜) :
    Matrix.toEuclideanLin (A * B) =
      (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) := by
  ext v i
  simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]

/-- Taking the pointwise star of a conjugate-transpose matrix-vector product
turns it into the corresponding row-vector product.-/
lemma star_conjTranspose_mulVec
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (A : Matrix (Fin n) (Fin n) 𝕜) (x : Fin n → 𝕜) :
    star (A.conjTranspose.mulVec x) = Matrix.vecMul (star x) A := by
  funext i
  change star (∑ j, star (A j i) * x j) = ∑ j, star (x j) * A j i
  simp [mul_comm]

/-- Conjugate transpose of a matrix represents the Hilbert-space adjoint of
its Euclidean linear map.-/
lemma adjoint_toEuclideanLin
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (A : Matrix (Fin n) (Fin n) 𝕜) :
    LinearMap.adjoint (Matrix.toEuclideanLin A) =
      Matrix.toEuclideanLin A.conjTranspose := by
  symm
  apply (LinearMap.eq_adjoint_iff _ _).2
  intro x y
  simp only [Matrix.toLpLin_apply,
    EuclideanSpace.inner_eq_star_dotProduct]
  rw [star_conjTranspose_mulVec]
  rw [dotProduct_comm, ← Matrix.dotProduct_mulVec, dotProduct_comm]

/-- Ordered eigenvalues of symmetric linear maps are unchanged when the maps
are equal.-/
lemma symmetricEigenvalues_congr
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E]
    {L M : E →ₗ[𝕜] E}
    (hL : L.IsSymmetric) (hM : M.IsSymmetric) (h : L = M)
    {n : ℕ} (hn : Module.finrank 𝕜 E = n) :
    hL.eigenvalues hn = hM.eigenvalues hn := by
  subst M
  rfl

/-- Mathlib's singular values of a matrix linear map square to the decreasing
eigenvalues of its Gram matrix.-/
lemma singularValues_sq_eq_decreasingEigenvalues_gram
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (A : Matrix (Fin n) (Fin n) 𝕜) (i : Fin n) :
    (Matrix.toEuclideanLin A).singularValues i ^ 2 =
      decreasingEigenvalues
        (Matrix.isHermitian_conjTranspose_mul_self A) i := by
  let ii : Fin (Fintype.card (Fin n)) :=
    finCongr (Fintype.card_fin n).symm i
  have hfin : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) =
      Fintype.card (Fin n) := by
    simp
  have hs := LinearMap.sq_singularValues_fin
    (Matrix.toEuclideanLin A) hfin ii
  have hgramlin :
      (LinearMap.adjoint (Matrix.toEuclideanLin A)).comp
          (Matrix.toEuclideanLin A) =
        Matrix.toEuclideanLin (A.conjTranspose * A) := by
    rw [adjoint_toEuclideanLin, toEuclideanLin_mul]
  have heigs := symmetricEigenvalues_congr
    (LinearMap.isSymmetric_adjoint_comp_self (Matrix.toEuclideanLin A))
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (Matrix.isHermitian_conjTranspose_mul_self A)) hgramlin hfin
  rw [heigs] at hs
  simpa [decreasingEigenvalues, Matrix.IsHermitian.eigenvalues₀, ii] using hs

/-- Once the proper-prefix inequality is available, Mathlib's determinant
identities complete the published `Lidskii` statement.-/
theorem lidskii_of_properPrefix
    {𝕜 : Type*} [RCLike 𝕜]
    (hprefix : LidskiiProperPrefix 𝕜) : Lidskii 𝕜 := by
  intro n _ B Y hB hY
  let x : Fin n → ℝ := fun i ↦
    Real.log (decreasingEigenvalues hB.isHermitian i) -
      Real.log (decreasingEigenvalues hY.isHermitian i)
  let y : Fin n → ℝ := fun i ↦ Real.log (decreasingEigenvalues
    (relativeMatrix_posDef hY hB).isHermitian i)
  obtain ⟨p, hp, hproper⟩ := hprefix n B Y hB hY
  have hy0 : ∀ i, 0 < decreasingEigenvalues
      (relativeMatrix_posDef hY hB).isHermitian i :=
    Matrix.PosDef.decreasingEigenvalues_pos (relativeMatrix_posDef hY hB)
  have hy : Antitone y := by
    intro i j hij
    exact Real.strictMonoOn_log.monotoneOn (by simpa [y] using hy0 j)
      (by simpa [y] using hy0 i)
      (decreasingEigenvalues_antitone
        (relativeMatrix_posDef hY hB).isHermitian hij)
  have htotal : (∑ i, x i) = ∑ i, y i := by
    simpa [x, y] using sum_log_ratio_eq_sum_log_relative hB hY
  refine ⟨p, Equiv.refl (Fin n), ?_, ?_, ?_, ?_⟩
  · simpa [x] using hp
  · simpa using hy
  · intro k hk
    by_cases hkn : k = n
    · subst k
      rw [prefixSum_card, prefixSum_card]
      calc
        (∑ i, x (p i)) = ∑ i, x i := Equiv.sum_comp p x
        _ = ∑ i, y i := htotal
        _ ≤ ∑ i, y ((Equiv.refl (Fin n)) i) := by simp
    · simpa [x, y] using hproper k (lt_of_le_of_ne hk hkn)
  · rw [prefixSum_card, prefixSum_card]
    calc
      (∑ i, x (p i)) = ∑ i, x i := Equiv.sum_comp p x
      _ = ∑ i, y i := htotal
      _ = ∑ i, y ((Equiv.refl (Fin n)) i) := by simp

/-- Consequently the single Gram-form inequality is sufficient for the full
published `Lidskii` statement; all remaining arrows in this reduction are
proved in this file from Mathlib.-/
theorem lidskii_of_gram
    {𝕜 : Type*} [RCLike 𝕜]
    (hgram : SelectedGramProduct 𝕜) : Lidskii 𝕜 :=
  lidskii_of_properPrefix
    (lidskiiProperPrefix_of_ratioProducts
      (ratioProducts_of_selectedProducts
        (selectedProducts_of_gram hgram)))

/-- As a consistency check, multiplicative Lidskii is completely derivable
from Mathlib in dimension one; there are then no nontrivial proper prefixes.-/
theorem lidskii_dim_one
    {𝕜 : Type*} [RCLike 𝕜]
    (B Y : Matrix (Fin 1) (Fin 1) 𝕜)
    (hB : B.PosDef) (hY : Y.PosDef) :
    Majorized
      (fun i ↦ Real.log (decreasingEigenvalues hB.isHermitian i) -
        Real.log (decreasingEigenvalues hY.isHermitian i))
      (fun i ↦ Real.log (decreasingEigenvalues
        (relativeMatrix_posDef hY hB).isHermitian i)) := by
  let x : Fin 1 → ℝ := fun i ↦
    Real.log (decreasingEigenvalues hB.isHermitian i) -
      Real.log (decreasingEigenvalues hY.isHermitian i)
  let y : Fin 1 → ℝ := fun i ↦ Real.log (decreasingEigenvalues
    (relativeMatrix_posDef hY hB).isHermitian i)
  have htotal : (∑ i, x i) = ∑ i, y i := by
    simpa [x, y] using sum_log_ratio_eq_sum_log_relative hB hY
  refine ⟨Equiv.refl (Fin 1), Equiv.refl (Fin 1), ?_, ?_, ?_, ?_⟩
  · intro i j _
    rw [Subsingleton.elim i j]
  · intro i j _
    rw [Subsingleton.elim i j]
  · intro k hk
    have hk_cases : k = 0 ∨ k = 1 := by omega
    rcases hk_cases with rfl | rfl
    · simp [prefixSum]
    · change prefixSum x 1 ≤ prefixSum y 1
      rw [prefixSum_card, prefixSum_card]
      exact htotal.le
  · change prefixSum x 1 = prefixSum y 1
    rw [prefixSum_card, prefixSum_card]
    exact htotal

end HiaiLimPowerMeans
