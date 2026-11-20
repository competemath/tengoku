import Tengoku.Seed.Analysis.Matrix.PosDef
import Tengoku.Seed.Data.Fin.Rev

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ordered spectra of finite matrices

Mathlib's `Matrix.IsHermitian.eigenvalues₀` is indexed by
`Fin (Fintype.card n)` and is antitone.  Its convenience reindexing
`eigenvalues : n → ℝ` preserves the multiset but, for a general finite index
type, does not preserve the order.  The definitions below specialize to
`Fin n` and reindex by the canonical order-preserving cast, so the decreasing
order required by multiplicative Lidskii is explicit in the type.
-/

namespace HiaiLimPowerMeans

open Matrix
open scoped BigOperators ComplexOrder

/-- The eigenvalues of a Hermitian `n × n` matrix in decreasing order.-/
noncomputable def decreasingEigenvalues
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) : Fin n → ℝ :=
  hA.eigenvalues₀ ∘ finCongr (Fintype.card_fin n).symm

/-- The eigenvalues of a Hermitian matrix in increasing order.-/
noncomputable def increasingEigenvalues
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) : Fin n → ℝ :=
  decreasingEigenvalues hA ∘ Fin.rev

/-- The permutation that sends a decreasing-spectrum index to Mathlib's
convenience indexing of the same eigenvalue/eigenvector pair.-/
noncomputable def decreasingIndexEquiv (n : ℕ) : Fin n ≃ Fin n :=
  (finCongr (Fintype.card_fin n).symm).trans
    (Fintype.equivOfCardEq
      (Fintype.card_fin (Fintype.card (Fin n))))

theorem eigenvalues_decreasingIndexEquiv
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) (i : Fin n) :
    hA.eigenvalues (decreasingIndexEquiv n i) =
      decreasingEigenvalues hA i := by
  simp [Matrix.IsHermitian.eigenvalues, decreasingIndexEquiv,
    decreasingEigenvalues]

/-- A unitary eigenvector matrix whose columns follow the decreasingly
ordered spectrum.-/
noncomputable def decreasingEigenvectorUnitary
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    Matrix (Fin n) (Fin n) 𝕜 :=
  fun p i ↦ hA.eigenvectorUnitary p (decreasingIndexEquiv n i)

theorem decreasingEigenvectorUnitary_isometry
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    (decreasingEigenvectorUnitary hA).conjTranspose *
        decreasingEigenvectorUnitary hA = 1 := by
  have hu := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  ext i j
  have hij := congrArg
    (fun M : Matrix (Fin n) (Fin n) 𝕜 ↦
      M (decreasingIndexEquiv n i) (decreasingIndexEquiv n j)) hu
  simpa [decreasingEigenvectorUnitary, Matrix.mul_apply, Matrix.one_apply] using hij

theorem mul_decreasingEigenvectorUnitary
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    A * decreasingEigenvectorUnitary hA =
      decreasingEigenvectorUnitary hA *
        Matrix.diagonal (RCLike.ofReal ∘ decreasingEigenvalues hA) := by
  ext p i
  have h := congrFun
    (hA.mulVec_eigenvectorBasis (decreasingIndexEquiv n i)) p
  rw [Matrix.mul_diagonal]
  simpa [decreasingEigenvectorUnitary, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, eigenvalues_decreasingIndexEquiv,
    RCLike.real_smul_eq_coe_mul, mul_comm] using h

theorem decreasingEigenvalues_antitone
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    Antitone (decreasingEigenvalues hA) := by
  intro i j hij
  apply hA.eigenvalues₀_antitone
  exact hij

/-- The eigenvalues reindexed in increasing order form a monotone vector.-/
theorem increasingEigenvalues_monotone
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian) :
    Monotone (increasingEigenvalues hA) := by
  intro i j hij
  exact decreasingEigenvalues_antitone hA (Fin.rev_le_rev.mpr hij)

theorem Matrix.PosDef.decreasingEigenvalues_pos
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosDef) (i : Fin n) :
    0 < decreasingEigenvalues hA.isHermitian i := by
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  simpa [decreasingEigenvalues, Matrix.IsHermitian.eigenvalues, e] using
    hA.eigenvalues_pos (e (finCongr (Fintype.card_fin n).symm i))

/-- An antitone unitary diagonalization determines the decreasingly ordered
eigenvalue list.  This is the uniqueness bridge between an explicitly
constructed ordered eigenbasis and Mathlib's canonical ordered spectrum.-/
theorem decreasingEigenvalues_eq_of_diagonalization
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    (U : Matrix (Fin n) (Fin n) 𝕜) (f : Fin n → ℝ)
    (hf : Antitone f) (hU : U.conjTranspose * U = 1)
    (hrel : A * U = U * Matrix.diagonal (RCLike.ofReal ∘ f)) :
    decreasingEigenvalues hA = f := by
  have hUU : U * U.conjTranspose = 1 := mul_eq_one_comm.mp hU
  have hspec : A = U * Matrix.diagonal (RCLike.ofReal ∘ f) * U.conjTranspose := by
    calc
      A = A * (1 : Matrix (Fin n) (Fin n) 𝕜) := (Matrix.mul_one A).symm
      _ = A * (U * U.conjTranspose) := by rw [hUU]
      _ = (A * U) * U.conjTranspose := by rw [Matrix.mul_assoc]
      _ = (U * Matrix.diagonal (RCLike.ofReal ∘ f)) * U.conjTranspose := by rw [hrel]
  have hchar : A.charpoly =
      ∏ i, (Polynomial.X - Polynomial.C ((RCLike.ofReal ∘ f) i)) := by
    rw [hspec, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul,
      Matrix.charpoly_diagonal]
  have hroots :
      A.charpoly.roots =
        Multiset.map (RCLike.ofReal ∘ f) Finset.univ.val := by
    rw [hchar, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsort :
      (A.charpoly.roots.map RCLike.re).sort (· ≥ ·) = List.ofFn f := by
    simp_rw [hroots, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
      Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
    apply List.mergeSort_of_pairwise
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hf.sortedGE_ofFn
  have hspectrum := hA.sort_roots_charpoly_eq_eigenvalues₀
  have hbase :
      (fun i : Fin n ↦ hA.eigenvalues₀
        (Fin.cast (Fintype.card_fin n).symm i)) = f := by
    simpa using hspectrum.symm.trans hsort
  funext i
  change hA.eigenvalues₀
    (finCongr (Fintype.card_fin n).symm i) = f i
  rw [show finCongr (Fintype.card_fin n).symm i =
    Fin.cast (Fintype.card_fin n).symm i by
      apply Fin.ext
      rfl]
  exact congrFun hbase i

/-- Reverse the columns of a square matrix.-/
noncomputable def reverseColumns
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (U : Matrix (Fin n) (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  fun p i ↦ U p i.rev

theorem reverseColumns_isometry
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {U : Matrix (Fin n) (Fin n) 𝕜} (hU : U.conjTranspose * U = 1) :
    (reverseColumns U).conjTranspose * reverseColumns U = 1 := by
  ext i j
  have hij := congrArg
    (fun M : Matrix (Fin n) (Fin n) 𝕜 ↦ M i.rev j.rev) hU
  simpa [reverseColumns, Matrix.mul_apply, Matrix.one_apply] using hij

/-- Inversion reciprocates the spectrum and reverses its decreasing order.-/
theorem Matrix.PosDef.decreasingEigenvalues_inv
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.PosDef) (i : Fin n) :
    decreasingEigenvalues hA.inv.isHermitian i =
      (decreasingEigenvalues hA.isHermitian i.rev)⁻¹ := by
  let U := decreasingEigenvectorUnitary hA.isHermitian
  let D : Matrix (Fin n) (Fin n) 𝕜 :=
    Matrix.diagonal (RCLike.ofReal ∘ decreasingEigenvalues hA.isHermitian)
  let E : Matrix (Fin n) (Fin n) 𝕜 :=
    Matrix.diagonal (fun j ↦ RCLike.ofReal
      ((decreasingEigenvalues hA.isHermitian j)⁻¹))
  let Urev := reverseColumns U
  let f : Fin n → ℝ := fun j ↦
    (decreasingEigenvalues hA.isHermitian j.rev)⁻¹
  have hU : U.conjTranspose * U = 1 :=
    decreasingEigenvectorUnitary_isometry hA.isHermitian
  have hrel : A * U = U * D :=
    mul_decreasingEigenvectorUnitary hA.isHermitian
  have hDE : D * E = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    simp only [Function.comp_apply, RCLike.ofReal_inv]
    exact mul_inv_cancel₀ (RCLike.ofReal_ne_zero.mpr
      (Matrix.PosDef.decreasingEigenvalues_pos hA j).ne')
  letI : Invertible A := hA.isUnit.invertible
  have hInvRel : A⁻¹ * U = U * E := by
    apply (Matrix.inv_mul_eq_iff_eq_mul_of_invertible A U (U * E)).2
    calc
      U = U * (1 : Matrix (Fin n) (Fin n) 𝕜) := (Matrix.mul_one U).symm
      _ = U * (D * E) := by rw [hDE]
      _ = (U * D) * E := by rw [Matrix.mul_assoc]
      _ = (A * U) * E := by rw [hrel]
      _ = A * (U * E) := by rw [Matrix.mul_assoc]
  have hInvRelRev :
      A⁻¹ * Urev = Urev * Matrix.diagonal (RCLike.ofReal ∘ f) := by
    ext p j
    have hj := congrArg (fun M : Matrix (Fin n) (Fin n) 𝕜 ↦ M p j.rev) hInvRel
    rw [Matrix.mul_diagonal] at hj
    rw [Matrix.mul_diagonal]
    change (A⁻¹ * U) p j.rev =
      U p j.rev * RCLike.ofReal
        ((decreasingEigenvalues hA.isHermitian j.rev)⁻¹)
    simpa [E, Function.comp_def] using hj
  have hf : Antitone f := by
    intro p q hpq
    apply inv_anti₀
    · exact Matrix.PosDef.decreasingEigenvalues_pos hA p.rev
    · exact decreasingEigenvalues_antitone hA.isHermitian
        (Fin.rev_le_rev.mpr hpq)
  have hUrev : Urev.conjTranspose * Urev = 1 :=
    reverseColumns_isometry hU
  have hordered := decreasingEigenvalues_eq_of_diagonalization
    hA.inv.isHermitian Urev f hf hUrev hInvRelRev
  exact congrFun hordered i

/-- Reindexing to decreasing order does not change a finite sum.-/
theorem sum_comp_decreasingEigenvalues_eq_eigenvalues
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    {R : Type*} [AddCommMonoid R] (f : ℝ → R) :
    (∑ i, f (decreasingEigenvalues hA i)) =
      ∑ i, f (hA.eigenvalues i) := by
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  calc
    (∑ i, f (decreasingEigenvalues hA i)) =
        ∑ i, f (hA.eigenvalues₀ i) :=
      (finCongr (Fintype.card_fin n).symm).sum_comp
        (f ∘ hA.eigenvalues₀)
    _ = ∑ i, f (hA.eigenvalues i) := by
      exact (e.symm.sum_comp (f ∘ hA.eigenvalues₀)).symm

/-- Reindexing to decreasing order does not change a finite product.-/
theorem prod_comp_decreasingEigenvalues_eq_eigenvalues
    {n : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {A : Matrix (Fin n) (Fin n) 𝕜} (hA : A.IsHermitian)
    {R : Type*} [CommMonoid R] (f : ℝ → R) :
    (∏ i, f (decreasingEigenvalues hA i)) =
      ∏ i, f (hA.eigenvalues i) := by
  let e : Fin (Fintype.card (Fin n)) ≃ Fin n :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  calc
    (∏ i, f (decreasingEigenvalues hA i)) =
        ∏ i, f (hA.eigenvalues₀ i) :=
      (finCongr (Fintype.card_fin n).symm).prod_comp
        (f ∘ hA.eigenvalues₀)
    _ = ∏ i, f (hA.eigenvalues i) := by
      exact (e.symm.prod_comp (f ∘ hA.eigenvalues₀)).symm

end HiaiLimPowerMeans
