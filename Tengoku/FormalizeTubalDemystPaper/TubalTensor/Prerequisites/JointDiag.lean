import Tengoku.Seed.Data.Complex.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.IsDiag
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
import Tengoku.Seed.LinearAlgebra.Eigenspace.Triangularizable
import Tengoku.Seed.LinearAlgebra.Eigenspace.Pi
import Tengoku.Seed.LinearAlgebra.Eigenspace.Semisimple
import Tengoku.Seed.LinearAlgebra.Eigenspace.Matrix
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin
import Tengoku.Seed.LinearAlgebra.Matrix.Basis
import Tengoku.Seed.LinearAlgebra.Semisimple
import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Defs
import Tengoku.Seed.FieldTheory.Separable
import Tengoku.Seed.Analysis.Complex.Polynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/Prerequisites/JointDiag.lean
  Lemma 38: Commuting diagonalizable matrices are jointly diagonalizable.

  This is a known result (Fact 5.17.8 in [2]). We prove it using Mathlib's
  eigenspace machinery for commuting endomorphisms.
-/

namespace TubalTensor

open Matrix Complex Module Module.Basis

-- IsAlgClosed ℂ is provided by Mathlib.Analysis.Complex.Polynomial.Basic
-- (instance: Complex.instIsAlgClosed)

/-! ## Matrix diagonalizability over ℂ -/

/-- A real matrix is *diagonalizable over ℂ* if it is similar to a diagonal complex matrix:
    there exists an invertible `S` and a diagonal `D` with `A_ℂ = S⁻¹ D S`.-/
def IsMatDiag {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ (S : Matrix (Fin n) (Fin n) ℂ) (D : Matrix (Fin n) (Fin n) ℂ),
    IsUnit S ∧ D.IsDiag ∧
    A.map ((↑) : ℝ → ℂ) = S * D * S⁻¹

/-- A set of real matrices is *jointly diagonalizable over ℂ* if there exists a single
    invertible `S` that simultaneously diagonalizes all of them.-/
def IsJointlyMatDiag {n : ℕ} (T : Set (Matrix (Fin n) (Fin n) ℝ)) : Prop :=
  ∃ (S : Matrix (Fin n) (Fin n) ℂ), IsUnit S ∧
    ∀ A ∈ T, ∃ D : Matrix (Fin n) (Fin n) ℂ,
      D.IsDiag ∧ A.map ((↑) : ℝ → ℂ) = S * D * S⁻¹

/-! ## Helper: lifting commutativity -/

private noncomputable abbrev mapOfReal {m₁ m₂ : ℕ} (A : Matrix (Fin m₁) (Fin m₂) ℝ) :
    Matrix (Fin m₁) (Fin m₂) ℂ :=
  A.map ((↑) : ℝ → ℂ)

private lemma commute_toLin'_of_commute_matrix {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (h : A * B = B * A) :
    Commute (mapOfReal A).toLin' (mapOfReal B).toLin' := by
  have key : mapOfReal A * mapOfReal B = mapOfReal B * mapOfReal A := by
    have := congr_arg (Complex.ofRealHom.mapMatrix (m := Fin n)) h
    simp only [_root_.map_mul] at this
    exact this
  show (mapOfReal A).toLin' * (mapOfReal B).toLin' =
       (mapOfReal B).toLin' * (mapOfReal A).toLin'
  simp only [End.mul_eq_comp, ← Matrix.toLin'_mul]
  exact congr_arg Matrix.toLin' key

/-! ## Semisimplicity of diagonalizable matrices -/

/-- For an eigenvector `v` of `f` with eigenvalue `μ`, polynomial evaluation
    acts by scalar evaluation: `(aeval f p) v = (p.eval μ) • v`.-/
private lemma aeval_apply_mem_eigenspace {n : ℕ}
    {f : End ℂ (Fin n → ℂ)} {μ : ℂ} {v : Fin n → ℂ}
    (hv : v ∈ f.eigenspace μ) (p : Polynomial ℂ) :
    (Polynomial.aeval f p) v = (p.eval μ) • v := by
  have hfv : f v = μ • v := End.mem_eigenspace_iff.mp hv
  have hpow : ∀ k : ℕ, (f ^ k) v = μ ^ k • v := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, End.mul_apply, hfv, map_smul, ih, smul_smul]; ring_nf
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, Polynomial.eval_add, add_smul, hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial, Polynomial.eval_monomial]
    rw [End.mul_apply, hpow, Module.algebraMap_end_apply ℂ ℂ, smul_smul]

/-- A diagonal matrix's `toLin'` is semisimple. Proved using
    `isSemisimple_of_squarefree_aeval_eq_zero` with the polynomial ∏_{μ distinct} (X - μ).
@isnad1 id=issemisi.0h2v.s10.e947f15b1cf8 from=translated src=- shape=54f96fa7 vocab=13356b1a
-/
theorem isSemisimple_toLin'_diagonal {n : ℕ} (d : Fin n → ℂ) :
    End.IsSemisimple (diagonal d).toLin' := by
  -- The polynomial p = ∏ μ ∈ (distinct eigenvalues), (X - C μ)
  set s := Finset.image d Finset.univ
  set p := ∏ μ ∈ s, (Polynomial.X - Polynomial.C μ) with hp_def
  -- p is squarefree (product of distinct linear factors is separable)
  have hp_sqf : Squarefree p :=
    (Polynomial.separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ h => h)).squarefree
  -- aeval f p = 0: check on each standard basis vector e_i (eigenvector with eigenvalue d_i)
  have hp_zero : Polynomial.aeval (diagonal d).toLin' p = 0 := by
    apply Basis.ext (Pi.basisFun ℂ (Fin n)); intro i
    simp only [LinearMap.zero_apply]
    rw [aeval_apply_mem_eigenspace (hasEigenvector_toLin'_diagonal d i).1]
    simp only [hp_def, Polynomial.eval_prod, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]
    rw [Finset.prod_eq_zero (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩) (sub_self _)]
    simp
  exact End.isSemisimple_of_squarefree_aeval_eq_zero hp_sqf hp_zero

/-- A matrix similar to a diagonal has semisimple `toLin'`.-/
private lemma isSemisimple_toLin'_of_similar_diagonal {n : ℕ}
    (M S D : Matrix (Fin n) (Fin n) ℂ)
    (hS : IsUnit S) (hD : D.IsDiag)
    (hM : M = S * D * S⁻¹) : End.IsSemisimple M.toLin' := by
  -- D is a diagonal matrix: extract diagonal entries
  have hdiag : ∃ d : Fin n → ℂ, D = diagonal d := by
    use fun i => D i i
    ext i j
    simp only [diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · exact hD h
  obtain ⟨d, rfl⟩ := hdiag
  have hDss := isSemisimple_toLin'_diagonal d
  -- Get IsUnit S.det for nonsing_inv lemmas
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  -- Construct linear equivalence from S
  let e : (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) :=
    LinearEquiv.ofLinearMap S.toLin' S⁻¹.toLin'
      (by simp only [← Matrix.toLin'_mul]; rw [mul_nonsing_inv _ hdet]; exact Matrix.toLin'_one)
      (by simp only [← Matrix.toLin'_mul]; rw [nonsing_inv_mul _ hdet]; exact Matrix.toLin'_one)
  -- Conjugation relation: e ∘ₗ D.toLin' = M.toLin' ∘ₗ e
  have he : (e : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ∘ₗ (diagonal d).toLin' = M.toLin' ∘ₗ e := by
    simp only [LinearMap.ext_iff]
    intro v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, e, LinearEquiv.coe_ofLinearMap]
    rw [← Matrix.toLin'_mul_apply, ← Matrix.toLin'_mul_apply]
    congr 1
    -- Need: S * diagonal d = M * S, i.e., S * D = (S * D * S⁻¹) * S
    rw [hM, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hdet, Matrix.mul_one]
  rwa [← e.isSemisimple_iff (diagonal d).toLin' M.toLin' he]

/-- `IsMatDiag A` implies the associated ℂ-linear map is finitely semisimple.-/
private lemma isFinitelySemisimple_of_isMatDiag {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsMatDiag A) :
    End.IsFinitelySemisimple (mapOfReal A).toLin' := by
  obtain ⟨S, D, hS, hD, hSDinv⟩ := hA
  exact (isSemisimple_toLin'_of_similar_diagonal _ S D hS hD hSDinv).isFinitelySemisimple

/-! ## From eigenbasis to joint diagonalizer matrix -/

/-- Given a basis b where each basis vector is an eigenvector of M.toLin',
    M equals the conjugation of diagonal(eigenvalues) by the change-of-basis matrix.-/
private lemma matrix_eq_conj_diagonal_of_eigenbasis {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ)
    (b : Basis (Fin n) ℂ (Fin n → ℂ))
    (μ : Fin n → ℂ)
    (heig : ∀ i : Fin n, M.toLin' (b i) = μ i • b i) :
    let S := (Pi.basisFun ℂ (Fin n)).toMatrix b
    M = S * diagonal μ * S⁻¹ := by
  intro S
  let e := Pi.basisFun ℂ (Fin n)
  -- Step 1: The representation of M.toLin' in basis b is diagonal μ
  -- because each b i is an eigenvector with eigenvalue μ i.
  have hdiag : LinearMap.toMatrix b b M.toLin' = diagonal μ := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    -- Need: (b.repr (M.toLin' (b j))) i = (diagonal μ) i j
    have hj := heig j
    -- hj : M.toLin' (b j) = μ j • b j
    rw [hj, map_smul, Basis.repr_self, diagonal_apply]
    simp only [Finsupp.coe_smul, Pi.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite,
               mul_one, mul_zero]
    -- Goal: (if j = i then μ j else 0) = (if i = j then μ i else 0)
    by_cases h : i = j <;> simp [h, eq_comm]
  -- Step 2: Change of basis formula gives
  -- e.toMatrix b * (LinearMap.toMatrix b b f) * b.toMatrix e = LinearMap.toMatrix e e f
  have hcob : S * (LinearMap.toMatrix b b M.toLin') * b.toMatrix e =
      LinearMap.toMatrix e e M.toLin' :=
    basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
      (b := e) (c := e) (b' := b) (c' := b) (f := M.toLin')
  -- LinearMap.toMatrix e e M.toLin' = M (since e is the standard basis)
  have hstd : LinearMap.toMatrix e e M.toLin' = M := by
    change LinearMap.toMatrix (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) M.toLin' = M
    rw [show Matrix.toLin' = Matrix.toLin (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n))
        from rfl]
    exact LinearMap.toMatrix_toLin (Pi.basisFun ℂ (Fin n)) (Pi.basisFun ℂ (Fin n)) M
  -- S⁻¹ = b.toMatrix e
  have hSinv : S⁻¹ = b.toMatrix e := by
    exact Matrix.inv_eq_right_inv (e.toMatrix_mul_toMatrix_flip b)
  rw [hdiag, hstd] at hcob
  rw [hSinv]
  exact hcob.symm

/-- **Lemma 38** (Fact 5.17.8 in [2]): Let `T` be a set of pairwise-commuting real matrices
    that are each diagonalizable over ℂ. Then `T` is jointly diagonalizable.

    Proved using Mathlib's eigenspace decomposition for commuting endomorphisms.
@isnad1 id=isjointl.2h2v.s7.4c873b5e25c3 from=translated src=- shape=926ce265 vocab=c484113d
-/
theorem jointly_diag_of_commuting {n : ℕ} (T : Set (Matrix (Fin n) (Fin n) ℝ))
    (hdiag : ∀ A ∈ T, IsMatDiag A)
    (hcomm : ∀ A ∈ T, ∀ B ∈ T, A * B = B * A) :
    IsJointlyMatDiag T := by
  -- Define the family of endomorphisms indexed by T
  set f : T → End ℂ (Fin n → ℂ) := fun ⟨A, _⟩ => (mapOfReal A).toLin' with hf_def

  -- Each f_A is finitely semisimple
  have hss : ∀ (A : T), (f A).IsFinitelySemisimple :=
    fun ⟨A, hA⟩ => isFinitelySemisimple_of_isMatDiag A (hdiag A hA)

  -- Semisimple => maxGenEigenspace = eigenspace
  have hmge : ∀ (A : T) (μ : ℂ),
      (f A).maxGenEigenspace μ = (f A).eigenspace μ :=
    fun A μ => (hss A).maxGenEigenspace_eq_eigenspace μ

  -- Pairwise commuting
  have hpw : Pairwise fun (i j : T) => Commute (f i) (f j) := by
    intro ⟨A, hA⟩ ⟨B, hB⟩ hne
    exact commute_toLin'_of_commute_matrix A B (hcomm A hA B hB)

  -- Over ℂ (algebraically closed), each has ⨆ μ, maxGenEigenspace = ⊤
  have hspan : ∀ (A : T), ⨆ μ, (f A).maxGenEigenspace μ = ⊤ :=
    fun A => End.iSup_maxGenEigenspace_eq_top (f A)

  -- Joint generalized eigenspace decomposition = ⊤
  have hjoint : ⨆ χ : T → ℂ, ⨅ (A : T), (f A).maxGenEigenspace (χ A) = ⊤ :=
    End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f hpw hspan

  -- Since each is semisimple, joint generalized eigenspaces = joint eigenspaces
  have hjoint_eig : ⨆ χ : T → ℂ, ⨅ (A : T), (f A).eigenspace (χ A) = ⊤ := by
    simp_rw [← hmge] at hjoint ⊢
    exact hjoint

  -- The joint eigenspaces span ⊤ (rewrite to span form for Basis.ofSpan)
  have hU_top : ⊤ ≤ ⨆ (χ : T → ℂ), ⨅ (A : T), (f A).eigenspace (χ A) :=
    hjoint_eig ▸ le_refl _
  rw [Submodule.iSup_eq_span] at hU_top
  -- Get a basis contained in the union of joint eigenspaces
  let b₀ := ofSpan hU_top
  letI := FiniteDimensional.fintypeBasisIndex b₀
  -- finrank = n
  have hfinrank : Module.finrank ℂ (Fin n → ℂ) = n := by
    simp
  -- Reindex to Fin n
  have hcard := (finrank_eq_card_basis b₀).symm.trans hfinrank
  let b := b₀.reindex (Fintype.equivFinOfCardEq hcard)
  -- Each basis element is in a joint eigenspace
  have hb_mem : ∀ j, ∃ χ : T → ℂ,
      b j ∈ (⨅ (A : T), (f A).eigenspace (χ A) : Submodule ℂ _) := by
    intro j
    have hj : b j ∈ Set.range (⇑b₀) := ⟨_, (Basis.reindex_apply b₀ _ j).symm⟩
    exact Set.mem_iUnion.mp (ofSpan_subset hU_top hj)
  choose χ hχ using hb_mem
  -- Each b j is an eigenvector for every f A
  have hb_eig : ∀ (A : T) (j : Fin n), (f A) (b j) = χ j A • b j :=
    fun A j ↦ End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp (hχ j) A)
  -- Construct S (change-of-basis matrix) and prove the result
  let e := Pi.basisFun ℂ (Fin n)
  refine ⟨e.toMatrix b,
    IsUnit.of_mul_eq_one _ (e.toMatrix_mul_toMatrix_flip b), ?_⟩
  intro A hA
  exact ⟨diagonal (fun j ↦ χ j ⟨A, hA⟩), isDiag_diagonal _,
    matrix_eq_conj_diagonal_of_eigenbasis (mapOfReal A) b _
      (fun j ↦ hb_eig ⟨A, hA⟩ j)⟩

end TubalTensor
