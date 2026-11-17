import Tengoku.Seed.RingTheory.AdjoinRoot
import Tengoku.Seed.Analysis.Normed.Module.Basic
import Tengoku.Seed.Analysis.Normed.Operator.LinearIsometry
import Tengoku.Seed.Analysis.Normed.Group.Ultra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The maximum coefficient norm on truncated polynomial algebras

The algebra `A = L[ε]/(ε^n)`, modelled as `AdjoinRoot (X ^ n)`, with the maximum norm on
coefficients in the basis `1, ε, …, ε^(n-1)`. Over an ultrametric field this norm is
submultiplicative, so `A` is a normed algebra. In Appendix H it is used with `n = p` and
`L = 𝔽_p((t))`.
-/

noncomputable section
open scoped BigOperators NNReal
namespace AlternatingAnalytic.TruncatedPolynomial

/-- The algebra `L[ε]/(ε^n)`.-/
abbrev A (L : Type*) [Field L] (n : ℕ) :=
  AdjoinRoot (Polynomial.X ^ n : Polynomial L)

variable (L : Type*) (n : ℕ)

section Algebra

variable [Field L]

/-- The element `ε`, the class of `X`.-/
def epsilon : A L n := AdjoinRoot.root (Polynomial.X ^ n : Polynomial L)

/-- The basis `1, ε, …, ε^(n-1)`, indexed by `Fin n`.-/
def basis : Module.Basis (Fin n) L (A L n) :=
  (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow n :
    (Polynomial.X ^ n : Polynomial L).Monic)).basis.reindex
      (finCongr (Polynomial.natDegree_X_pow n))

/-- Coefficients in the basis `1, ε, …, ε^(n-1)`.-/
def coeff : A L n ≃ₗ[L] (Fin n → L) := (basis L n).equivFun

/--
@isnad1 id=eq.0h3v.s9.3099beb4cdd2 from=translated src=- shape=5f589a20 vocab=9dbea1ba
-/
theorem basis_eq_pow (i : Fin n) : basis L n i = epsilon L n ^ (i : ℕ) := by
  simp only [basis, Module.Basis.reindex_apply,
    (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow n :
      (Polynomial.X ^ n : Polynomial L).Monic)).basis_eq_pow]
  rfl

/--
@isnad1 id=eq.0h2v.s8.412b0c947db7 from=translated src=- shape=f20c1d4a vocab=6ac8ce7b
-/
@[simp] theorem epsilon_pow : epsilon L n ^ n = 0 := by
  have h := AdjoinRoot.eval₂_root (Polynomial.X ^ n : Polynomial L)
  simpa [epsilon] using h

/--
@isnad1 id=eq.1h3v.s8.deb8d0b870ff from=translated src=- shape=09442427 vocab=189a16c0
-/
theorem epsilon_pow_eq_zero {m : ℕ} (h : n ≤ m) : epsilon L n ^ m = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, epsilon_pow, zero_mul]

/--
@isnad1 id=eq.0h4v.s10.079782676561 from=translated src=- shape=15fd8e47 vocab=1b87b6c0
-/
@[simp] theorem coeff_basis (i j : Fin n) :
    coeff L n (basis L n i) j = if i = j then 1 else 0 := by
  exact (basis L n).equivFun_self i j

/--
@isnad1 id=eq.0h4v.s10.3549b7f69739 from=translated src=- shape=30dbe85d vocab=479b26ca
-/
theorem coeff_pow (m : ℕ) (k : Fin n) :
    coeff L n (epsilon L n ^ m) k = if m = (k : ℕ) then 1 else 0 := by
  by_cases hm : m < n
  · rw [← basis_eq_pow L n ⟨m, hm⟩, coeff_basis]
    simp only [Fin.ext_iff]
  · rw [epsilon_pow_eq_zero L n (Nat.le_of_not_gt hm)]
    have hmk : m ≠ (k : ℕ) := by omega
    simp [hmk]

/--
@isnad1 id=eq.0h3v.s11.20cab9b1fab5 from=translated src=- shape=b87d1c52 vocab=fd4bcbae
-/
theorem expansion (x : A L n) : x = ∑ i : Fin n, coeff L n x i • basis L n i := by
  exact ((basis L n).sum_equivFun x).symm

/-- Multiplication is truncated convolution of coefficients.
@isnad1 id=eq.0h5v.s11.e70f1dda3085 from=translated src=- shape=b320794a vocab=99f5535c
-/
theorem coeff_mul (x y : A L n) (k : Fin n) :
    coeff L n (x * y) k =
      ∑ i : Fin n, ∑ j : Fin n,
        if (i : ℕ) + (j : ℕ) = (k : ℕ) then coeff L n x i * coeff L n y j else 0 := by
  conv_lhs => rw [expansion L n x, expansion L n y]
  simp_rw [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm,
    basis_eq_pow, ← pow_add, map_sum, map_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, coeff_pow, mul_ite, mul_one, mul_zero]

end Algebra

section Norm

variable [NontriviallyNormedField L]

/-- The maximum norm on coefficients.-/
instance instNormedAddCommGroup : NormedAddCommGroup (A L n) :=
  NormedAddCommGroup.induced (A L n) (Fin n → L) (coeff L n) (coeff L n).injective

instance instNormedSpace : NormedSpace L (A L n) :=
  NormedSpace.induced L (A L n) (Fin n → L) (coeff L n)

/-- The coefficient map is a linear isometry onto `Fin n → L` with the sup norm.-/
def coefficientIsometry : A L n ≃ₗᵢ[L] (Fin n → L) :=
  { coeff L n with norm_map' := fun _ => rfl }

/--
@isnad1 id=eq.0h3v.s11.798d493ac26e from=translated src=- shape=a7098208 vocab=38425670
-/
@[simp]
theorem coefficientIsometry_apply (x : A L n) :
    coefficientIsometry L n x = coeff L n x := rfl

/--
@isnad1 id=eq.0h3v.s10.06a622c43974 from=translated src=- shape=511d18e6 vocab=b5022ae3
-/
theorem coefficientIsometry_symm_apply (v : Fin n → L) :
    (coefficientIsometry L n).symm v = ∑ i : Fin n, v i • epsilon L n ^ (i : ℕ) := by
  change (basis L n).equivFun.symm v = _
  rw [Module.Basis.equivFun_symm_apply]
  simp_rw [basis_eq_pow]

/--
@isnad1 id=eq.0h3v.s10.c7da2d4fe30a from=translated src=- shape=a7d836d7 vocab=52c1e43f
-/
@[simp]
theorem norm_coeff (x : A L n) : ‖coeff L n x‖ = ‖x‖ := rfl

/-- The norm is the maximum of the coefficient norms.
@isnad1 id=eq.0h3v.s10.62455e000e8c from=translated src=- shape=b6f90ec5 vocab=a25ef69a
-/
theorem norm_eq_max (x : A L n) :
    ‖x‖ = (Finset.univ.sup fun i : Fin n => ‖coeff L n x i‖₊ : ℝ≥0) := rfl

/--
@isnad1 id=le.0h4v.s10.218da8779b9b from=translated src=- shape=c628f230 vocab=b3170172
-/
theorem norm_coefficient_le (x : A L n) (i : Fin n) :
    ‖coeff L n x i‖ ≤ ‖x‖ := norm_le_pi_norm (coeff L n x) i

/--
@isnad1 id=eq.0h3v.s9.efe5b6504d48 from=translated src=- shape=533a2da7 vocab=f9523454
-/
@[simp]
theorem norm_basis (i : Fin n) : ‖basis L n i‖ = 1 := by
  rw [← norm_coeff]
  have h : coeff L n (basis L n i) = Pi.single i 1 := by
    ext j
    simp [coeff_basis, Pi.single_apply, eq_comm]
  rw [h, Pi.norm_single, norm_one]

/--
@isnad1 id=eq.0h3v.s7.519f5a157be0 from=translated src=- shape=94ee0dab vocab=c2b6cabb
-/
@[simp]
theorem norm_epsilon_pow (i : Fin n) : ‖epsilon L n ^ (i : ℕ)‖ = 1 := by
  rw [← basis_eq_pow, norm_basis]

/--
@isnad1 id=complete.0h2v.s5.81c2fb532144 from=translated src=- shape=1ed5d3bc vocab=e9cd50b7
-/
instance instCompleteSpace [CompleteSpace L] : CompleteSpace (A L n) :=
  (coefficientIsometry L n).toIsometryEquiv.completeSpace

section Ultrametric

variable [IsUltrametricDist L]

/--
@isnad1 id=isultram.0h2v.s5.5598a2062175 from=translated src=- shape=1ed5d3bc vocab=15f6c1f8
-/
instance instIsUltrametricDist : IsUltrametricDist (A L n) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
    change ‖coeff L n (x + y)‖ ≤ max ‖coeff L n x‖ ‖coeff L n y‖
    rw [map_add]
    apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2
    intro i
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le_max (norm_le_pi_norm _ i) (norm_le_pi_norm _ i))

/-- Over an ultrametric field the norm is submultiplicative.
@isnad1 id=le.0h4v.s8.08dc890e25b8 from=translated src=- shape=d0932d62 vocab=8e54fbee
-/
theorem norm_mul_le (x y : A L n) : ‖x * y‖ ≤ ‖x‖ * ‖y‖ := by
  change ‖coeff L n (x * y)‖ ≤ ‖coeff L n x‖ * ‖coeff L n y‖
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
  intro k
  rw [coeff_mul]
  change ‖∑ i : Fin n, ∑ j : Fin n,
    if (i : ℕ) + (j : ℕ) = (k : ℕ) then coeff L n x i * coeff L n y j else 0‖₊ ≤
      ‖coeff L n x‖₊ * ‖coeff L n y‖₊
  apply (Finset.nnnorm_sum_le_sup_nnnorm _ _).trans
  apply Finset.sup_le
  intro i _
  apply (Finset.nnnorm_sum_le_sup_nnnorm _ _).trans
  apply Finset.sup_le
  intro j _
  split_ifs
  · rw [nnnorm_mul]
    exact mul_le_mul' (nnnorm_le_pi_nnnorm _ i) (nnnorm_le_pi_nnnorm _ j)
  · simp

instance instNormedCommRing : NormedCommRing (A L n) :=
  { instNormedAddCommGroup L n, (inferInstance : CommRing (A L n)) with
    norm_mul_le := norm_mul_le L n }

instance instNormedAlgebra : NormedAlgebra L (A L n) where
  norm_smul_le := (instNormedSpace L n).norm_smul_le

end Ultrametric
end Norm
end AlternatingAnalytic.TruncatedPolynomial
