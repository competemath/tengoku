module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.HomogeneousTensorCoordinates
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.LinearMatrix
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.PolynomialFactorialWeights
public import Tengoku.Seed.LinearAlgebra.Dual.Lemmas
public import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Concrete coefficient transpose duality for polynomial differential
operators and actual matrices of ternary linear forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ChoppedPlane
open Module MvPolynomial
open SymmetricDerivative
open scoped TensorProduct
variable {K : Type*} [Field K]
variable {V W : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] {a c : ℕ}

/-- The homogeneous monomial in the shared finite exponent coordinates.
@isnad1 id=eq.0h3v.s10.f59396fc1634 from=translated src=- shape=30c0679f vocab=28472e66
-/
theorem formsBasis_val_tensorExponent (n : ℕ) (s : Sym (Fin 3) n) :
    (formsBasis K 3 n s).val = monomial (homogeneousTensorExponent n s) 1 := by
  simpa only [homogeneousTensorExponent, homogeneousTensorExponentEquiv, exponentEquiv]
    using formsBasis_val_monomial K 3 n s

/-- Apply the three coefficient operators after the three actual partial
derivatives of the synthesized monomials.-/
def operatorDifferential (T : Fin 3 → V →ₗ[K] W) (t : ℕ) :
    (Sym (Fin 3) (t + 1) → V) →ₗ[K] (Sym (Fin 3) t → W) :=
  LinearMap.pi fun s => ∑ b : Sym (Fin 3) (t + 1), ∑ i : Fin 3,
    (pderiv i (monomial (homogeneousTensorExponent (t + 1) b) 1 : Poly K 3)).coeff
        (homogeneousTensorExponent t s) • (T i).comp (LinearMap.proj b)

/--
@isnad1 id=eq.0h7v.s10.71a0edecf6c0 from=translated src=- shape=701e6c7d vocab=d2aaa7bb
-/
@[simp] theorem operatorDifferential_coeff (T : Fin 3 → V →ₗ[K] W) (t : ℕ)
    (x : Sym (Fin 3) (t + 1) → V) (s : Sym (Fin 3) t) :
    operatorDifferential T t x s = ∑ b : Sym (Fin 3) (t + 1), ∑ i : Fin 3,
      (pderiv i (monomial (homogeneousTensorExponent (t + 1) b) 1 : Poly K 3)).coeff
          (homogeneousTensorExponent t s) • T i (x b) := by
  simp only [operatorDifferential, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- The entries of the genuine linear-form matrix are the transposed
coefficients of the three operators, in the given coefficient-module bases.-/
def operatorLinearMatrix (bV : Basis (Fin a) K V) (bW : Basis (Fin c) K W)
    (T : Fin 3 → V →ₗ[K] W) : LinearMatrix K a c := fun k j =>
  ∑ i : Fin 3, (bW.repr (T i (bV k)) j) • (⟨X i, isHomogeneous_X K i⟩ : Forms K 3 1)

/--
@isnad1 id=eq.0h10v.s10.a28dac388d9c from=translated src=- shape=9b0bbd34 vocab=fa0d0d2b
-/
@[simp] theorem operatorLinearMatrix_val (bV : Basis (Fin a) K V)
    (bW : Basis (Fin c) K W) (T : Fin 3 → V →ₗ[K] W) (k : Fin a) (j : Fin c) :
    (operatorLinearMatrix bV bW T k j).val =
      ∑ i : Fin 3, C (bW.repr (T i (bV k)) j) * X i := by
  simp [operatorLinearMatrix, smul_eq_C_mul]

/-- Read one literal coefficient of one component of a homogeneous vector.-/
def polynomialVectorCoefficient {n : ℕ} (k : Fin a) (s : Fin 3 →₀ ℕ) :
    (Fin a → Forms K 3 n) →ₗ[K] K :=
  (lcoeff K s).comp ((Forms K 3 n).subtype.comp (LinearMap.proj k))

/--
@isnad1 id=eq.0h6v.s11.818170354b3a from=translated src=- shape=08bad5b3 vocab=96f65a9b
-/
@[simp] theorem polynomialVectorCoefficient_apply {n : ℕ} (k : Fin a)
    (s : Fin 3 →₀ ℕ) (g : Fin a → Forms K 3 n) :
    polynomialVectorCoefficient k s g = (g k).val.coeff s := rfl

/-- The factorial coefficient pairing identifies module-valued homogeneous
coefficients with the dual of a genuine polynomial vector space.-/
def operatorFactorialDualMap (b : Basis (Fin a) K V) (n : ℕ) :
    (Sym (Fin 3) n → V) →ₗ[K] Module.Dual K (Fin a → Forms K 3 n) where
  toFun x := ∑ s : Sym (Fin 3) n, ∑ k : Fin a,
    (factorialWeight K (homogeneousTensorExponent n s) * b.repr (x s) k) •
      polynomialVectorCoefficient k (homogeneousTensorExponent n s)
  map_add' x y := by
    simp [map_add, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' q x := by
    simp [map_smul, Finset.smul_sum, smul_smul, smul_eq_mul, mul_left_comm]

/--
@isnad1 id=eq.0h7v.s13.6f15e871e67c from=translated src=- shape=dae4aad0 vocab=5dcb001d
-/
@[simp] theorem operatorFactorialDualMap_apply (b : Basis (Fin a) K V) (n : ℕ)
    (x : Sym (Fin 3) n → V) (g : Fin a → Forms K 3 n) :
    operatorFactorialDualMap b n x g = ∑ s : Sym (Fin 3) n, ∑ k : Fin a,
      factorialWeight K (homogeneousTensorExponent n s) * b.repr (x s) k *
        (g k).val.coeff (homogeneousTensorExponent n s) := by
  simp [operatorFactorialDualMap, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]

/-- Testing the pairing on a single coefficient-one monomial reads precisely
one module coordinate, multiplied by its nonzero factorial.
@isnad1 id=eq.0h8v.s13.7c4f87bbb569 from=translated src=- shape=ce39a47e vocab=d542becb
-/
@[simp] theorem operatorFactorialDualMap_single_basis
    (b : Basis (Fin a) K V) (n : ℕ) (x : Sym (Fin 3) n → V)
    (k : Fin a) (s : Sym (Fin 3) n) :
    operatorFactorialDualMap b n x (Pi.single k (formsBasis K 3 n s)) =
      factorialWeight K (homogeneousTensorExponent n s) * b.repr (x s) k := by
  classical
  rw [operatorFactorialDualMap_apply]
  calc
    _ = ∑ q : Sym (Fin 3) n,
        factorialWeight K (homogeneousTensorExponent n q) * b.repr (x q) k *
          (formsBasis K 3 n s).val.coeff (homogeneousTensorExponent n q) := by
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_eq_single k]
      · simp only [Pi.single_eq_same]
      · intro j _ hj
        simp [hj]
      · simp
    _ = _ := by
      simp [formsBasis_val_tensorExponent, coeff_monomial,
        (homogeneousTensorExponent_injective n).eq_iff]

/--
@isnad1 id=injectiv.0h5v.s13.d7a7441fe18f from=translated src=- shape=2eff0f22 vocab=95bd1e08
-/
theorem operatorFactorialDualMap_injective [CharZero K]
    (b : Basis (Fin a) K V) (n : ℕ) :
    Function.Injective (operatorFactorialDualMap b n) := by
  intro x y h
  funext s
  apply b.repr.injective
  ext k
  have htest := congrArg (fun f => f (Pi.single k (formsBasis K 3 n s))) h
  simp only [operatorFactorialDualMap_single_basis] at htest
  exact mul_left_cancel₀ (factorialWeight_ne_zero K _) htest

/-- This pairing is a concrete perfect pairing in characteristic zero.-/
def operatorFactorialDual [CharZero K] (b : Basis (Fin a) K V) (n : ℕ) :
    (Sym (Fin 3) n → V) ≃ₗ[K] Module.Dual K (Fin a → Forms K 3 n) := by
  letI : Module.Finite K V := Module.Finite.of_basis b
  apply LinearMap.linearEquivOfInjective (operatorFactorialDualMap b n)
    (operatorFactorialDualMap_injective b n)
  rw [Subspace.dual_finrank_eq]
  simp [Module.finrank_pi_fintype, Module.finrank_eq_card_basis b,
    Module.finrank_eq_card_basis (formsBasis K 3 n), mul_comm]

/--
@isnad1 id=eq.0h6v.s14.ee72fd806aaf from=translated src=- shape=28f5c1ca vocab=a23805af
-/
@[simp] theorem operatorFactorialDual_apply [CharZero K] (b : Basis (Fin a) K V)
    (n : ℕ) (x : Sym (Fin 3) n → V) :
    operatorFactorialDual b n x = operatorFactorialDualMap b n x := rfl

/--
@isnad1 id=eq.0h8v.s10.8b409f9cf14c from=translated src=- shape=f85501a1 vocab=efbbfd71
-/
@[simp] theorem operatorDifferential_single (T : Fin 3 → V →ₗ[K] W) (t : ℕ)
    (b : Sym (Fin 3) (t + 1)) (v : V) (s : Sym (Fin 3) t) :
    operatorDifferential T t (Pi.single b v) s = ∑ i : Fin 3,
      (pderiv i (monomial (homogeneousTensorExponent (t + 1) b) 1 : Poly K 3)).coeff
        (homogeneousTensorExponent t s) • T i v := by
  classical
  rw [operatorDifferential_coeff, Finset.sum_eq_single b]
  · simp only [Pi.single_eq_same]
  · intro q _ hq
    simp [hq]
  · simp

/--
@isnad1 id=eq.0h11v.s11.23a0c7906034 from=translated src=- shape=de2d3705 vocab=508951b6
-/
@[simp] theorem operatorDifferential_single_repr (bW : Basis (Fin c) K W)
    (T : Fin 3 → V →ₗ[K] W) (t : ℕ) (b : Sym (Fin 3) (t + 1))
    (v : V) (s : Sym (Fin 3) t) (j : Fin c) :
    bW.repr (operatorDifferential T t (Pi.single b v) s) j = ∑ i : Fin 3,
      (pderiv i (monomial (homogeneousTensorExponent (t + 1) b) 1 : Poly K 3)).coeff
        (homogeneousTensorExponent t s) * bW.repr (T i v) j := by
  rw [operatorDifferential_single]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

/--
@isnad1 id=eq.0h8v.s13.b01706869046 from=translated src=- shape=5a86d25f vocab=e9b7a722
-/
@[simp] theorem operatorFactorialDualMap_single_module_basis
    (b : Basis (Fin a) K V) (n : ℕ) (s : Sym (Fin 3) n)
    (k : Fin a) (g : Fin a → Forms K 3 n) :
    operatorFactorialDualMap b n (Pi.single s (b k)) g =
      factorialWeight K (homogeneousTensorExponent n s) *
        (g k).val.coeff (homogeneousTensorExponent n s) := by
  classical
  rw [operatorFactorialDualMap_apply, Finset.sum_eq_single s]
  · simp [Pi.single_eq_same, Basis.repr_self, Finsupp.single_apply]
  · intro q _ hq
    simp [hq]
  · simp

/-- Literal multiplication coefficients of the transposed operator matrix.
@isnad1 id=eq.0h13v.s12.cb00dc64f3d0 from=translated src=- shape=daa1e068 vocab=531274a0
-/
theorem operatorLinearMatrix_mul_single_coeff
    (bV : Basis (Fin a) K V) (bW : Basis (Fin c) K W)
    (T : Fin 3 → V →ₗ[K] W) (t : ℕ) (j : Fin c) (s : Sym (Fin 3) t)
    (k : Fin a) (b : Sym (Fin 3) (t + 1)) :
    (linearMatrixMap (operatorLinearMatrix bV bW T) t
      (Pi.single j (formsBasis K 3 t s)) k).val.coeff
        (homogeneousTensorExponent (t + 1) b) = ∑ i : Fin 3,
      bW.repr (T i (bV k)) j *
        (X i * monomial (homogeneousTensorExponent t s) 1 : Poly K 3).coeff
          (homogeneousTensorExponent (t + 1) b) := by
  classical
  have hval : (linearMatrixMap (operatorLinearMatrix bV bW T) t
      (Pi.single j (formsBasis K 3 t s)) k).val =
      (operatorLinearMatrix bV bW T k j).val * (formsBasis K 3 t s).val := by
    rw [linearMatrixMap_val, Finset.sum_eq_single j]
    · simp only [Pi.single_eq_same]
    · intro l _ hl
      simp [hl]
    · simp
  rw [hval]
  rw [operatorLinearMatrix_val, formsBasis_val_tensorExponent, Finset.sum_mul, coeff_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, coeff_C_mul]

/-- The actual differential and actual polynomial matrix are adjoint under
the concrete factorial pairing. This is the coefficient transpose theorem.
@isnad1 id=eq.0h9v.s14.1147efa610bf from=translated src=- shape=74392fb4 vocab=4af2e37a
-/
theorem operatorFactorialDual_adjoint [CharZero K]
    (bV : Basis (Fin a) K V) (bW : Basis (Fin c) K W)
    (T : Fin 3 → V →ₗ[K] W) (t : ℕ) :
    (operatorFactorialDual bW t).toLinearMap.comp (operatorDifferential T t) =
      (linearMatrixMap (operatorLinearMatrix bV bW T) t).dualMap.comp
        (operatorFactorialDual bV (t + 1)).toLinearMap := by
  classical
  apply LinearMap.pi_ext'
  intro b
  apply bV.ext
  intro k
  apply LinearMap.pi_ext'
  intro j
  apply (formsBasis K 3 t).ext
  intro s
  change operatorFactorialDualMap bW t
      (operatorDifferential T t (Pi.single b (bV k))) (Pi.single j (formsBasis K 3 t s)) =
    operatorFactorialDualMap bV (t + 1) (Pi.single b (bV k))
      (linearMatrixMap (operatorLinearMatrix bV bW T) t (Pi.single j (formsBasis K 3 t s)))
  rw [operatorFactorialDualMap_single_basis, operatorFactorialDualMap_single_module_basis,
    operatorDifferential_single_repr, operatorLinearMatrix_mul_single_coeff,
    Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (factorialWeight K (homogeneousTensorExponent t s) *
        (pderiv i (monomial (homogeneousTensorExponent (t + 1) b) 1 : Poly K 3)).coeff
          (homogeneousTensorExponent t s)) * bW.repr (T i (bV k)) j := by ring
    _ = (factorialWeight K (homogeneousTensorExponent (t + 1) b) *
        (X i * monomial (homogeneousTensorExponent t s) 1 : Poly K 3).coeff
          (homogeneousTensorExponent (t + 1) b)) * bW.repr (T i (bV k)) j := by
      rw [factorialWeight_pderiv_monomial_pair]
    _ = _ := by ring

/--
@isnad1 id=iff.0h9v.s12.38e348510b75 from=translated src=- shape=1a41c48b vocab=5cc3aade
-/
theorem operatorDifferential_injective_iff_linearMatrixMap_surjective [CharZero K]
    (bV : Basis (Fin a) K V) (bW : Basis (Fin c) K W)
    (T : Fin 3 → V →ₗ[K] W) (t : ℕ) :
    Function.Injective (operatorDifferential T t) ↔
      Function.Surjective (linearMatrixMap (operatorLinearMatrix bV bW T) t) := by
  let S := operatorFactorialDual bV (t + 1)
  let E := operatorFactorialDual bW t
  let F := linearMatrixMap (operatorLinearMatrix bV bW T) t
  have hadj (x : Sym (Fin 3) (t + 1) → V) : E (operatorDifferential T t x) = F.dualMap (S x) :=
    LinearMap.congr_fun (operatorFactorialDual_adjoint bV bW T t) x
  constructor
  · intro hD
    apply LinearMap.dualMap_injective_iff.mp
    intro f g hfg
    obtain ⟨x, rfl⟩ := S.surjective f
    obtain ⟨y, rfl⟩ := S.surjective g
    have hxy : operatorDifferential T t x = operatorDifferential T t y :=
      E.injective (by rw [hadj, hadj]; exact hfg)
    exact congrArg S (hD hxy)
  · intro hF x y hxy
    apply S.injective
    apply (LinearMap.dualMap_injective_iff.mpr hF)
    rw [← hadj, ← hadj, hxy]

/--
@isnad1 id=iff.0h9v.s12.87892c18cfdb from=translated src=- shape=1a41c48b vocab=5cc3aade
-/
theorem operatorDifferential_surjective_iff_linearMatrixMap_injective [CharZero K]
    (bV : Basis (Fin a) K V) (bW : Basis (Fin c) K W)
    (T : Fin 3 → V →ₗ[K] W) (t : ℕ) :
    Function.Surjective (operatorDifferential T t) ↔
      Function.Injective (linearMatrixMap (operatorLinearMatrix bV bW T) t) := by
  let S := operatorFactorialDual bV (t + 1)
  let E := operatorFactorialDual bW t
  let F := linearMatrixMap (operatorLinearMatrix bV bW T) t
  have hadj (x : Sym (Fin 3) (t + 1) → V) : E (operatorDifferential T t x) = F.dualMap (S x) :=
    LinearMap.congr_fun (operatorFactorialDual_adjoint bV bW T t) x
  constructor
  · intro hD
    apply LinearMap.dualMap_surjective_iff.mp
    intro g
    obtain ⟨z, hz⟩ := E.surjective g
    obtain ⟨x, hx⟩ := hD z
    refine ⟨S x, ?_⟩
    rw [← hadj, hx, hz]
  · intro hF z
    obtain ⟨g, hg⟩ := (LinearMap.dualMap_surjective_iff.mpr hF) (E z)
    obtain ⟨x, rfl⟩ := S.surjective g
    refine ⟨x, E.injective ?_⟩
    rw [hadj, hg]

/-- Add one occurrence of an auxiliary variable to a homogeneous monomial
index. The exponent vector remains independent of the coefficient field.-/
def operatorRaisedIndex (t : ℕ) (s : Sym (Fin 3) t) (i : Fin 3) :
    Sym (Fin 3) (t + 1) :=
  (homogeneousTensorExponentEquiv (t + 1)).symm
    ⟨homogeneousTensorExponent t s + Finsupp.single i 1, by
      simp only [map_add, homogeneousTensorExponent_degree, Finsupp.degree_single]⟩

/--
@isnad1 id=eq.0h3v.s6.2bdc16f340ce from=translated src=- shape=91efbd74 vocab=4c4e484a
-/
@[simp] theorem operatorRaisedIndex_exponent (t : ℕ) (s : Sym (Fin 3) t) (i : Fin 3) :
    homogeneousTensorExponent (t + 1) (operatorRaisedIndex t s i) =
      homogeneousTensorExponent t s + Finsupp.single i 1 := by
  simp [operatorRaisedIndex, homogeneousTensorExponent]

/-- The differential has exactly the usual partial-derivative coefficient
recurrence, expressed in the finite homogeneous monomial indices.
@isnad1 id=eq.0h7v.s9.4ab114421d7d from=translated src=- shape=c401288c vocab=fe9bb945
-/
theorem operatorDifferential_apply (T : Fin 3 → V →ₗ[K] W) (t : ℕ)
    (x : Sym (Fin 3) (t + 1) → V) (s : Sym (Fin 3) t) :
    operatorDifferential T t x s = ∑ i : Fin 3,
      (((homogeneousTensorExponent t s) i + 1 : ℕ) : K) •
        T i (x (operatorRaisedIndex t s i)) := by
  classical
  rw [operatorDifferential_coeff, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coeff_pderiv, coeff_monomial]
  rw [← operatorRaisedIndex_exponent t s i]
  simp only [(homogeneousTensorExponent_injective (t + 1)).eq_iff, ite_mul,
    one_mul, zero_mul, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Nat.cast_add, Nat.cast_one]

end ChoppedPlane
