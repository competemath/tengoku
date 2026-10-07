/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.MvPolynomial.Monad
public import Tengoku.Seed.LinearAlgebra.Charpoly.ToMatrix
public import Tengoku.Seed.LinearAlgebra.FreeModule.StrongRankCondition
public import Tengoku.Seed.LinearAlgebra.Matrix.Charpoly.Univ
public import Tengoku.Seed.RingTheory.TensorProduct.Finite
public import Tengoku.Seed.RingTheory.TensorProduct.Free

/-!
# Characteristic polynomials of linear families of endomorphisms

The coefficients of the characteristic polynomials of a linear family of endomorphisms
are homogeneous polynomials in the parameters.
This result is used in Lie theory
to establish the existence of regular elements and Cartan subalgebras,
and ultimately a well-defined notion of rank for Lie algebras.

In this file we prove this result about characteristic polynomials.
Let `L` and `M` be modules over a nontrivial commutative ring `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear map.
Let `b` be a basis of `L`, indexed by `ι`.
Then we define a multivariate polynomial with variables indexed by `ι`
that evaluates on elements `x` of `L` to the characteristic polynomial of `φ x`.

## Main declarations

* `Matrix.toMvPolynomial M i`: the family of multivariate polynomials that evaluates on `c : n → R`
  to the dot product of the `i`-th row of `M` with `c`.
  `Matrix.toMvPolynomial M i` is the sum of the monomials `C (M i j) * X j`.
* `LinearMap.toMvPolynomial b₁ b₂ f`: a version of `Matrix.toMvPolynomial` for linear maps `f`
  with respect to bases `b₁` and `b₂` of the domain and codomain.
* `LinearMap.polyCharpoly`: the multivariate polynomial that evaluates on elements `x` of `L`
  to the characteristic polynomial of `φ x`.
* `LinearMap.polyCharpoly_map_eq_charpoly`: the evaluation of `polyCharpoly` on elements `x` of `L`
  is the characteristic polynomial of `φ x`.
* `LinearMap.polyCharpoly_coeff_isHomogeneous`: the coefficients of `polyCharpoly`
  are homogeneous polynomials in the parameters.
* `LinearMap.nilRank`: the smallest index at which `polyCharpoly` has a non-zero coefficient,
  which is independent of the choice of basis for `L`.
* `LinearMap.IsNilRegular`: an element `x` of `L` is *nil-regular* with respect to `φ`
  if the `n`-th coefficient of the characteristic polynomial of `φ x` is non-zero,
  where `n` denotes the nil-rank of `φ`.

## Implementation details

We show that `LinearMap.polyCharpoly` does not depend on the choice of basis of the target module.
This is done via `LinearMap.polyCharpoly_eq_polyCharpolyAux`
and `LinearMap.polyCharpolyAux_basisIndep`.
The latter is proven by considering
the base change of the `R`-linear map `φ : L →ₗ[R] End R M`
to the multivariate polynomial ring `MvPolynomial ι R`,
and showing that `polyCharpolyAux φ` is equal to the characteristic polynomial of this base change.
The proof concludes because characteristic polynomials are independent of the chosen basis.

## References

* [barnes1967]: "On Cartan subalgebras of Lie algebras" by D.W. Barnes.

-/

@[expose] public section

open Module MvPolynomial
open scoped Matrix

namespace Matrix

variable {m n o R S : Type*}
variable [Fintype n] [Fintype o] [CommSemiring R] [CommSemiring S]

/-- Let `M` be an `(m × n)`-matrix over `R`.
Then `Matrix.toMvPolynomial M` is the family (indexed by `i : m`)
of multivariate polynomials in `n` variables over `R` that evaluates on `c : n → R`
to the dot product of the `i`-th row of `M` with `c`:
`Matrix.toMvPolynomial M i` is the sum of the monomials `C (M i j) * X j`. -/
noncomputable
def toMvPolynomial (M : Matrix m n R) (i : m) : MvPolynomial n R :=
  ∑ j, monomial (.single j 1) (M i j)

/--
@isnad1 id=eq.0h6v.s6.fc11679b7520 from=seed src=0 shape=74d222ef vocab=c0c6d573
-/
lemma toMvPolynomial_eval_eq_apply (M : Matrix m n R) (i : m) (c : n → R) :
    eval c (M.toMvPolynomial i) = (M *ᵥ c) i := by
  simp only [toMvPolynomial, map_sum, eval_monomial, pow_zero, Finsupp.prod_single_index, pow_one,
    mulVec, dotProduct]

/--
@isnad1 id=eq.0h7v.s7.86ed4f01c1c0 from=seed src=0 shape=a874a9cf vocab=edf3b7ae
-/
lemma toMvPolynomial_map (f : R →+* S) (M : Matrix m n R) (i : m) :
    (M.map f).toMvPolynomial i = MvPolynomial.map f (M.toMvPolynomial i) := by
  simp only [toMvPolynomial, map_apply, map_sum, map_monomial]

/--
@isnad1 id=ishomoge.0h5v.s5.53675cead848 from=seed src=0 shape=7f96bc2d vocab=94f35a83
-/
lemma toMvPolynomial_isHomogeneous (M : Matrix m n R) (i : m) :
    (M.toMvPolynomial i).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  rintro j -
  apply MvPolynomial.isHomogeneous_monomial _ _
  simp

/--
@isnad1 id=le.0h5v.s5.6d0729f65866 from=seed src=0 shape=4ea1c77a vocab=5a6fb035
-/
lemma toMvPolynomial_totalDegree_le (M : Matrix m n R) (i : m) :
    (M.toMvPolynomial i).totalDegree ≤ 1 := by
  apply (toMvPolynomial_isHomogeneous _ _).totalDegree_le

/--
@isnad1 id=eq.0h5v.s6.c879f27d78f8 from=seed src=0 shape=0573d671 vocab=ae2cbe5b
-/
@[simp]
lemma toMvPolynomial_constantCoeff (M : Matrix m n R) (i : m) :
    constantCoeff (M.toMvPolynomial i) = 0 := by
  simp only [toMvPolynomial, ← C_mul_X_eq_monomial, map_sum, map_mul, constantCoeff_X,
    mul_zero, Finset.sum_const_zero]

/--
@isnad1 id=eq.0h3v.s6.be00c7504b85 from=seed src=0 shape=203dff6a vocab=6bd18f61
-/
@[simp]
lemma toMvPolynomial_zero : (0 : Matrix m n R).toMvPolynomial = 0 := by
  ext; simp only [toMvPolynomial, zero_apply, map_zero, Finset.sum_const_zero, Pi.zero_apply]

/--
@isnad1 id=eq.0h2v.s5.fd617bd155f3 from=seed src=0 shape=a4f38919 vocab=efb4c07b
-/
@[simp]
lemma toMvPolynomial_one [DecidableEq n] : (1 : Matrix n n R).toMvPolynomial = X := by
  ext i : 1
  rw [toMvPolynomial, Finset.sum_eq_single i]
  · simp only [one_apply_eq, ← C_mul_X_eq_monomial, C_1, one_mul]
  · rintro j - hj
    simp only [one_apply_ne hj.symm, map_zero]
  · grind

/--
@isnad1 id=eq.0h5v.s7.8a673688ea0d from=seed src=0 shape=3c99f737 vocab=0bf31003
-/
lemma toMvPolynomial_add (M N : Matrix m n R) :
    (M + N).toMvPolynomial = M.toMvPolynomial + N.toMvPolynomial := by
  ext i : 1
  simp only [toMvPolynomial, add_apply, map_add, Finset.sum_add_distrib, Pi.add_apply]

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h7v.s8.f6160d2d22c9 from=seed src=0 shape=9868276c vocab=c5d9df51
-/
lemma toMvPolynomial_mul (M : Matrix m n R) (N : Matrix n o R) (i : m) :
    (M * N).toMvPolynomial i = bind₁ N.toMvPolynomial (M.toMvPolynomial i) := by
  simp only [toMvPolynomial, mul_apply, map_sum, Finset.sum_comm (γ := o), bind₁, aeval,
    AlgHom.coe_mk, coe_eval₂Hom, eval₂_monomial, algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, C_apply, pow_zero, Finsupp.prod_single_index, pow_one, Finset.mul_sum,
    monomial_mul_monomial, zero_add]

end Matrix

namespace LinearMap

open MvPolynomial

section

variable {R M₁ M₂ ι₁ ι₂ : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂]
variable [Module R M₁] [Module R M₂]
variable [Fintype ι₁] [Finite ι₂]
variable [DecidableEq ι₁]
variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂)

/-- Let `f : M₁ →ₗ[R] M₂` be an `R`-linear map
between modules `M₁` and `M₂` with bases `b₁` and `b₂` respectively.
Then `LinearMap.toMvPolynomial b₁ b₂ f` is the family of multivariate polynomials over `R`
that evaluates on an element `x` of `M₁` (represented on the basis `b₁`)
to the element `f x` of `M₂` (represented on the basis `b₂`). -/
noncomputable
def toMvPolynomial (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    MvPolynomial ι₁ R :=
  (toMatrix b₁ b₂ f).toMvPolynomial i

/--
@isnad1 id=eq.0h10v.s10.6b19251d665c from=seed src=0 shape=d9763949 vocab=25f7565a
-/
lemma toMvPolynomial_eval_eq_apply (f : M₁ →ₗ[R] M₂) (i : ι₂) (c : ι₁ →₀ R) :
    eval c (f.toMvPolynomial b₁ b₂ i) = b₂.repr (f (b₁.repr.symm c)) i := by
  rw [toMvPolynomial, Matrix.toMvPolynomial_eval_eq_apply,
    ← LinearMap.toMatrix_mulVec_repr b₁ b₂, LinearEquiv.apply_symm_apply]

open Algebra.TensorProduct in
/--
@isnad1 id=eq.0h10v.s9.4fe47d528a8b from=seed src=0 shape=4c2cd329 vocab=1fffb041
-/
lemma toMvPolynomial_baseChange (f : M₁ →ₗ[R] M₂) (i : ι₂) (A : Type*) [CommRing A] [Algebra R A] :
    (f.baseChange A).toMvPolynomial (basis A b₁) (basis A b₂) i =
      MvPolynomial.map (algebraMap R A) (f.toMvPolynomial b₁ b₂ i) := by
  simp only [toMvPolynomial, toMatrix_baseChange, Matrix.toMvPolynomial_map]

/--
@isnad1 id=ishomoge.0h9v.s7.4aa886187868 from=seed src=0 shape=c0b8d11f vocab=b0b7db97
-/
lemma toMvPolynomial_isHomogeneous (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    (f.toMvPolynomial b₁ b₂ i).IsHomogeneous 1 :=
  Matrix.toMvPolynomial_isHomogeneous _ _

/--
@isnad1 id=le.0h9v.s7.1c7642ea4411 from=seed src=0 shape=da8fd3a8 vocab=c7f315dd
-/
lemma toMvPolynomial_totalDegree_le (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    (f.toMvPolynomial b₁ b₂ i).totalDegree ≤ 1 :=
  Matrix.toMvPolynomial_totalDegree_le _ _

/--
@isnad1 id=eq.0h9v.s7.c3e75c71b30a from=seed src=0 shape=5210d2f0 vocab=efd7c2f4
-/
@[simp]
lemma toMvPolynomial_constantCoeff (f : M₁ →ₗ[R] M₂) (i : ι₂) :
    constantCoeff (f.toMvPolynomial b₁ b₂ i) = 0 :=
  Matrix.toMvPolynomial_constantCoeff _ _

/--
@isnad1 id=eq.0h7v.s8.ea15a96cce4b from=seed src=0 shape=e8f2a12d vocab=9c43e68d
-/
@[simp]
lemma toMvPolynomial_zero : (0 : M₁ →ₗ[R] M₂).toMvPolynomial b₁ b₂ = 0 := by
  unfold toMvPolynomial; simp only [map_zero, Matrix.toMvPolynomial_zero]

/--
@isnad1 id=eq.0h4v.s6.a4a60e991de8 from=seed src=0 shape=8a39f2d4 vocab=bf84b8e8
-/
@[simp]
lemma toMvPolynomial_id : (id : M₁ →ₗ[R] M₁).toMvPolynomial b₁ b₁ = X := by
  unfold toMvPolynomial; simp only [toMatrix_id, Matrix.toMvPolynomial_one]

/--
@isnad1 id=eq.0h9v.s8.edb0cd8cb810 from=seed src=0 shape=f581c76d vocab=2331280a
-/
lemma toMvPolynomial_add (f g : M₁ →ₗ[R] M₂) :
    (f + g).toMvPolynomial b₁ b₂ = f.toMvPolynomial b₁ b₂ + g.toMvPolynomial b₁ b₂ := by
  unfold toMvPolynomial; simp only [map_add, Matrix.toMvPolynomial_add]

end

variable {R M₁ M₂ M₃ ι₁ ι₂ ι₃ : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M₁] [Module R M₂] [Module R M₃]
variable [Fintype ι₁] [Fintype ι₂] [Finite ι₃]
variable [DecidableEq ι₁] [DecidableEq ι₂]
variable (b₁ : Basis ι₁ R M₁) (b₂ : Basis ι₂ R M₂) (b₃ : Basis ι₃ R M₃)

/--
@isnad1 id=eq.0h13v.s9.2cf129a0afcd from=seed src=0 shape=b70594a7 vocab=d0c7626f
-/
lemma toMvPolynomial_comp (g : M₂ →ₗ[R] M₃) (f : M₁ →ₗ[R] M₂) (i : ι₃) :
    (g ∘ₗ f).toMvPolynomial b₁ b₃ i =
      bind₁ (f.toMvPolynomial b₁ b₂) (g.toMvPolynomial b₂ b₃ i) := by
  simp only [toMvPolynomial, toMatrix_comp b₁ b₂ b₃, Matrix.toMvPolynomial_mul]
  rfl

end LinearMap

variable {R L M n ι ι' ιM : Type*}
variable [CommRing R] [AddCommGroup L] [Module R L] [AddCommGroup M] [Module R M]
variable (φ : L →ₗ[R] Module.End R M)
variable [Fintype ι] [Fintype ι'] [Fintype ιM] [DecidableEq ι] [DecidableEq ι']

namespace LinearMap

section aux

variable [DecidableEq ιM] (b : Basis ι R L) (bₘ : Basis ιM R M)

open Matrix

/-- (Implementation detail, see `LinearMap.polyCharpoly`.)

Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear map.
Let `b` be a basis of `L` and `bₘ` a basis of `M`.
Then `LinearMap.polyCharpolyAux φ b bₘ` is the polynomial that evaluates on elements `x` of `L`
to the characteristic polynomial of `φ x` acting on `M`.

This definition does not depend on the choice of `bₘ`
(see `LinearMap.polyCharpolyAux_basisIndep`). -/
noncomputable
def polyCharpolyAux : Polynomial (MvPolynomial ι R) :=
  (charpoly.univ R ιM).map <| MvPolynomial.bind₁ (φ.toMvPolynomial b bₘ.end)

set_option backward.defeqAttrib.useBackward true in
open Algebra.TensorProduct MvPolynomial in
/--
@isnad1 id=eq.0h9v.s10.00ad06824575 from=seed src=0 shape=0e244cef vocab=bfb3f045
-/
lemma polyCharpolyAux_baseChange (A : Type*) [CommRing A] [Algebra R A] :
    polyCharpolyAux (tensorProduct _ _ _ _ ∘ₗ φ.baseChange A) (basis A b) (basis A bₘ) =
      (polyCharpolyAux φ b bₘ).map (MvPolynomial.map (algebraMap R A)) := by
  simp only [polyCharpolyAux]
  rw [← charpoly.univ_map_map _ (algebraMap R A)]
  simp only [Polynomial.map_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_C, bind₁_C_right]
  · rintro ij
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, map_X, bind₁_X_right]
    rw [toMvPolynomial_comp _ (basis A (Basis.end bₘ)), ← toMvPolynomial_baseChange]
    suffices toMvPolynomial (M₂ := (Module.End A (TensorProduct R A M)))
        (basis A bₘ.end) (basis A bₘ).end (tensorProduct R A M M) ij = X ij by
      rw [this, bind₁_X_right]
    simp only [toMvPolynomial, Matrix.toMvPolynomial]
    suffices ∀ kl,
        (toMatrix (basis A bₘ.end) (basis A bₘ).end) (tensorProduct R A M M) ij kl =
        if kl = ij then 1 else 0 by
      rw [Finset.sum_eq_single ij]
      · rw [this, ite_eq_left rfl, X]
      · rintro kl - H
        rw [this, ite_eq_right H, map_zero]
      · grind
    intro kl
    rw [toMatrix_apply, tensorProduct, TensorProduct.AlgebraTensorModule.lift_apply,
      basis_apply, TensorProduct.lift.tmul, coe_restrictScalars]
    dsimp only [coe_mk, AddHom.coe_mk, smul_apply, baseChangeHom_apply]
    rw [one_smul, Basis.baseChange_end, Basis.repr_self_apply]

open LinearMap in
/--
@isnad1 id=eq.0h9v.s10.fcdbfd92d19f from=seed src=0 shape=a0cdb1f1 vocab=3b409d04
-/
lemma polyCharpolyAux_map_eq_toMatrix_charpoly (x : L) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval (b.repr x)) =
      (toMatrix bₘ bₘ (φ x)).charpoly := by
  rw [polyCharpolyAux, Polynomial.map_map, ← MvPolynomial.eval₂Hom_C_eq_bind₁,
    MvPolynomial.comp_eval₂Hom, charpoly.univ_map_eval₂Hom]
  congr
  ext
  rw [of_apply, Function.curry_apply, toMvPolynomial_eval_eq_apply, LinearEquiv.symm_apply_apply]
  rfl

open LinearMap in
/--
@isnad1 id=eq.0h10v.s10.2874e0d7c953 from=seed src=0 shape=e7737e1d vocab=cee51f87
-/
lemma polyCharpolyAux_eval_eq_toMatrix_charpoly_coeff (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((polyCharpolyAux φ b bₘ).coeff i) =
      (toMatrix bₘ bₘ (φ x)).charpoly.coeff i := by
  simp [← polyCharpolyAux_map_eq_toMatrix_charpoly φ b bₘ x]

/--
@isnad1 id=eq.0h9v.s9.4f3220e098a5 from=seed src=0 shape=2912e9b3 vocab=bcece7a7
-/
@[simp]
lemma polyCharpolyAux_map_eq_charpoly [Module.Finite R M] [Module.Free R M]
    (x : L) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  nontriviality R
  rw [polyCharpolyAux_map_eq_toMatrix_charpoly, LinearMap.charpoly_toMatrix]

/--
@isnad1 id=eq.0h10v.s9.11709240a5b5 from=seed src=0 shape=04ff06cf vocab=7885674f
-/
@[simp]
lemma polyCharpolyAux_coeff_eval [Module.Finite R M] [Module.Free R M] (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((polyCharpolyAux φ b bₘ).coeff i) = (φ x).charpoly.coeff i := by
  nontriviality R
  rw [← polyCharpolyAux_map_eq_charpoly φ b bₘ x, Polynomial.coeff_map]

set_option backward.isDefEq.respectTransparency.types false in
/--
@isnad1 id=eq.0h9v.s10.6ff9db123c5a from=seed src=0 shape=6342e2c9 vocab=cf96317a
-/
lemma polyCharpolyAux_map_eval [Module.Finite R M] [Module.Free R M]
    (x : ι → R) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.eval x) =
      (φ (b.repr.symm (Finsupp.equivFunOnFinite.symm x))).charpoly := by
  simp only [← polyCharpolyAux_map_eq_charpoly φ b bₘ, LinearEquiv.apply_symm_apply,
    Finsupp.equivFunOnFinite, Equiv.coe_fn_symm_mk, Finsupp.coe_mk]

open Algebra.TensorProduct TensorProduct in
/--
@isnad1 id=eq.0h10v.s12.e1b3e2d19ba7 from=seed src=0 shape=b2b70945 vocab=db5062b7
-/
lemma polyCharpolyAux_map_aeval
    (A : Type*) [CommRing A] [Algebra R A] [Module.Finite A (A ⊗[R] M)] [Module.Free A (A ⊗[R] M)]
    (x : ι → A) :
    (polyCharpolyAux φ b bₘ).map (MvPolynomial.aeval x).toRingHom =
      LinearMap.charpoly ((tensorProduct R A M M).comp (baseChange A φ)
        ((basis A b).repr.symm (Finsupp.equivFunOnFinite.symm x))) := by
  rw [← polyCharpolyAux_map_eval (tensorProduct R A M M ∘ₗ baseChange A φ) _ (basis A bₘ),
    polyCharpolyAux_baseChange, Polynomial.map_map]
  congr
  exact DFunLike.ext _ _ fun f ↦ (MvPolynomial.eval_map (algebraMap R A) x f).symm

open Algebra.TensorProduct MvPolynomial in
/-- `LinearMap.polyCharpolyAux` is independent of the choice of basis of the target module.

Proof strategy:
1. Rewrite `polyCharpolyAux` as the (honest, ordinary) characteristic polynomial
   of the base change of `φ` to the multivariate polynomial ring `MvPolynomial ι R`.
2. Use that the characteristic polynomial of a linear map is independent of the choice of basis.
   This independence result is used transitively via
   `LinearMap.polyCharpolyAux_map_aeval` and `LinearMap.polyCharpolyAux_map_eq_charpoly`.
@isnad1 id=eq.0h10v.s8.95eaf9e0f25d from=seed src=0 shape=e2466645 vocab=2696073d
-/
lemma polyCharpolyAux_basisIndep {ιM' : Type*} [Fintype ιM'] [DecidableEq ιM']
    (bₘ' : Basis ιM' R M) :
    polyCharpolyAux φ b bₘ = polyCharpolyAux φ b bₘ' := by
  let f : Polynomial (MvPolynomial ι R) → Polynomial (MvPolynomial ι R) :=
    Polynomial.map (MvPolynomial.aeval X).toRingHom
  have hf : Function.Injective f := by
    simp only [f, aeval_X_left, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom]
    exact Polynomial.map_injective (RingHom.id _) Function.injective_id
  apply hf
  let _h1 : Module.Finite (MvPolynomial ι R) (TensorProduct R (MvPolynomial ι R) M) :=
    Module.Finite.of_basis (basis (MvPolynomial ι R) bₘ)
  let _h2 : Module.Free (MvPolynomial ι R) (TensorProduct R (MvPolynomial ι R) M) :=
    Module.Free.of_basis (basis (MvPolynomial ι R) bₘ)
  simp only [f, polyCharpolyAux_map_aeval, polyCharpolyAux_map_aeval]

end aux

open Module Matrix

variable [Module.Free R M] [Module.Finite R M] (b : Basis ι R L)

/-- Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms.
Let `b` be a basis of `L` and `bₘ` a basis of `M`.
Then `LinearMap.polyCharpoly φ b` is the polynomial that evaluates on elements `x` of `L`
to the characteristic polynomial of `φ x` acting on `M`. -/
noncomputable
def polyCharpoly : Polynomial (MvPolynomial ι R) :=
  φ.polyCharpolyAux b (Module.Free.chooseBasis R M)

/--
@isnad1 id=eq.0h8v.s9.3caf6e2fcf1a from=seed src=0 shape=f4643659 vocab=4597daa2
-/
lemma polyCharpoly_eq_of_basis [DecidableEq ιM] (bₘ : Basis ιM R M) :
    polyCharpoly φ b =
    (charpoly.univ R ιM).map (MvPolynomial.bind₁ (φ.toMvPolynomial b bₘ.end)) := by
  rw [polyCharpoly, φ.polyCharpolyAux_basisIndep b (Module.Free.chooseBasis R M) bₘ,
    polyCharpolyAux]

/--
@isnad1 id=monic.0h6v.s7.83de57a0485d from=seed src=0 shape=300ae026 vocab=0afbb78e
-/
lemma polyCharpoly_monic : (polyCharpoly φ b).Monic :=
  (charpoly.univ_monic R _).map _

/--
@isnad1 id=ne.0h6v.s8.2251f9f70989 from=seed src=0 shape=76e91c21 vocab=44f0af4d
-/
lemma polyCharpoly_ne_zero [Nontrivial R] : (polyCharpoly φ b) ≠ 0 :=
  (polyCharpoly_monic _ _).ne_zero

/--
@isnad1 id=eq.0h6v.s8.3022a30555d1 from=seed src=0 shape=b16facc0 vocab=2940239f
-/
@[simp]
lemma polyCharpoly_natDegree [Nontrivial R] :
    (polyCharpoly φ b).natDegree = finrank R M := by
  rw [polyCharpoly, polyCharpolyAux, (charpoly.univ_monic _ _).natDegree_map,
    charpoly.univ_natDegree, finrank_eq_card_chooseBasisIndex]

/--
@isnad1 id=ishomoge.1h8v.s8.e5eee34bfaba from=seed src=0 shape=57f8653d vocab=00ceb633
-/
lemma polyCharpoly_coeff_isHomogeneous (i j : ℕ) (hij : i + j = finrank R M) [Nontrivial R] :
    ((polyCharpoly φ b).coeff i).IsHomogeneous j := by
  rw [finrank_eq_card_chooseBasisIndex] at hij
  rw [polyCharpoly, polyCharpolyAux, Polynomial.coeff_map, ← one_mul j]
  apply (charpoly.univ_coeff_isHomogeneous _ _ _ _ hij).eval₂
  · exact fun r ↦ MvPolynomial.isHomogeneous_C _ _
  · exact LinearMap.toMvPolynomial_isHomogeneous _ _ _

open Algebra.TensorProduct MvPolynomial in
/--
@isnad1 id=eq.0h7v.s10.d708346bb040 from=seed src=0 shape=7a40c7fd vocab=4e6180ec
-/
lemma polyCharpoly_baseChange (A : Type*) [CommRing A] [Algebra R A] :
    polyCharpoly (tensorProduct _ _ _ _ ∘ₗ φ.baseChange A) (basis A b) =
      (polyCharpoly φ b).map (MvPolynomial.map (algebraMap R A)) := by
  unfold polyCharpoly
  rw [← φ.polyCharpolyAux_baseChange]
  apply polyCharpolyAux_basisIndep

/--
@isnad1 id=eq.0h7v.s9.c7cb033b3db2 from=seed src=0 shape=464c27cf vocab=e9ea84ff
-/
@[simp]
lemma polyCharpoly_map_eq_charpoly (x : L) :
    (polyCharpoly φ b).map (MvPolynomial.eval (b.repr x)) = (φ x).charpoly := by
  rw [polyCharpoly, polyCharpolyAux_map_eq_charpoly]

/--
@isnad1 id=eq.0h8v.s9.082d9fb5426a from=seed src=0 shape=d5c6c6e0 vocab=4713e844
-/
@[simp]
lemma polyCharpoly_coeff_eval (x : L) (i : ℕ) :
    MvPolynomial.eval (b.repr x) ((polyCharpoly φ b).coeff i) = (φ x).charpoly.coeff i := by
  rw [polyCharpoly, polyCharpolyAux_coeff_eval]

/--
@isnad1 id=eq.1h9v.s8.cf186667002f from=seed src=0 shape=df017b17 vocab=ebdc8b17
-/
lemma polyCharpoly_coeff_eq_zero_of_basis (b : Basis ι R L) (b' : Basis ι' R L) (k : ℕ)
    (H : (polyCharpoly φ b).coeff k = 0) :
    (polyCharpoly φ b').coeff k = 0 := by
  rw [polyCharpoly, polyCharpolyAux, Polynomial.coeff_map] at H ⊢
  set B := (Module.Free.chooseBasis R M).end
  set g := toMvPolynomial b' b LinearMap.id
  apply_fun (MvPolynomial.bind₁ g) at H
  have : toMvPolynomial b' B φ = fun i ↦ (MvPolynomial.bind₁ g) (toMvPolynomial b B φ i) :=
    funext <| toMvPolynomial_comp b' b B φ LinearMap.id
  rwa [map_zero, RingHom.coe_coe, MvPolynomial.bind₁_bind₁, ← this] at H

/--
@isnad1 id=iff.0h9v.s8.f803a9963f6c from=seed src=0 shape=60935f9d vocab=ebdc8b17
-/
lemma polyCharpoly_coeff_eq_zero_iff_of_basis (b : Basis ι R L) (b' : Basis ι' R L) (k : ℕ) :
    (polyCharpoly φ b).coeff k = 0 ↔ (polyCharpoly φ b').coeff k = 0 := by
  constructor <;> apply polyCharpoly_coeff_eq_zero_of_basis

section aux

/-- (Implementation detail, see `LinearMap.nilRank`.)

Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms.
Then `LinearMap.nilRankAux φ b` is the smallest index
at which `LinearMap.polyCharpoly φ b` has a non-zero coefficient.

This number does not depend on the choice of `b`, see `nilRankAux_basis_indep`. -/
noncomputable
def nilRankAux (φ : L →ₗ[R] Module.End R M) (b : Basis ι R L) : ℕ :=
  (polyCharpoly φ b).natTrailingDegree

/--
@isnad1 id=ne.0h6v.s8.1712cc7fac4e from=seed src=0 shape=847ac6be vocab=188bbddd
-/
lemma polyCharpoly_coeff_nilRankAux_ne_zero [Nontrivial R] :
    (polyCharpoly φ b).coeff (nilRankAux φ b) ≠ 0 := by
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
  apply polyCharpoly_ne_zero

/--
@isnad1 id=le.0h8v.s8.c87f9c9a7d67 from=seed src=0 shape=851e0be3 vocab=a2667613
-/
lemma nilRankAux_le [Nontrivial R] (b : Basis ι R L) (b' : Basis ι' R L) :
    nilRankAux φ b ≤ nilRankAux φ b' := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [Ne, (polyCharpoly_coeff_eq_zero_iff_of_basis φ b b' _).not]
  apply polyCharpoly_coeff_nilRankAux_ne_zero

/--
@isnad1 id=eq.0h8v.s8.222baafa970c from=seed src=0 shape=3fdc1042 vocab=d25f641d
-/
lemma nilRankAux_basis_indep [Nontrivial R] (b : Basis ι R L) (b' : Basis ι' R L) :
    nilRankAux φ b = (polyCharpoly φ b').natTrailingDegree := by
  apply le_antisymm <;> apply nilRankAux_le

end aux

variable [Module.Finite R L] [Module.Free R L]

/-- Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms.
Then `LinearMap.nilRank φ b` is the smallest index
at which `LinearMap.polyCharpoly φ b` has a non-zero coefficient.

This number does not depend on the choice of `b`,
see `LinearMap.nilRank_eq_polyCharpoly_natTrailingDegree`. -/
noncomputable
def nilRank (φ : L →ₗ[R] Module.End R M) : ℕ :=
  nilRankAux φ (Module.Free.chooseBasis R L)

section
variable [Nontrivial R]

/--
@isnad1 id=eq.0h6v.s8.440f713c727d from=seed src=0 shape=7c49043d vocab=c54e2c5a
-/
lemma nilRank_eq_polyCharpoly_natTrailingDegree (b : Basis ι R L) :
    nilRank φ = (polyCharpoly φ b).natTrailingDegree := by
  apply nilRankAux_basis_indep

/--
@isnad1 id=ne.0h6v.s8.0ab54ecff571 from=seed src=0 shape=e25608d2 vocab=d3b5d0d0
-/
lemma polyCharpoly_coeff_nilRank_ne_zero :
    (polyCharpoly φ b).coeff (nilRank φ) ≠ 0 := by
  rw [nilRank_eq_polyCharpoly_natTrailingDegree _ b]
  apply polyCharpoly_coeff_nilRankAux_ne_zero

open Module Module.Free

/--
@isnad1 id=le.0h6v.s7.dc014440c872 from=seed src=0 shape=22036cea vocab=d7433406
-/
lemma nilRank_le_card {ι : Type*} [Fintype ι] (b : Basis ι R M) : nilRank φ ≤ Fintype.card ι := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  rw [← Module.finrank_eq_card_basis b, ← polyCharpoly_natDegree φ (chooseBasis R L),
    Polynomial.coeff_natDegree, (polyCharpoly_monic _ _).leadingCoeff]
  apply one_ne_zero

/--
@isnad1 id=le.0h4v.s7.e75772d7412e from=seed src=0 shape=1c983bc3 vocab=0a095b17
-/
lemma nilRank_le_finrank : nilRank φ ≤ finrank R M := by
  simpa only [finrank_eq_card_chooseBasisIndex R M] using nilRank_le_card φ (chooseBasis R M)

/--
@isnad1 id=le.0h5v.s8.13def7fc3ec9 from=seed src=0 shape=0f8efb3b vocab=34bbb5c9
-/
lemma nilRank_le_natTrailingDegree_charpoly (x : L) :
    nilRank φ ≤ (φ x).charpoly.natTrailingDegree := by
  apply Polynomial.natTrailingDegree_le_of_ne_zero
  intro h
  apply_fun (MvPolynomial.eval ((chooseBasis R L).repr x)) at h
  rw [polyCharpoly_coeff_eval, map_zero] at h
  apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr _ h
  apply (LinearMap.charpoly_monic _).ne_zero

end

/-- Let `L` and `M` be finite free modules over `R`,
and let `φ : L →ₗ[R] Module.End R M` be a linear family of endomorphisms,
and denote `n := nilRank φ`.

An element `x : L` is *nil-regular* with respect to `φ`
if the `n`-th coefficient of the characteristic polynomial of `φ x` is non-zero. -/
def IsNilRegular (x : L) : Prop :=
  Polynomial.coeff (φ x).charpoly (nilRank φ) ≠ 0

variable (x : L)

/--
@isnad1 id=iff.0h5v.s8.e1147581dcdc from=seed src=0 shape=fb3f44a4 vocab=3dcd8b28
-/
lemma isNilRegular_def :
    IsNilRegular φ x ↔ (Polynomial.coeff (φ x).charpoly (nilRank φ) ≠ 0) := Iff.rfl

/--
@isnad1 id=iff.0h7v.s9.ba433eac8878 from=seed src=0 shape=d7f87fee vocab=ec8fae19
-/
lemma isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero :
    IsNilRegular φ x ↔
    MvPolynomial.eval (b.repr x)
      ((polyCharpoly φ b).coeff (nilRank φ)) ≠ 0 := by
  rw [IsNilRegular, polyCharpoly_coeff_eval]

/--
@isnad1 id=iff.0h5v.s8.3474f7535194 from=seed src=0 shape=cc4007be vocab=0c5e9a1c
-/
lemma isNilRegular_iff_natTrailingDegree_charpoly_eq_nilRank [Nontrivial R] :
    IsNilRegular φ x ↔ (φ x).charpoly.natTrailingDegree = nilRank φ := by
  rw [isNilRegular_def]
  constructor
  · intro h
    exact le_antisymm
      (Polynomial.natTrailingDegree_le_of_ne_zero h)
      (nilRank_le_natTrailingDegree_charpoly φ x)
  · intro h
    rw [← h]
    apply Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr
    apply (LinearMap.charpoly_monic _).ne_zero

section IsDomain

variable [IsDomain R]

open Cardinal Module MvPolynomial Module.Free in
/--
@isnad1 id=ex.1h4v.s7.0b54c8b3f479 from=seed src=0 shape=bb26ae40 vocab=cd619e02
-/
lemma exists_isNilRegular_of_finrank_le_card (h : finrank R M ≤ #R) :
    ∃ x : L, IsNilRegular φ x := by
  let b := chooseBasis R L
  let bₘ := chooseBasis R M
  let n := Fintype.card (ChooseBasisIndex R M)
  have aux :
    ((polyCharpoly φ b).coeff (nilRank φ)).IsHomogeneous (n - nilRank φ) :=
    polyCharpoly_coeff_isHomogeneous _ b (nilRank φ) (n - nilRank φ)
      (by simp [n, nilRank_le_card φ bₘ, finrank_eq_card_chooseBasisIndex])
  obtain ⟨x, hx⟩ : ∃ r, eval r ((polyCharpoly _ b).coeff (nilRank φ)) ≠ 0 := by
    by_contra! h₀
    apply polyCharpoly_coeff_nilRank_ne_zero φ b
    apply aux.eq_zero_of_forall_eval_eq_zero_of_le_card h₀ (le_trans _ h)
    simp only [n, finrank_eq_card_chooseBasisIndex, Nat.cast_le, Nat.sub_le]
  let c := Finsupp.equivFunOnFinite.symm x
  use b.repr.symm c
  rwa [isNilRegular_iff_coeff_polyCharpoly_nilRank_ne_zero _ b, LinearEquiv.apply_symm_apply]

/--
@isnad1 id=ex.0h4v.s7.6fdc9c128163 from=seed src=0 shape=ddc356e8 vocab=71057aca
-/
lemma exists_isNilRegular [Infinite R] : ∃ x : L, IsNilRegular φ x := by
  apply exists_isNilRegular_of_finrank_le_card
  exact Cardinal.natCast_le_aleph0.trans <| Cardinal.infinite_iff.mp ‹Infinite R›

end IsDomain

end LinearMap
