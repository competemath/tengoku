import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Scalar.TestCertificate.Defs
import Tengoku.Seed.LinearAlgebra.Dual.Lemmas
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base change of coordinate maps along a field extension

For a field extension `K / F` and finite index types, an `F`-linear map `g : F^n → F^m` has a
base change `bcMap g : K^n → K^m`, the `K`-linear map with the same matrix, and an `F`-linear
form `ℓ` on `F^n` has a base change `bcForm ℓ` on `K^n`. Base change commutes with the
inclusion `F^n → K^n`, and a form vanishing on the kernel of another still does so after base
change. These facts are used to transfer the tests of the family (F.2) from `F` to `K`.
-/

namespace AlternatingAnalytic.TestCertificate

open Module

variable {F K : Type*} [Field F] [Field K] [Algebra F K]
variable {m n : Type*}

/-- The coordinatewise inclusion `F^n → K^n`.-/
def incl : (n → F) →ₗ[F] (n → K) := (Algebra.linearMap F K).compLeft n

@[simp] theorem incl_apply (y : n → F) (i : n) : (incl y : n → K) i = algebraMap F K (y i) := rfl

variable [Fintype n] [DecidableEq n]

/-- The base change to `K` of an `F`-linear map `F^n → F^m`: the `K`-linear map with the same
matrix.-/
noncomputable def bcMap (g : (n → F) →ₗ[F] (m → F)) : (n → K) →ₗ[K] (m → K) :=
  Matrix.mulVecLin ((LinearMap.toMatrix' g).map (algebraMap F K))

/-- The base change to `K` of an `F`-linear form on `F^n`, as a function on `K^n`.-/
noncomputable def bcForm (ℓ : (n → F) →ₗ[F] F) (x : n → K) : K :=
  ∑ j, algebraMap F K (ℓ (Pi.single j 1)) * x j

theorem bcMap_apply (g : (n → F) →ₗ[F] (m → F)) (x : n → K) (i : m) :
    bcMap g x i = bcForm ((LinearMap.proj i).comp g) x := by
  simp [bcMap, bcForm, Matrix.mulVec, dotProduct, LinearMap.toMatrix'_apply]

theorem bcForm_smul (c : F) (ℓ : (n → F) →ₗ[F] F) (x : n → K) :
    bcForm (c • ℓ) x = algebraMap F K c * bcForm ℓ x := by
  simp [bcForm, Finset.mul_sum, mul_assoc]

theorem bcForm_zero (x : n → K) : bcForm (0 : (n → F) →ₗ[F] F) x = 0 := by
  simp [bcForm]

theorem bcForm_add (ℓ ℓ' : (n → F) →ₗ[F] F) (x : n → K) :
    bcForm (ℓ + ℓ') x = bcForm ℓ x + bcForm ℓ' x := by
  simp [bcForm, add_mul, Finset.sum_add_distrib]

theorem bcForm_sub (ℓ ℓ' : (n → F) →ₗ[F] F) (x : n → K) :
    bcForm (ℓ - ℓ') x = bcForm ℓ x - bcForm ℓ' x := by
  simp [bcForm, sub_mul, Finset.sum_sub_distrib]

theorem bcForm_proj (a : n) (x : n → K) :
    bcForm (LinearMap.proj (R := F) (φ := fun _ => F) a) x = x a := by
  simp [bcForm, Pi.single_apply]

theorem bcForm_incl (ℓ : (n → F) →ₗ[F] F) (y : n → F) :
    bcForm ℓ (incl y) = algebraMap F K (ℓ y) := by
  conv_rhs => rw [pi_eq_sum_univ y, map_sum, map_sum]
  simp only [bcForm, incl_apply, map_smul, smul_eq_mul, map_mul, mul_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 3
  ext i
  simp [Pi.single_apply, eq_comm]

theorem bcMap_incl [Fintype m] (g : (n → F) →ₗ[F] (m → F)) (y : n → F) :
    bcMap g (incl y) = (incl (g y) : m → K) := by
  ext i
  rw [bcMap_apply, bcForm_incl]
  rfl

/-- Base change of `F`-linear maps, as an `F`-linear map.-/
noncomputable def bcMapₗ : ((n → F) →ₗ[F] (m → F)) →ₗ[F] ((n → K) →ₗ[K] (m → K)) where
  toFun := bcMap
  map_add' g h := by
    refine LinearMap.ext fun x => funext fun i => ?_
    simp only [LinearMap.add_apply, Pi.add_apply, bcMap_apply]
    rw [LinearMap.comp_add, bcForm_add]
  map_smul' c g := by
    refine LinearMap.ext fun x => funext fun i => ?_
    simp only [LinearMap.smul_apply, Pi.smul_apply, bcMap_apply, RingHom.id_apply]
    rw [LinearMap.comp_smul, bcForm_smul, Algebra.smul_def]

@[simp] theorem bcMapₗ_apply (g : (n → F) →ₗ[F] (m → F)) :
    (bcMapₗ g : (n → K) →ₗ[K] (m → K)) = bcMap g := rfl

/-- If an `F`-linear form `ℓ` vanishes on the kernel of `ν`, then its base change vanishes on the
zero set of the base change of `ν`.-/
theorem bcForm_eq_zero_of_ker_le {ν ℓ : (n → F) →ₗ[F] F} (h : LinearMap.ker ν ≤ LinearMap.ker ℓ)
    {x : n → K} (hx : bcForm ν x = 0) : bcForm ℓ x = 0 := by
  have h' : ⨅ _ : Unit, LinearMap.ker ν ≤ LinearMap.ker ℓ := by simpa using h
  have hmem := mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => ν) h'
  rw [Set.range_const, Submodule.mem_span_singleton] at hmem
  obtain ⟨c, rfl⟩ := hmem
  rw [bcForm_smul, hx, mul_zero]

end AlternatingAnalytic.TestCertificate
