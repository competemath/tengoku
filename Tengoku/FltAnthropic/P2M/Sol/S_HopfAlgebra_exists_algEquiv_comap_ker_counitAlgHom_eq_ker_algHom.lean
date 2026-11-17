import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom

open _root_.Bialgebra open _root_.Coalgebra open _root_.TensorProduct open _root_.Bialgebra.TensorProduct open _root_.Coalgebra.TensorProduct

noncomputable section

namespace HopfRightTranslate

universe u v

variable (K : Type u) [Field K] (A : Type v) [CommRing A] [HopfAlgebra K A]

def rightTranslate (χ : A →ₐ[K] K) : A →ₐ[K] A :=
  (Algebra.TensorProduct.rid K K A).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id K A) χ).comp (comulAlgHom K A))

def antipodeAlgHom : A →ₐ[K] A :=
  AlgHom.ofLinearMap (HopfAlgebra.antipode K) HopfAlgebra.antipode_one
    (fun a b => (HopfAlgebra.antipode_mul_antidistrib a b).trans (mul_comm _ _))

variable {K A}

/--
@isnad1 id=eq.0h3v.s9.2815569f538c from=translated src=- shape=31de17bd vocab=2e2350ec
-/
theorem antipodeAlgHom_apply (a : A) : antipodeAlgHom K A a = HopfAlgebra.antipode K a := rfl

/--
@isnad1 id=eq.0h6v.s10.0ec6a1625e4a from=translated src=- shape=342fbaca vocab=8e34b116
-/
theorem rightTranslate_apply_repr (χ : A →ₐ[K] K) (a : A) {ιrepr : Type*} (repr : Coalgebra.Repr K a ιrepr) :
    rightTranslate K A χ a = ∑ i ∈ repr.index, χ (repr.right i) • repr.left i := by
  show (Algebra.TensorProduct.rid K K A)
      (Algebra.TensorProduct.map (AlgHom.id K A) χ (comulAlgHom K A a)) = _
  have hcomul : comulAlgHom K A a = Coalgebra.comul (R := K) a := rfl
  rw [hcomul, ← repr.eq, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.rid_tmul]

/--
@isnad1 id=eq.0h5v.s10.5769d1a15bcd from=translated src=- shape=46547faa vocab=4d78dbea
-/
theorem sum_counit_right_smul {a : A} {ιrepr : Type*} (repr : Coalgebra.Repr K a ιrepr) :
    ∑ i ∈ repr.index, Coalgebra.counit (R := K) (repr.right i) • repr.left i = a := by
  have h := Coalgebra.sum_tmul_counit_eq (R := K) repr
  have h2 := congrArg (TensorProduct.rid K A) h
  simp only [map_sum, TensorProduct.rid_tmul, one_smul] at h2
  exact h2

/--
@isnad1 id=eq.0h3v.s8.2162f9e78048 from=translated src=- shape=2db7c1da vocab=65cf853e
-/
theorem counitAlgHom_comp_rightTranslate (χ : A →ₐ[K] K) :
    (counitAlgHom K A).comp (rightTranslate K A χ) = χ := by
  ext x
  show (counitAlgHom K A) ((Algebra.TensorProduct.rid K K A)
      (Algebra.TensorProduct.map (AlgHom.id K A) χ (comulAlgHom K A x))) = χ x
  have hcomul : comulAlgHom K A x = Coalgebra.comul (R := K) x := rfl
  rw [hcomul]
  have hmap : ((counitAlgHom K A).toLinearMap.comp
        (Algebra.TensorProduct.rid K K A).toLinearMap).comp
          (Algebra.TensorProduct.map (AlgHom.id K A) χ).toLinearMap
      = (TensorProduct.lid K K).toLinearMap.comp
          (χ.toLinearMap.lTensor K |>.comp ((Coalgebra.counit (R := K)).rTensor A)) := by
    ext a b
    simp [Algebra.TensorProduct.rid_tmul, TensorProduct.lid_tmul, Algebra.smul_def, mul_comm]
  have h2 := congrArg (· (Coalgebra.comul (R := K) x)) (congrArg DFunLike.coe hmap)
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgEquiv.toLinearMap_apply,
    LinearEquiv.coe_toLinearMap, Coalgebra.rTensor_counit_comul, LinearMap.lTensor_tmul,
    TensorProduct.lid_tmul, one_smul] at h2
  exact h2

/--
@isnad1 id=leftinve.0h3v.s9.87b0ab4fd4ad from=translated src=- shape=f1c68b90 vocab=8fa6658e
-/
theorem rightTranslate_leftInverse (χ : A →ₐ[K] K) :
    Function.LeftInverse (rightTranslate K A (χ.comp (antipodeAlgHom K A)))
      (rightTranslate K A χ) := by
  intro a
  set ψ : A →ₐ[K] K := χ.comp (antipodeAlgHom K A)
  set R0 := ℛ K a
  rw [rightTranslate_apply_repr χ a R0, map_sum]
  simp_rw [map_smul]
  have hinner : ∀ i, rightTranslate K A ψ (R0.left i) =
      ∑ j ∈ (ℛ K (R0.left i)).index,
        ψ ((ℛ K (R0.left i)).right j) • (ℛ K (R0.left i)).left j :=
    fun i => rightTranslate_apply_repr ψ (R0.left i) (ℛ K (R0.left i))
  simp_rw [hinner, Finset.smul_sum, smul_smul]
  set a₁ : ∀ i, Coalgebra.Repr K (R0.left i) (A × A) := fun i => ℛ K (R0.left i)
  set a₂ : ∀ i, Coalgebra.Repr K (R0.right i) (A × A) := fun i => ℛ K (R0.right i)
  have hcoassoc := Coalgebra.sum_tmul_tmul_eq (R := K) R0 a₁ a₂
  let g : A ⊗[K] A →ₗ[K] K :=
    TensorProduct.lift (((LinearMap.mul K K).comp ψ.toLinearMap).compl₂ χ.toLinearMap)
  let φ : A ⊗[K] (A ⊗[K] A) →ₗ[K] A :=
    TensorProduct.lift ((LinearMap.flip (LinearMap.lsmul K A)).compl₂ g)
  have hφ : ∀ (x y z : A), φ (x ⊗ₜ (y ⊗ₜ z)) = (ψ y * χ z) • x := by
    intro x y z
    simp only [φ, g, TensorProduct.lift.tmul, LinearMap.compl₂_apply, LinearMap.flip_apply,
      LinearMap.lsmul_apply, LinearMap.comp_apply, LinearMap.mul_apply', AlgHom.toLinearMap_apply]
  have hcoassoc' := congrArg φ hcoassoc
  simp only [map_sum, hφ] at hcoassoc'
  calc ∑ i ∈ R0.index, ∑ j ∈ (a₁ i).index,
          (χ (R0.right i) * ψ ((a₁ i).right j)) • (a₁ i).left j
      = ∑ i ∈ R0.index, ∑ j ∈ (a₁ i).index,
          (ψ ((a₁ i).right j) * χ (R0.right i)) • (a₁ i).left j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    _ = ∑ i ∈ R0.index, ∑ j ∈ (a₂ i).index,
          (ψ ((a₂ i).left j) * χ ((a₂ i).right j)) • R0.left i := hcoassoc'
    _ = ∑ i ∈ R0.index,
          (∑ j ∈ (a₂ i).index, ψ ((a₂ i).left j) * χ ((a₂ i).right j)) • R0.left i := by
        simp_rw [Finset.sum_smul]
    _ = ∑ i ∈ R0.index, (counit (R := K) (R0.right i)) • R0.left i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        simp_rw [ψ, AlgHom.comp_apply, antipodeAlgHom_apply, ← map_mul, ← map_sum]
        rw [HopfAlgebra.sum_antipode_mul_eq_smul (a₂ i), map_smul, map_one, smul_eq_mul,
          mul_one]
    _ = a := sum_counit_right_smul R0

/--
@isnad1 id=rightinv.0h3v.s9.093b016dc2f1 from=translated src=- shape=f1c68b90 vocab=e5ab67d8
-/
theorem rightTranslate_rightInverse (χ : A →ₐ[K] K) :
    Function.RightInverse (rightTranslate K A (χ.comp (antipodeAlgHom K A)))
      (rightTranslate K A χ) := by
  intro a
  set ψ : A →ₐ[K] K := χ.comp (antipodeAlgHom K A)
  set R0 := ℛ K a
  rw [rightTranslate_apply_repr ψ a R0, map_sum]
  simp_rw [map_smul]
  have hinner : ∀ i, rightTranslate K A χ (R0.left i) =
      ∑ j ∈ (ℛ K (R0.left i)).index,
        χ ((ℛ K (R0.left i)).right j) • (ℛ K (R0.left i)).left j :=
    fun i => rightTranslate_apply_repr χ (R0.left i) (ℛ K (R0.left i))
  simp_rw [hinner, Finset.smul_sum, smul_smul]
  set a₁ : ∀ i, Coalgebra.Repr K (R0.left i) (A × A) := fun i => ℛ K (R0.left i)
  set a₂ : ∀ i, Coalgebra.Repr K (R0.right i) (A × A) := fun i => ℛ K (R0.right i)
  have hcoassoc := Coalgebra.sum_tmul_tmul_eq (R := K) R0 a₁ a₂
  let g : A ⊗[K] A →ₗ[K] K :=
    TensorProduct.lift (((LinearMap.mul K K).comp χ.toLinearMap).compl₂ ψ.toLinearMap)
  let φ : A ⊗[K] (A ⊗[K] A) →ₗ[K] A :=
    TensorProduct.lift ((LinearMap.flip (LinearMap.lsmul K A)).compl₂ g)
  have hφ : ∀ (x y z : A), φ (x ⊗ₜ (y ⊗ₜ z)) = (χ y * ψ z) • x := by
    intro x y z
    simp only [φ, g, TensorProduct.lift.tmul, LinearMap.compl₂_apply, LinearMap.flip_apply,
      LinearMap.lsmul_apply, LinearMap.comp_apply, LinearMap.mul_apply', AlgHom.toLinearMap_apply]
  have hcoassoc' := congrArg φ hcoassoc
  simp only [map_sum, hφ] at hcoassoc'
  calc ∑ i ∈ R0.index, ∑ j ∈ (a₁ i).index,
          (ψ (R0.right i) * χ ((a₁ i).right j)) • (a₁ i).left j
      = ∑ i ∈ R0.index, ∑ j ∈ (a₁ i).index,
          (χ ((a₁ i).right j) * ψ (R0.right i)) • (a₁ i).left j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    _ = ∑ i ∈ R0.index, ∑ j ∈ (a₂ i).index,
          (χ ((a₂ i).left j) * ψ ((a₂ i).right j)) • R0.left i := hcoassoc'
    _ = ∑ i ∈ R0.index,
          (∑ j ∈ (a₂ i).index, χ ((a₂ i).left j) * ψ ((a₂ i).right j)) • R0.left i := by
        simp_rw [Finset.sum_smul]
    _ = ∑ i ∈ R0.index, (counit (R := K) (R0.right i)) • R0.left i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        simp_rw [ψ, AlgHom.comp_apply, antipodeAlgHom_apply, ← map_mul, ← map_sum]
        rw [HopfAlgebra.sum_mul_antipode_eq_smul (a₂ i), map_smul, map_one, smul_eq_mul,
          mul_one]
    _ = a := sum_counit_right_smul R0

def rightTranslateEquiv (χ : A →ₐ[K] K) : A ≃ₐ[K] A :=
  AlgEquiv.ofAlgHom (rightTranslate K A χ)
    (rightTranslate K A (χ.comp (antipodeAlgHom K A)))
    (AlgHom.ext (rightTranslate_rightInverse χ))
    (AlgHom.ext (rightTranslate_leftInverse χ))

/--
@isnad1 id=eq.0h3v.s9.bdad40083338 from=translated src=- shape=4a2d7d4d vocab=84a6ac1c
-/
theorem comap_ker_counitAlgHom_rightTranslate (χ : A →ₐ[K] K) :
    (RingHom.ker (counitAlgHom K A).toRingHom).comap (rightTranslate K A χ).toRingHom
      = RingHom.ker χ.toRingHom := by
  ext a
  simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  have := DFunLike.congr_fun (counitAlgHom_comp_rightTranslate χ) a
  simp only [AlgHom.comp_apply] at this
  rw [this]

end HopfRightTranslate

end

/--
@isnad1 id=ex.0h3v.s9.864b416a8260 from=translated src=- shape=e721e93b vocab=bddce3ce
-/
theorem solution
    (K : Type*) [Field K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] (χ : A →ₐ[K] K) :
    ∃ e : A ≃ₐ[K] A,
      (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).comap e.toRingEquiv.toRingHom
        = RingHom.ker χ.toRingHom := by
  refine ⟨HopfRightTranslate.rightTranslateEquiv χ, ?_⟩
  show (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).comap
      (HopfRightTranslate.rightTranslate K A χ).toRingHom = RingHom.ker χ.toRingHom
  exact HopfRightTranslate.comap_ker_counitAlgHom_rightTranslate χ
