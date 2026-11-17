import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_formallyUnramified_of_ker_counit_eq_sq.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_formallyUnramified_of_ker_counit_eq_sq

universe u v

set_option autoImplicit false

open TensorProduct

namespace HopfAlgebra
export _root_.HopfAlgebra (sum_mul_antipode_eq_algebraMap_counit antipode_one antipode_mul sum_antipode_mul_eq_algebraMap_counit)
open _root_.HopfAlgebra

variable {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]

noncomputable def antipodeAlgHom : H →ₐ[R] H :=
  AlgHom.ofLinearMap (antipode R (A := H)) antipode_one (fun a b => by rw [antipode_mul_antidistrib, mul_comm])

/--
@isnad1 id=eq.0h3v.s8.2f9095497dc0 from=translated src=- shape=714eb64c vocab=5598dd63
-/
@[scoped simp] theorem antipodeAlgHom_apply (a : H) : antipodeAlgHom (R := R) a = antipode R a := rfl

noncomputable def shearRight : H →ₐ[R] H ⊗[R] H :=
  (Algebra.TensorProduct.map (antipodeAlgHom (R := R) (H := H)) (AlgHom.id R H)).comp
    (Bialgebra.comulAlgHom R H)

/--
@isnad1 id=eq.0h5v.s11.825cfd580141 from=translated src=- shape=13df4155 vocab=2130c378
-/
theorem shearRight_apply (b : H) {ιr : Type*} (r : Coalgebra.Repr R b ιr) :
    shearRight (R := R) b = ∑ i ∈ r.index, antipode R (r.left i) ⊗ₜ[R] r.right i := by
  change Algebra.TensorProduct.map (antipodeAlgHom (R := R) (H := H)) (AlgHom.id R H)
    (Coalgebra.comul (R := R) b) = _
  rw [← r.eq, map_sum]
  simp only [Algebra.TensorProduct.map_tmul, antipodeAlgHom_apply, AlgHom.id_apply]

noncomputable def shear : H ⊗[R] H →ₐ[R] H ⊗[R] H :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (S := R)) (shearRight (R := R))
    (fun _ _ => .all _ _)

/--
@isnad1 id=eq.0h6v.s11.fb0671a31be5 from=translated src=- shape=33f4ec9c vocab=81ca7bfc
-/
theorem shear_tmul (a b : H) {ιr : Type*} (r : Coalgebra.Repr R b ιr) :
    shear (R := R) (a ⊗ₜ[R] b) = ∑ i ∈ r.index, (a * antipode R (r.left i)) ⊗ₜ[R] r.right i := by
  rw [shear, Algebra.TensorProduct.lift_tmul, shearRight_apply b r, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/--
@isnad1 id=eq.0h3v.s11.b9332b22715d from=translated src=- shape=975fa9b2 vocab=61f40949
-/
theorem lmul'_shear_one_tmul (b : H) :
    Algebra.TensorProduct.lmul' (S := H) R (shear (R := R) ((1 : H) ⊗ₜ[R] b)) =
      algebraMap R H (Coalgebra.counit b) := by
  rw [shear_tmul 1 b (Coalgebra.Repr.arbitrary R b), map_sum]
  simp only [one_mul, Algebra.TensorProduct.lmul'_apply_tmul]
  exact sum_antipode_mul_eq_algebraMap_counit _

/--
@isnad1 id=eq.0h5v.s11.8b89b378ef0f from=translated src=- shape=94a5253b vocab=7730b420
-/
theorem shear_comul (b : H) {ιr : Type*} (r : Coalgebra.Repr R b ιr) :
    ∑ i ∈ r.index, shear (R := R) (r.left i ⊗ₜ[R] r.right i) = (1 : H) ⊗ₜ[R] b := by

  let T : H ⊗[R] (H ⊗[R] H) →ₗ[R] H ⊗[R] H :=
    LinearMap.rTensor H (LinearMap.mul' R H ∘ₗ LinearMap.lTensor H (antipode R)) ∘ₗ
      (TensorProduct.assoc R H H H).symm.toLinearMap
  have hT : ∀ x y z : H, T (x ⊗ₜ[R] (y ⊗ₜ[R] z)) = (x * antipode R y) ⊗ₜ[R] z := fun x y z => by
    simp only [T, LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul,
      LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, LinearMap.mul'_apply]
  let a₁ : ∀ i : ιr, Coalgebra.Repr R (r.left i) (H × H) := fun i => Coalgebra.Repr.arbitrary R _
  let a₂ : ∀ i : ιr, Coalgebra.Repr R (r.right i) (H × H) := fun i => Coalgebra.Repr.arbitrary R _
  have hco := congrArg T (Coalgebra.sum_tmul_tmul_eq r a₁ a₂)
  simp only [map_sum, hT] at hco

  have hleft : ∑ i ∈ r.index, ∑ j ∈ (a₁ i).index,
      ((a₁ i).left j * antipode R ((a₁ i).right j)) ⊗ₜ[R] r.right i = (1 : H) ⊗ₜ[R] b := by
    have h2 : ∑ i ∈ r.index, algebraMap R H (Coalgebra.counit (r.left i)) ⊗ₜ[R] r.right i
        = (1 : H) ⊗ₜ[R] b := by
      have h := congrArg (LinearMap.rTensor H (Algebra.linearMap R H)) (Coalgebra.sum_counit_tmul_eq r)
      simpa only [map_sum, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one] using h
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sum_tmul, sum_mul_antipode_eq_algebraMap_counit (a₁ i)]

  have hright : ∑ i ∈ r.index, ∑ j ∈ (a₂ i).index,
      (r.left i * antipode R ((a₂ i).left j)) ⊗ₜ[R] (a₂ i).right j =
        ∑ i ∈ r.index, shear (R := R) (r.left i ⊗ₜ[R] r.right i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [shear_tmul (r.left i) (r.right i) (a₂ i)]
  rw [← hright, ← hco, hleft]

/--
@isnad1 id=le.1h2v.s11.a12c653ee46c from=translated src=- shape=b0e4fcd0 vocab=bd6dd45a
-/
theorem kaehlerDifferential_ideal_le_sq
    (hI : RingHom.ker (Bialgebra.counitAlgHom R H) = RingHom.ker (Bialgebra.counitAlgHom R H) ^ 2) :
    KaehlerDifferential.ideal R H ≤ KaehlerDifferential.ideal R H ^ 2 := by
  set I : Ideal H := RingHom.ker (Bialgebra.counitAlgHom R H) with hIdef

  set K : Ideal (H ⊗[R] H) := I.map (Algebra.TensorProduct.includeRight (R := R) (A := H) (B := H))
    with hK
  have hKsq : K = K ^ 2 := by
    rw [hK, ← Ideal.map_pow, ← hI]

  have hKJ : K.map (shear (R := R) (H := H)) ≤ KaehlerDifferential.ideal R H := by
    rw [Ideal.map_le_iff_le_comap, hK, Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, Ideal.mem_comap, KaehlerDifferential.ideal, RingHom.mem_ker]
    change Algebra.TensorProduct.lmul' (S := H) R (shear (R := R) ((1 : H) ⊗ₜ[R] i)) = 0
    rw [lmul'_shear_one_tmul]
    have : Coalgebra.counit (R := R) i = 0 := by
      rwa [hIdef, RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hi
    rw [this, map_zero]

  have hgen : ∀ b : H, (1 : H) ⊗ₜ[R] b - b ⊗ₜ[R] 1 ∈ K.map (shear (R := R) (H := H)) := by
    intro b
    have r := Coalgebra.Repr.arbitrary R b

    have hpre : ∑ i ∈ r.index, r.left i ⊗ₜ[R] r.right i - b ⊗ₜ[R] (1 : H) ∈ K := by
      have h3 : ∑ i ∈ r.index, r.left i ⊗ₜ[R] algebraMap R H (Coalgebra.counit (r.right i))
          = b ⊗ₜ[R] (1 : H) := by
        have h := congrArg (LinearMap.lTensor H (Algebra.linearMap R H)) (Coalgebra.sum_tmul_counit_eq r)
        simpa only [map_sum, LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one] using h
      rw [← h3, ← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun i _ => ?_
      rw [← tmul_sub, show r.left i ⊗ₜ[R] (r.right i - algebraMap R H (Coalgebra.counit (r.right i)))
          = (r.left i ⊗ₜ[R] (1 : H)) * ((1 : H) ⊗ₜ[R] (r.right i - algebraMap R H (Coalgebra.counit (r.right i)))) by
            rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
      refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
      rw [hIdef, RingHom.mem_ker, Bialgebra.counitAlgHom_apply, map_sub, Bialgebra.counit_algebraMap,
        sub_self]
    have himg := Ideal.mem_map_of_mem (shear (R := R) (H := H)) hpre
    rw [map_sub, map_sum, shear_comul b r, shear_tmul b 1 (Coalgebra.Repr.arbitrary R (1 : H))] at himg

    have hone : ∑ i ∈ (Coalgebra.Repr.arbitrary R (1 : H)).index,
        (b * antipode R ((Coalgebra.Repr.arbitrary R (1 : H)).left i)) ⊗ₜ[R]
          (Coalgebra.Repr.arbitrary R (1 : H)).right i = b ⊗ₜ[R] (1 : H) := by
      have := shear_tmul (R := R) b 1 (Coalgebra.Repr.arbitrary R (1 : H))
      rw [← this, shear, Algebra.TensorProduct.lift_tmul, map_one, mul_one,
        Algebra.TensorProduct.includeLeft_apply]
    rwa [hone] at himg

  have hJle : KaehlerDifferential.ideal R H ≤ K.map (shear (R := R) (H := H)) := by
    rw [← KaehlerDifferential.span_range_eq_ideal, Ideal.span_le]
    rintro _ ⟨b, rfl⟩
    exact hgen b
  calc KaehlerDifferential.ideal R H ≤ K.map (shear (R := R) (H := H)) := hJle
    _ = (K.map (shear (R := R) (H := H))) ^ 2 := by rw [← Ideal.map_pow, ← hKsq]
    _ ≤ KaehlerDifferential.ideal R H ^ 2 := Ideal.pow_right_mono hKJ 2

/--
@isnad1 id=subsingl.1h2v.s8.3767b129d206 from=translated src=- shape=d2709bc3 vocab=fd89ca11
-/
theorem subsingleton_kaehlerDifferential
    (hI : RingHom.ker (Bialgebra.counitAlgHom R H) = RingHom.ker (Bialgebra.counitAlgHom R H) ^ 2) :
    Subsingleton (Ω[H⁄R]) := by
  have hle := kaehlerDifferential_ideal_le_sq (R := R) (H := H) hI
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := (KaehlerDifferential.ideal R H).toCotangent_surjective x
  obtain ⟨y, rfl⟩ := (KaehlerDifferential.ideal R H).toCotangent_surjective y
  rw [(Ideal.toCotangent_eq_zero _ _).2 (hle x.2), (Ideal.toCotangent_eq_zero _ _).2 (hle y.2)]

end HopfAlgebra
open scoped _root_.P2MW.S_HopfAlgebra_formallyUnramified_of_ker_counit_eq_sq.HopfAlgebra

/--
@isnad1 id=formally.1h2v.s8.a3ed1f978c02 from=translated src=- shape=dc223f09 vocab=06a5c3fd
-/
theorem solution
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    (hI : RingHom.ker (Bialgebra.counitAlgHom R H) = RingHom.ker (Bialgebra.counitAlgHom R H) ^ 2) :
    Algebra.FormallyUnramified R H := by
  haveI := HopfAlgebra.subsingleton_kaehlerDifferential (R := R) (H := H) hI
  exact (Algebra.formallyUnramified_iff R H).mpr ‹_›
