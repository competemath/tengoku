import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfKer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Deformation_wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Deformation_wittHomMap_eq_zero_iff_forall_coeff_mem_hopfKer

set_option autoImplicit false

open _root_.Function open _root_.Deformation open _root_.Deformation.TruncWitt
open scoped TensorProduct

universe u v w

namespace Deformation
export _root_.Deformation (comulRingHom wittHom mem_wittHom_iff counit_coeff_of_mem_wittHom wittHomMap coe_wittHomMap)
namespace WittHomLeftExact
open _root_.Deformation

variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
variable {A : Type v} [CommRing A] [Bialgebra R A] {B : Type w} [CommRing B] [Bialgebra R B]

theorem apply_eq_algebraMap_counit_of_mem_hopfKer (π : A →ₐc[R] B) {a : A}
    (ha : a ∈ HopfAlgebra.hopfKer π) :
    π a = algebraMap R B (Coalgebra.counit (R := R) a) := by
  have h : HopfAlgebra.coaction π a = a ⊗ₜ[R] 1 := ha
  rw [HopfAlgebra.coaction_apply] at h
  let 𝓡 := Coalgebra.Repr.arbitrary R a
  have hsum : Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B)
      (Coalgebra.comul (R := R) a) = ∑ i ∈ 𝓡.index, 𝓡.left i ⊗ₜ[R] π (𝓡.right i) := by
    rw [← 𝓡.eq, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  rw [hsum] at h

  let Φ : A ⊗[R] B →ₗ[R] B := TensorProduct.lift ((LinearMap.lsmul R B).comp Coalgebra.counit)
  have hΦ : ∀ (a' : A) (b : B), Φ (a' ⊗ₜ[R] b) = Coalgebra.counit (R := R) a' • b := fun a' b => by
    simp [Φ]
  have h2 := congrArg Φ h
  rw [map_sum] at h2
  simp only [hΦ] at h2
  have h3 : ∑ i ∈ 𝓡.index, Coalgebra.counit (R := R) (𝓡.left i) • π (𝓡.right i) =
      π (∑ i ∈ 𝓡.index, Coalgebra.counit (R := R) (𝓡.left i) • 𝓡.right i) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
  rw [h3, Coalgebra.sum_counit_smul 𝓡] at h2
  rw [h2, Algebra.algebraMap_eq_smul_one]

theorem main (π : A →ₐc[R] B) (x : wittHom R p n A) :
    wittHomMap p n π x = 0 ↔
      ∀ i, (x : TruncatedWittVector p n A).coeff i ∈ HopfAlgebra.hopfKer π := by
  constructor
  · intro h0 i
    have hx := (mem_wittHom_iff (x : TruncatedWittVector p n A)).1 x.2
    have hπ : map (π : A →ₐ[R] B).toRingHom (x : TruncatedWittVector p n A) = 0 := by
      have := congrArg Subtype.val h0
      simpa using this

    let θ : A ⊗[R] A →ₐ[R] A ⊗[R] B :=
      Algebra.TensorProduct.map (AlgHom.id R A) (π : A →ₐ[R] B)
    have hΔ : θ.toRingHom.comp (comulRingHom R A) = (HopfAlgebra.coaction π).toRingHom := rfl
    have h₁ : θ.toRingHom.comp
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] A).toRingHom =
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toRingHom := by
      refine RingHom.ext fun a => ?_
      simp [θ]
    have h₂ : θ.toRingHom.comp
        (Algebra.TensorProduct.includeRight : A →ₐ[R] A ⊗[R] A).toRingHom =
        (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom.comp
          (π : A →ₐ[R] B).toRingHom := by
      refine RingHom.ext fun a => ?_
      simp [θ]
    have hpush := congrArg (map θ.toRingHom) hx
    rw [map_add, map_map, map_map, map_map, hΔ, h₁, h₂, ← map_map (π : A →ₐ[R] B).toRingHom,
      hπ, map_zero, add_zero] at hpush
    have hi := congrArg (TruncatedWittVector.coeff i) hpush
    rw [coeff_map, coeff_map] at hi

    rw [HopfAlgebra.mem_hopfKer_iff]
    exact hi
  · intro hmem
    refine Subtype.ext (TruncatedWittVector.ext fun i => ?_)
    rw [coe_wittHomMap, coeff_map]
    change π ((x : TruncatedWittVector p n A).coeff i) = (0 : TruncatedWittVector p n B).coeff i
    rw [TruncatedWittVector.coeff_zero, apply_eq_algebraMap_counit_of_mem_hopfKer π (hmem i),
      counit_coeff_of_mem_wittHom x.2 i, map_zero]

end Deformation.WittHomLeftExact

theorem solution
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A] {B : Type w} [CommRing B] [Bialgebra R B]
    (π : A →ₐc[R] B) (x : Deformation.wittHom R p n A) :
    Deformation.wittHomMap p n π x = 0 ↔
      ∀ i, (x : TruncatedWittVector p n A).coeff i ∈ HopfAlgebra.hopfKer π :=
  Deformation.WittHomLeftExact.main π x
