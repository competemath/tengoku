import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_UnramQuad_exists_frobenius_quotient_and_finite_flat_quotientMap.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_UnramQuad_exists_frobenius_quotient_and_finite_flat_quotientMap

set_option autoImplicit false

namespace F6preAux

section O2

variable {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)

abbrev O2 : Subalgebra 𝒪 Onr :=
  AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)

theorem mem_O2_iff (y : Onr) : y ∈ O2 Fr ↔ Fr (Fr y) = y := by
  simp [AlgHom.mem_equalizer]

theorem fr_mem_O2 {y : Onr} (hy : y ∈ O2 Fr) : Fr y ∈ O2 Fr := by
  rw [mem_O2_iff] at hy ⊢
  rw [hy]

noncomputable def Fr₂ : ↥(O2 Fr) ≃ₐ[𝒪] ↥(O2 Fr) :=
  AlgEquiv.ofAlgHom
    ((Fr : Onr →ₐ[𝒪] Onr).domRestrict (O2 Fr) |>.codRestrict (O2 Fr) (fun y => fr_mem_O2 Fr y.2))
    ((Fr : Onr →ₐ[𝒪] Onr).domRestrict (O2 Fr) |>.codRestrict (O2 Fr) (fun y => fr_mem_O2 Fr y.2))
    (by
      ext y
      simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_codRestrict, AlgHom.coe_id, id_eq]
      exact (mem_O2_iff Fr (y : Onr)).1 y.2)
    (by
      ext y
      simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_codRestrict, AlgHom.coe_id, id_eq]
      exact (mem_O2_iff Fr (y : Onr)).1 y.2)

@[scoped simp] theorem coe_Fr₂ (y : ↥(O2 Fr)) : ((Fr₂ Fr y : ↥(O2 Fr)) : Onr) = Fr (y : Onr) := rfl

theorem Fr₂_Fr₂ (y : ↥(O2 Fr)) : Fr₂ Fr (Fr₂ Fr y) = y := by
  ext
  simp only [coe_Fr₂]
  exact (mem_O2_iff Fr (y : Onr)).1 y.2

theorem Fr₂_algebraMap (x : 𝒪) : Fr₂ Fr (algebraMap 𝒪 (↥(O2 Fr)) x) = algebraMap 𝒪 (↥(O2 Fr)) x :=
  AlgEquiv.commutes _ x

variable (π : 𝒪)

abbrev lvl (n : ℕ) : Ideal ↥(O2 Fr) := Ideal.span {(algebraMap 𝒪 (↥(O2 Fr)) π) ^ (n + 1)}

theorem lvl_map_Fr₂ (n : ℕ) : lvl Fr π n = (lvl Fr π n).map (Fr₂ Fr : ↥(O2 Fr) →+* ↥(O2 Fr)) := by
  rw [Ideal.map_span, Set.image_singleton]
  have h : (Fr₂ Fr : ↥(O2 Fr) →+* ↥(O2 Fr)) ((algebraMap 𝒪 (↥(O2 Fr)) π) ^ (n + 1)) = (algebraMap 𝒪 (↥(O2 Fr)) π) ^ (n + 1) := by
    rw [map_pow]
    exact congrArg (· ^ (n + 1)) (Fr₂_algebraMap Fr π)
  rw [h]

noncomputable def Fr₂lvl (n : ℕ) : (↥(O2 Fr) ⧸ lvl Fr π n) ≃ₐ[𝒪] (↥(O2 Fr) ⧸ lvl Fr π n) :=
  Ideal.quotientEquivAlg (lvl Fr π n) (lvl Fr π n) (Fr₂ Fr) (lvl_map_Fr₂ Fr π n)

theorem Fr₂lvl_mk (n : ℕ) (y : ↥(O2 Fr)) :
    Fr₂lvl Fr π n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (Fr₂ Fr y) := by
  simp [Fr₂lvl]

theorem Fr₂lvl_link (n : ℕ) (y y' : ↥(O2 Fr)) (h : (y' : Onr) = Fr (y : Onr)) :
    Fr₂lvl Fr π n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y' := by
  rw [Fr₂lvl_mk]
  congr 1
  ext
  rw [coe_Fr₂, h]

theorem Fr₂lvl_Fr₂lvl (n : ℕ) (z : ↥(O2 Fr) ⧸ lvl Fr π n) : Fr₂lvl Fr π n (Fr₂lvl Fr π n z) = z := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [Fr₂lvl_mk, Fr₂lvl_mk, Fr₂_Fr₂]

end O2

section Finiteness

variable {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [IsDomain Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
variable (π : 𝒪)

end Finiteness

section LevelBase

variable {𝒪 : Type} [CommRing 𝒪] {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr) (π : 𝒪)

theorem base_le_comap (n : ℕ) :
    Ideal.span {π ^ (n + 1)} ≤ (lvl Fr π n).comap (algebraMap 𝒪 ↥(O2 Fr)) := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]
  exact Ideal.subset_span rfl

theorem lvl_eq_map (n : ℕ) : lvl Fr π n = (Ideal.span {π ^ (n + 1)}).map (algebraMap 𝒪 ↥(O2 Fr)) := by
  rw [Ideal.map_span, Set.image_singleton, map_pow]

abbrev baseMap (n : ℕ) : (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) →+* (↥(O2 Fr) ⧸ lvl Fr π n) :=
  Ideal.quotientMap (lvl Fr π n) (algebraMap 𝒪 ↥(O2 Fr)) (base_le_comap Fr π n)

theorem baseMap_flat (n : ℕ) [Module.Flat 𝒪 ↥(O2 Fr)] : (baseMap Fr π n).Flat := by
  set J : Ideal 𝒪 := Ideal.span {π ^ (n + 1)}

  have hflat : Module.Flat (𝒪 ⧸ J) (↥(O2 Fr) ⧸ J.map (algebraMap 𝒪 ↥(O2 Fr))) :=
    Module.Flat.of_linearEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (↥(O2 Fr)) J).toLinearEquiv
  have h1 : (Ideal.quotientMap (J.map (algebraMap 𝒪 ↥(O2 Fr))) (algebraMap 𝒪 ↥(O2 Fr)) Ideal.le_comap_map).Flat := by
    have := (RingHom.flat_algebraMap_iff (R := 𝒪 ⧸ J) (S := ↥(O2 Fr) ⧸ J.map (algebraMap 𝒪 ↥(O2 Fr)))).mpr hflat
    exact this

  let e : (↥(O2 Fr) ⧸ J.map (algebraMap 𝒪 ↥(O2 Fr))) ≃ₐ[𝒪] (↥(O2 Fr) ⧸ lvl Fr π n) :=
    Ideal.quotientEquivAlgOfEq 𝒪 (lvl_eq_map Fr π n).symm
  have hcomp : baseMap Fr π n =
      e.toRingEquiv.toRingHom.comp (Ideal.quotientMap (J.map (algebraMap 𝒪 ↥(O2 Fr))) (algebraMap 𝒪 ↥(O2 Fr)) Ideal.le_comap_map) := by
    apply Ideal.Quotient.ringHom_ext
    ext x
    simp only [RingHom.coe_comp, Function.comp_apply, Ideal.quotientMap_mk]
    change _ = e (Ideal.Quotient.mk _ (algebraMap 𝒪 ↥(O2 Fr) x))
    rw [Ideal.quotientEquivAlgOfEq_mk]
  rw [hcomp]
  exact (RingHom.Flat.comp_iff_of_bijective_left e.bijective).mpr h1

end LevelBase

end F6preAux
open scoped _root_.P2MW.S_CerednikDrinfeld_UnramQuad_exists_frobenius_quotient_and_finite_flat_quotientMap.F6preAux

open F6preAux in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hfree : Module.Free 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
    (hrank : Module.finrank 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) = 2) :
    ∃ Fr₂ : ∀ n : ℕ, (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) ≃ₐ[𝒪] (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}),

      (∀ (n : ℕ) (y y' : ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))), (y' : Onr) = Fr (y : Onr) →
        Fr₂ n (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y') ∧

      (∀ (n : ℕ) (x : (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})), Fr₂ n (Fr₂ n x) = x) ∧

      (∀ n : ℕ, (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            𝒪 ⧸ Ideal.span {π ^ (n + 1)} →+* (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})).Finite ∧
        (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)}) (algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
          (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl) :
            𝒪 ⧸ Ideal.span {π ^ (n + 1)} →+* (↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) ⧸ Ideal.span {(algebraMap 𝒪 ↥(AlgHom.equalizer ((Fr.trans Fr : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) π) ^ (n + 1)})).Flat) := by
  haveI := hfree

  haveI hfin : Module.Finite 𝒪 ↥(O2 Fr) := by
    rcases subsingleton_or_nontrivial 𝒪 with h𝒪 | h𝒪
    · haveI : Subsingleton ↥(O2 Fr) := Module.subsingleton 𝒪 _
      exact Module.Finite.of_finite
    · exact Module.finite_of_finrank_pos (by rw [hrank]; norm_num)
  haveI hflat : Module.Flat 𝒪 ↥(O2 Fr) := inferInstance
  refine ⟨fun n => Fr₂lvl Fr π n, fun n y y' h => Fr₂lvl_link Fr π n y y' h, fun n x => Fr₂lvl_Fr₂lvl Fr π n x, fun n => ⟨?_, ?_⟩⟩
  ·
    change (baseMap Fr π n).Finite
    letI : Algebra (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) (↥(O2 Fr) ⧸ lvl Fr π n) := (baseMap Fr π n).toAlgebra
    haveI : IsScalarTower 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) (↥(O2 Fr) ⧸ lvl Fr π n) :=
      IsScalarTower.of_algebraMap_eq (fun x => rfl)
    haveI : Module.Finite 𝒪 (↥(O2 Fr) ⧸ lvl Fr π n) := inferInstance
    exact Module.Finite.of_restrictScalars_finite 𝒪 (𝒪 ⧸ Ideal.span {π ^ (n + 1)}) (↥(O2 Fr) ⧸ lvl Fr π n)
  · exact baseMap_flat Fr π n
