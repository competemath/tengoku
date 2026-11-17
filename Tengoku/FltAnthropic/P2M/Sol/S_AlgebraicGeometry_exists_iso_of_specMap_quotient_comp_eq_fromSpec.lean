import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Tengoku.FltAnthropic.Theorems.Thm_AlgHom_bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_exists_iso_of_specMap_quotient_comp_eq_fromSpec.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_exists_iso_of_specMap_quotient_comp_eq_fromSpec

set_option autoImplicit false
set_option maxHeartbeats 3200000

open _root_.CategoryTheory open _root_.AlgebraicGeometry open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

universe u

/--
@isnad1 id=ex.4h6v.s16.a49bfa7dee88 from=translated src=- shape=375ea5a8 vocab=1c5addb8
-/
theorem solution
    {T' : Type u} [CommRing T'] (I : Ideal T') (hI2 : I * I = ⊥)
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T')) (U : Y.Opens) (hU : IsAffineOpen U)
    (v : Spec Γ(Y, U) ⟶ Y) (hv : v ≫ qY = hU.fromSpec ≫ qY)
    (hred : letI := algebraOfHom qY U
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ v =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.fromSpec) :
    ∃ τ : (U : Scheme.{u}) ≅ (U : Scheme.{u}),
      hU.isoSpec.inv ≫ τ.hom ≫ U.ι = v ∧
      τ.hom ≫ U.ι ≫ qY = U.ι ≫ qY ∧
      (∀ O : (U : Scheme.{u}).Opens, τ.hom ⁻¹ᵁ O = O) ∧
      (letI := algebraOfHom qY U
       Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv ≫ τ.hom =
         Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' Γ(Y, U))))) ≫ hU.isoSpec.inv) := by
  classical
  letI instAlg : Algebra T' Γ(Y, U) := algebraOfHom qY U
  set J : Ideal Γ(Y, U) := I.map (algebraMap T' Γ(Y, U)) with hJ

  have hJ2 : J * J = ⊥ := by rw [hJ, ← Ideal.map_mul, hI2, Ideal.map_bot]
  have hJnil : ∀ x ∈ J, IsNilpotent x := fun x hx => by
    refine ⟨2, ?_⟩
    rw [pow_two]
    have hxx := Ideal.mul_mem_mul hx hx
    rw [hJ2] at hxx
    exact (Submodule.mem_bot _).mp hxx

  have hsurjpts : Function.Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).base := by
    intro p
    have hp : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk J)) := by
      rw [range_comap_of_surjective (R := Y.presheaf.obj (Opposite.op U)) _ (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective]
      intro x hx
      have hx' : x ∈ J := by rwa [Ideal.mk_ker] at hx
      exact nilpotent_iff_mem_prime.mp (hJnil x hx') p.asIdeal p.isPrime
    obtain ⟨q, hq⟩ := hp
    exact ⟨q, hq⟩

  have hrange : Set.range v.base ⊆ Set.range U.ι.base := by
    rintro y ⟨p, rfl⟩
    obtain ⟨p', rfl⟩ := hsurjpts p
    rw [Scheme.Opens.range_ι]
    show (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ v).base p' ∈ (U : Set Y)
    rw [hred]
    exact hU.range_fromSpec.le ⟨_, rfl⟩
  let v' : Spec Γ(Y, U) ⟶ (U : Scheme.{u}) := IsOpenImmersion.lift U.ι v hrange
  have hv' : v' ≫ U.ι = v := IsOpenImmersion.lift_fac _ _ _

  let e : Spec Γ(Y, U) ⟶ Spec Γ(Y, U) := v' ≫ hU.isoSpec.hom
  let ψ₀ : Γ(Y, U) ⟶ Γ(Y, U) := Spec.preimage e
  have hψ₀ : Spec.map ψ₀ = e := Spec.map_preimage e

  have hstr : hU.fromSpec ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y, U))) := by
    rw [show CommRingCat.ofHom (algebraMap T' Γ(Y, U)) = (Scheme.ΓSpecIso (CommRingCat.of T')).inv ≫ qY.appLE ⊤ U le_top from rfl,
      Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
      IsAffineOpen.SpecMap_appLE_fromSpec qY (isAffineOpen_top _) hU le_top]
  have hestr : e ≫ Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y, U))) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y, U))) := by
    rw [← hstr, ← IsAffineOpen.isoSpec_inv_ι]
    show (v' ≫ hU.isoSpec.hom) ≫ hU.isoSpec.inv ≫ U.ι ≫ qY = hU.isoSpec.inv ≫ U.ι ≫ qY
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hv', hv, ← IsAffineOpen.isoSpec_inv_ι, Category.assoc]
  have hcomm : ∀ t : T', ψ₀.hom (algebraMap T' Γ(Y, U) t) = algebraMap T' Γ(Y, U) t := by
    have h1 : Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y, U)) ≫ ψ₀) = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(Y, U))) := by
      rw [Spec.map_comp, hψ₀]; exact hestr
    have h2 := Spec.map_injective h1
    intro t
    exact congrArg (fun f : CommRingCat.of T' ⟶ Γ(Y, U) => f.hom t) h2
  let ψ : Γ(Y, U) →ₐ[T'] Γ(Y, U) := ⟨ψ₀.hom, hcomm⟩

  have hemod : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ e = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    have h2 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ v' =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hU.isoSpec.inv := by
      rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hv', IsAffineOpen.isoSpec_inv_ι]
      exact hred
    show Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ v' ≫ hU.isoSpec.hom = _
    rw [← Category.assoc, h2, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hmod : ∀ c : Γ(Y, U), ψ c - c ∈ I.map (algebraMap T' Γ(Y, U)) := by
    have h3 : Spec.map (ψ₀ ≫ CommRingCat.ofHom (Ideal.Quotient.mk J)) = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
      rw [Spec.map_comp, hψ₀]; exact hemod
    have h4 := Spec.map_injective h3
    intro c
    rw [← hJ, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact congrArg (fun f : Γ(Y, U) ⟶ CommRingCat.of (↥(Y.presheaf.obj (Opposite.op U)) ⧸ J) => f.hom c) h4

  obtain ⟨hbij, hfix⟩ :=
    AlgHom.bijective_and_comap_eq_of_forall_sub_mem_map_of_mul_eq_bot I hI2 (Y.presheaf.obj (Opposite.op U)) ψ hmod
  let ε : Γ(Y, U) ≅ Γ(Y, U) := (RingEquiv.ofBijective ψ hbij).toCommRingCatIso
  have hε : ε.hom = ψ₀ := rfl
  haveI : IsIso e := by rw [← hψ₀, ← hε]; infer_instance
  let τ : (U : Scheme.{u}) ≅ (U : Scheme.{u}) := hU.isoSpec ≪≫ asIso e ≪≫ hU.isoSpec.symm
  have hτ : τ.hom = hU.isoSpec.hom ≫ e ≫ hU.isoSpec.inv := rfl
  have hebase : ∀ p, e.base p = p := fun p => by
    rw [← hψ₀]; exact hfix p
  have hτb : ∀ x, τ.hom.base x = x := fun x => by
    rw [hτ]
    show hU.isoSpec.inv.base (e.base (hU.isoSpec.hom.base x)) = x
    rw [hebase]
    exact congrArg (fun f : (U : Scheme.{u}) ⟶ U => f.base x) hU.isoSpec.hom_inv_id
  refine ⟨τ, ?_, ?_, ?_, ?_⟩
  · rw [hτ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    show (v' ≫ hU.isoSpec.hom) ≫ hU.isoSpec.inv ≫ U.ι = v
    rw [Category.assoc, Iso.hom_inv_id_assoc, hv']
  · rw [hτ]
    simp only [Category.assoc]
    show hU.isoSpec.hom ≫ (v' ≫ hU.isoSpec.hom) ≫ hU.isoSpec.inv ≫ U.ι ≫ qY = U.ι ≫ qY
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc v', hv', hv, ← IsAffineOpen.isoSpec_inv_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  · intro O
    ext x
    show τ.hom.base x ∈ (O : Set _) ↔ x ∈ (O : Set _)
    rw [hτb]
  · rw [hτ, Iso.inv_hom_id_assoc, ← Category.assoc, hemod]
