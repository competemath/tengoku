import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace E163TC

section Pushout

variable {T' T C : Type u} [CommRing T'] [CommRing T] [CommRing C]

noncomputable def tau (π : T' →+* T) (hπ : Function.Surjective π) (φ : T' →+* C) :
    T →+* C ⧸ (RingHom.ker π).map φ :=
  (Ideal.Quotient.lift (RingHom.ker π) ((Ideal.Quotient.mk ((RingHom.ker π).map φ)).comp φ)
      (fun a ha => by
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_map_of_mem φ ha)).comp
    (RingHom.quotientKerEquivOfSurjective hπ).symm.toRingHom

/--
@isnad1 id=eq.1h6v.s11.bcefc9588f10 from=translated src=- shape=e2e4456f vocab=3f4929c6
-/
theorem tau_apply (π : T' →+* T) (hπ : Function.Surjective π) (φ : T' →+* C) (k : T') :
    tau π hπ φ (π k) = Ideal.Quotient.mk _ (φ k) := by
  simp [tau]

/--
@isnad1 id=eq.1h5v.s10.32b0f99cbeab from=translated src=- shape=88cc6083 vocab=542151f0
-/
theorem tau_comp (π : T' →+* T) (hπ : Function.Surjective π) (φ : T' →+* C) :
    (tau π hπ φ).comp π = (Ideal.Quotient.mk ((RingHom.ker π).map φ)).comp φ :=
  RingHom.ext fun k => tau_apply π hπ φ k

/--
@isnad1 id=ispushou.1h5v.s9.65a601692116 from=translated src=- shape=94ac83f8 vocab=d0458024
-/
theorem isPushout_quotient (π : T' →+* T) (hπ : Function.Surjective π) (φ : T' →+* C) :
    IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom π)
      (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map φ))) (CommRingCat.ofHom (tau π hπ φ)) := by
  have w : CommSq (CommRingCat.ofHom φ) (CommRingCat.ofHom π)
      (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map φ))) (CommRingCat.ofHom (tau π hπ φ)) :=
    ⟨by rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, tau_comp]⟩
  have hdesc : ∀ s : PushoutCocone (CommRingCat.ofHom φ) (CommRingCat.ofHom π),
      ∀ a ∈ (RingHom.ker π).map φ, s.inl.hom a = 0 := by
    intro s
    have hle : (RingHom.ker π).map φ ≤ RingHom.ker s.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro k hk
      have hc := congrArg (fun ψ : CommRingCat.of T' ⟶ s.pt => ψ.hom k) s.condition
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at hc
      simp only [Ideal.mem_comap, RingHom.mem_ker, hc, RingHom.mem_ker.mp hk, map_zero]
    exact fun a ha => hle ha
  refine IsPushout.of_isColimit' w (PushoutCocone.IsColimit.mk _
    (fun s => CommRingCat.ofHom (Ideal.Quotient.lift _ s.inl.hom (hdesc s)))
    (fun s => ?_) (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · ext a
    simp
  · ext t
    obtain ⟨k, rfl⟩ := hπ t
    have hc := congrArg (fun ψ : CommRingCat.of T' ⟶ s.pt => ψ.hom k) s.condition
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at hc
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, tau_apply,
      Ideal.Quotient.lift_mk, hc]
  · apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    have h1 : m.hom.comp (Ideal.Quotient.mk _) = s.inl.hom := by
      rw [← hm₁]; rfl
    rw [h1]
    ext a
    simp

end Pushout

/--
@isnad1 id=isnilpot.1h4v.s7.688c348c6b4a from=translated src=- shape=43e75246 vocab=005c8f5f
-/
theorem isNilpotent_map {T' C : Type u} [CommRing T'] [CommRing C] (φ : T' →+* C) {K : Ideal T'}
    (hK : IsNilpotent K) : IsNilpotent (K.map φ) := by
  obtain ⟨n, hn⟩ := hK
  refine ⟨n, ?_⟩
  rw [← Ideal.map_pow, hn]
  simp

end E163TC

/--
@isnad1 id=and.4h9v.s15.97b265c0dae8 from=translated src=- shape=2536e43a vocab=bc4a6591
-/
theorem solution
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {P P₀ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) (p₀ : P₀ ⟶ Spec (CommRingCat.of T))
    (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (D : P.Opens) (hD : IsAffineOpen D) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p D
    IsNilpotent ((RingHom.ker π).map (algebraMap T' Γ(P, D))) ∧
    ∃ ε : Spec (CommRingCat.of (Γ(P, D) ⧸ (RingHom.ker π).map (algebraMap T' Γ(P, D)))) ≅ ↑(G ⁻¹ᵁ D),
      ε.hom ≫ G ∣_ D ≫ hD.isoSpec.hom =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, D))))) := by
  letI inst := Scheme.TwoAffineOpenCover.algebraOfHom p D
  refine ⟨E163TC.isNilpotent_map _ hker, ?_⟩

  have hφ : CommRingCat.ofHom (algebraMap T' Γ(P, D)) =
      (Scheme.ΓSpecIso (.of T')).inv ≫ p.appLE ⊤ D le_top := rfl
  have hDp : hD.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap T' Γ(P, D))) = (D.ι ≫ p) ≫ 𝟙 _ := by
    rw [Category.comp_id, hφ, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
      IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hD le_top, IsAffineOpen.isoSpec_hom,
      IsAffineOpen.toSpecΓ_fromSpec_assoc]
  have sq1 : IsPullback (G ∣_ D) ((G ⁻¹ᵁ D).ι ≫ p₀) (D.ι ≫ p) (Spec.map (CommRingCat.ofHom π)) :=
    (isPullback_morphismRestrict G D).paste_vert hG
  have sq2 : IsPullback hD.isoSpec.hom (D.ι ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap T' Γ(P, D))))
      (𝟙 _) := IsPullback.of_horiz_isIso ⟨hDp⟩
  have sq3 := sq1.paste_horiz sq2
  rw [Category.comp_id] at sq3
  have sq4 := isPullback_SpecMap_of_isPushout _ _ _ _
    (E163TC.isPushout_quotient π hπ (algebraMap T' Γ(P, D)))
  exact ⟨sq4.isoIsPullback _ _ sq3, by rw [← Category.assoc]; exact sq4.isoIsPullback_hom_fst _ _ sq3⟩

