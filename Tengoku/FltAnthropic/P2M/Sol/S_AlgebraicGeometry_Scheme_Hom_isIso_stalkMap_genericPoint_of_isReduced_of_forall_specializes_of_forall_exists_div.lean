import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_stalkMap_genericPoint_surjective_of_forall_exists_div

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_genericPoint_of_isReduced_of_forall_specializes_of_forall_exists_div.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isIso_stalkMap_genericPoint_of_isReduced_of_forall_specializes_of_forall_exists_div

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=isiso.4h4v.s13.2a912d6fb3ed from=translated src=- shape=5ec29b62 vocab=0bf1d20c
-/
theorem solution
    {Y Z : Scheme.{u}} [IsIntegral Y] (f : Y ⟶ Z)
    (hred : _root_.IsReduced (Z.presheaf.stalk (f (genericPoint Y))))
    (hmax : ∀ z : Z, z ⤳ f (genericPoint Y) → z = f (genericPoint Y))
    (V : Z.Opens) (hV : f (genericPoint Y) ∈ V)
    (hgen : ∀ x : Y.functionField, ∃ a b : Γ(Z, V),
      Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V b) ≠ 0 ∧
        x * Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V b) =
          Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V a)) :
    IsIso (f.stalkMap (genericPoint Y)) := by
  classical

  have hsurj : Function.Surjective (f.stalkMap (genericPoint Y)) :=
    AlgebraicGeometry.Scheme.Hom.stalkMap_genericPoint_surjective_of_forall_exists_div f V hV hgen

  set ζ : Z := f (genericPoint Y) with hζ
  obtain ⟨U, hU, hζU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (x := ζ) (U := ⊤) trivial
  letI := Z.presheaf.algebra_section_stalk (⟨ζ, hζU⟩ : U)
  let 𝔭 : Ideal Γ(Z, U) := (hU.primeIdealOf ⟨ζ, hζU⟩).asIdeal
  haveI : IsLocalization.AtPrime (Z.presheaf.stalk ζ) 𝔭 := hU.isLocalization_stalk ⟨ζ, hζU⟩

  have hprime : ∀ Q : Ideal (Z.presheaf.stalk ζ), Q.IsPrime → Q = IsLocalRing.maximalIdeal _ := by
    intro Q hQ
    let 𝔮 : Ideal Γ(Z, U) := Q.comap (algebraMap Γ(Z, U) (Z.presheaf.stalk ζ))
    haveI : 𝔮.IsPrime := Ideal.comap_isPrime _ Q
    have h𝔮𝔭 : 𝔮 ≤ 𝔭 := by
      have h1 : Q ≤ IsLocalRing.maximalIdeal _ := IsLocalRing.le_maximalIdeal hQ.ne_top
      have h2 := Ideal.comap_mono (f := algebraMap Γ(Z, U) (Z.presheaf.stalk ζ)) h1
      exact h2.trans (IsLocalization.AtPrime.under_maximalIdeal (Z.presheaf.stalk ζ) 𝔭).le

    let y : PrimeSpectrum Γ(Z, U) := ⟨𝔮, inferInstance⟩
    have hy : hU.fromSpec y ⤳ ζ := by
      have h1 : y ⤳ hU.primeIdealOf ⟨ζ, hζU⟩ := (PrimeSpectrum.le_iff_specializes _ _).mp h𝔮𝔭
      have h2 := h1.map hU.fromSpec.base.hom.continuous
      rwa [show hU.fromSpec.base.hom (hU.primeIdealOf ⟨ζ, hζU⟩) = ζ from hU.fromSpec_primeIdealOf ⟨ζ, hζU⟩] at h2
    have hyζ : hU.fromSpec y = ζ := hmax _ hy
    have h𝔮eq : 𝔮 = 𝔭 := by
      have hinj : Function.Injective hU.fromSpec := hU.fromSpec.isOpenEmbedding.injective
      have : y = hU.primeIdealOf ⟨ζ, hζU⟩ := by
        apply hinj
        rw [hyζ]
        exact (hU.fromSpec_primeIdealOf ⟨ζ, hζU⟩).symm
      exact congrArg PrimeSpectrum.asIdeal this
    calc Q = Ideal.map (algebraMap Γ(Z, U) (Z.presheaf.stalk ζ)) 𝔮 :=
          (IsLocalization.map_under 𝔭.primeCompl (Z.presheaf.stalk ζ) Q).symm
      _ = IsLocalRing.maximalIdeal _ := by rw [h𝔮eq]; exact IsLocalization.AtPrime.map_eq_maximalIdeal 𝔭 _

  have hmax0 : IsLocalRing.maximalIdeal (Z.presheaf.stalk ζ) = ⊥ := by
    haveI := hred
    have hle : IsLocalRing.maximalIdeal (Z.presheaf.stalk ζ) ≤ _root_.nilradical (Z.presheaf.stalk ζ) := by
      rw [_root_.nilradical_eq_sInf]
      exact le_sInf fun Q hQ => (hprime Q hQ).ge
    rwa [_root_.nilradical_eq_zero, Ideal.zero_eq_bot, le_bot_iff] at hle
  have hinj : Function.Injective (f.stalkMap (genericPoint Y)) := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff, ← hmax0]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _)
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩
