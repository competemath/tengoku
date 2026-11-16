import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.Seed.NumberTheory.NumberField.Basic
import Tengoku.Seed.RingTheory.DedekindDomain.SelmerGroup
import Tengoku.Seed.RingTheory.Invariant.Profinite
import Tengoku.Seed.NumberTheory.RamificationInertia.Basic
import Tengoku.Seed.RingTheory.DedekindDomain.AdicValuation
import Tengoku.Seed.RingTheory.DedekindDomain.Dvr
import Tengoku.Seed.RingTheory.Localization.AsSubring
import Tengoku.Seed.FieldTheory.Galois.Profinite
import Tengoku.Seed.FieldTheory.Galois.Infinite
import Tengoku.Seed.FieldTheory.Extension
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.RingTheory.Ideal.GoingUp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ValuationSubring_exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation

open NumberField IsDedekindDomain

set_option autoImplicit false

open NumberField IsDedekindDomain IntermediateField

open scoped Pointwise

namespace WtTF
namespace RB

local notation "ℚ̄" => AlgebraicClosure ℚ

/--
@isnad1 id=isalgebr.0h0v.s4.92f995461263 from=translated src=- shape=3905abf2 vocab=c7f7e443
-/
theorem isAlgebraic_rat_qbar : Algebra.IsAlgebraic ℚ ℚ̄ := by
  constructor
  intro x
  obtain ⟨p, hp0, hp⟩ := (AlgebraicClosure.isAlgebraic (k := ℚ)).isAlgebraic x
  refine ⟨p, hp0, ?_⟩
  rw [Polynomial.aeval_def] at hp ⊢
  have : (algebraMap ℚ ℚ̄) = (AlgebraicClosure.instAlgebra ℚ).algebraMap := by
    refine RingHom.ext fun q => ?_
    rw [eq_ratCast, eq_ratCast]
  rw [this]
  exact hp

/--
@isnad1 id=isalgebr.0h1v.s6.69da508e6e7a from=translated src=- shape=363095d8 vocab=b8da9b0c
-/
theorem isAlgebraic_over (F : Type*) [Field F] [Algebra ℚ F] [Algebra F ℚ̄]
    [IsScalarTower ℚ F ℚ̄] : Algebra.IsAlgebraic F ℚ̄ := by
  haveI := isAlgebraic_rat_qbar
  exact Algebra.IsAlgebraic.tower_top (K := ℚ) F (A := ℚ̄)

/--
@isnad1 id=isgalois.0h1v.s6.64569d20167c from=translated src=- shape=363095d8 vocab=b9223a2f
-/
theorem isGalois_over (F : Type*) [Field F] [Algebra ℚ F] [Algebra F ℚ̄]
    [IsScalarTower ℚ F ℚ̄] : IsGalois F ℚ̄ := by
  haveI ha := isAlgebraic_over F
  haveI : IsAlgClosure F ℚ̄ := ⟨inferInstance, ha⟩
  haveI : Normal F ℚ̄ := IsAlgClosure.normal F ℚ̄
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  haveI : Algebra.IsIntegral F ℚ̄ := ha.isIntegral
  haveI : Algebra.IsSeparable F ℚ̄ := Algebra.IsSeparable.of_integral F ℚ̄
  constructor

/--
@isnad1 id=eq.0h3v.s10.476ec042fe93 from=translated src=- shape=ecaed359 vocab=4c6a950f
-/
theorem coe_galSmul {F : Type*} [Field F] [Algebra F ℚ̄] (g : ℚ̄ ≃ₐ[F] ℚ̄) (b : 𝓞 ℚ̄) :
    ((g • b : 𝓞 ℚ̄) : ℚ̄) = g (b : ℚ̄) := rfl

/--
@isnad1 id=eq.0h3v.s7.e724bdfc4cdd from=translated src=- shape=014cf703 vocab=5b170a42
-/
theorem coe_ringOfIntegersMap {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra F₁ F₂] (c : 𝓞 F₁) :
    ((algebraMap (𝓞 F₁) (𝓞 F₂) c : 𝓞 F₂) : F₂) = algebraMap F₁ F₂ (c : F₁) := by
  rw [show ((algebraMap (𝓞 F₁) (𝓞 F₂) c : 𝓞 F₂) : F₂) =
      algebraMap (𝓞 F₂) F₂ (algebraMap (𝓞 F₁) (𝓞 F₂) c) from rfl,
    ← IsScalarTower.algebraMap_apply (𝓞 F₁) (𝓞 F₂) F₂,
    IsScalarTower.algebraMap_apply (𝓞 F₁) F₁ F₂]

/--
@isnad1 id=smulcomm.0h1v.s9.853c85e51575 from=translated src=- shape=0938f49d vocab=c4bc71bc
-/
scoped instance smulCommClass_gal {F : Type*} [Field F] [Algebra F ℚ̄] :
    SMulCommClass (ℚ̄ ≃ₐ[F] ℚ̄) (𝓞 F) (𝓞 ℚ̄) := by
  constructor
  intro g a b
  apply NumberField.RingOfIntegers.ext
  have hcoe : ∀ z : 𝓞 ℚ̄, ∀ c : 𝓞 F,
      ((c • z : 𝓞 ℚ̄) : ℚ̄) = algebraMap F ℚ̄ (c : F) * (z : ℚ̄) := by
    intro z c
    rw [Algebra.smul_def,
      show ((algebraMap (𝓞 F) (𝓞 ℚ̄) c * z : 𝓞 ℚ̄) : ℚ̄) =
        algebraMap (𝓞 ℚ̄) ℚ̄ (algebraMap (𝓞 F) (𝓞 ℚ̄) c) * algebraMap (𝓞 ℚ̄) ℚ̄ z from
      map_mul (algebraMap (𝓞 ℚ̄) ℚ̄) _ _,
      show algebraMap (𝓞 ℚ̄) ℚ̄ (algebraMap (𝓞 F) (𝓞 ℚ̄) c) = algebraMap F ℚ̄ (c : F) from
      coe_ringOfIntegersMap c]
  rw [coe_galSmul, hcoe, hcoe, map_mul, coe_galSmul]
  congr 1
  exact g.commutes (a : F)

/--
@isnad1 id=isinvari.0h1v.s8.cca68f82935a from=translated src=- shape=49138091 vocab=ef0f3a68
-/
theorem isInvariant_gal (F : Type*) [Field F] [Algebra ℚ F] [Algebra F ℚ̄]
    [IsScalarTower ℚ F ℚ̄] :
    Algebra.IsInvariant (𝓞 F) (𝓞 ℚ̄) (ℚ̄ ≃ₐ[F] ℚ̄) := by
  haveI := isGalois_over F
  constructor
  intro b hb
  have hmem : (b : ℚ̄) ∈ (⊥ : IntermediateField F ℚ̄) := by
    rw [InfiniteGalois.mem_bot_iff_fixed]
    intro f
    have := congrArg (fun z : 𝓞 ℚ̄ => (z : ℚ̄)) (hb f)
    simpa [coe_galSmul] using this
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
  have hbint : IsIntegral ℤ (b : ℚ̄) := NumberField.RingOfIntegers.isIntegral_coe b
  have hcint : IsIntegral ℤ c := by
    obtain ⟨p, hmonic, hroot⟩ := hbint
    refine ⟨p, hmonic, ?_⟩
    apply (algebraMap F ℚ̄).injective
    have hcomp : (algebraMap F ℚ̄).comp (algebraMap ℤ F) = algebraMap ℤ ℚ̄ :=
      RingHom.ext fun n => by
        rw [RingHom.comp_apply, eq_intCast, eq_intCast, map_intCast]
    rw [map_zero, ← hroot, ← hc, Polynomial.hom_eval₂, hcomp]
  refine ⟨⟨c, hcint⟩, ?_⟩
  apply NumberField.RingOfIntegers.ext
  rw [coe_ringOfIntegersMap (⟨c, hcint⟩ : 𝓞 F)]
  exact hc

/--
@isnad1 id=isfracti.0h0v.s5.51f19996570e from=translated src=- shape=5f8c0c92 vocab=db1c106a
-/
scoped instance isFractionRing_ringOfIntegers_qbar : IsFractionRing (𝓞 ℚ̄) ℚ̄ := by
  haveI : Algebra.IsAlgebraic (𝓞 ℚ) ℚ̄ :=
    (IsFractionRing.comap_isAlgebraic_iff (A := 𝓞 ℚ) (K := ℚ) (C := ℚ̄)).mpr
      isAlgebraic_rat_qbar
  exact IsIntegralClosure.isFractionRing_of_algebraic (A := 𝓞 ℚ) (C := 𝓞 ℚ̄)
    (fun x hx => by
      rw [IsScalarTower.algebraMap_apply (𝓞 ℚ) ℚ ℚ̄] at hx
      have h2 : algebraMap (𝓞 ℚ) ℚ x = 0 :=
        (map_eq_zero_iff _ (algebraMap ℚ ℚ̄).injective).mp hx
      exact NumberField.RingOfIntegers.coe_injective (by rw [h2, map_zero]))

end RB
open scoped _root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.WtTF.RB

local notation "ℚ̄" => AlgebraicClosure ℚ

end WtTF
open scoped _root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.WtTF.RB _root_.P2MW.S_ValuationSubring_exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation.WtTF
