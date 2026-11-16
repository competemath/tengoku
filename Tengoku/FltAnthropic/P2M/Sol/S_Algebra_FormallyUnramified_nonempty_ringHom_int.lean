import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_NumberField_finrank_eq_one_of_forall_isUnramifiedAt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_FormallyUnramified_nonempty_ringHom_int.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_FormallyUnramified_nonempty_ringHom_int

set_option autoImplicit false

open scoped NumberField nonZeroDivisors

namespace Algebra export _root_.Algebra (mk algebraMap FormallyUnramified FormallyUnramified.comp algebraMapSubmonoid botEquiv formallyUnramified_iff_forall FormallyUnramified.of_equiv IsAlgebraic.extendScalars) namespace FormallyUnramified export _root_.Algebra.FormallyUnramified (quotient of_surjective comp of_isLocalization of_equiv mk) end Algebra.FormallyUnramified
open scoped _root_.Algebra _root_.Algebra.FormallyUnramified in

private theorem Algebra.FormallyUnramified.nonempty_ringEquiv_int_of_isDomain
    (D K : Type*) [CommRing D] [IsDomain D] [CharZero D] [Module.Finite ℤ D]
    [Algebra.FormallyUnramified ℤ D] [Field K] [Algebra D K] [IsFractionRing D K] :
    Nonempty (D ≃+* ℤ) := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective D K)
  haveI : IsDedekindDomain D := IsDedekindDomain.of_formallyUnramified ℤ D
  haveI : IsIntegralClosure D ℤ K := IsIntegralClosure.of_isIntegrallyClosed D ℤ K
  haveI : Algebra.IsAlgebraic ℤ K := (IsFractionRing.isAlgebraic_iff' ℤ D K).mp inferInstance
  haveI : Algebra.IsAlgebraic ℚ K :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ) (algebraMap ℤ ℚ).injective_int
  haveI : IsLocalization (Algebra.algebraMapSubmonoid D ℤ⁰) K :=
    IsIntegralClosure.isLocalization ℤ ℚ K D
  haveI : Module.Finite ℚ K := Module.Finite.of_isLocalization ℤ D ℤ⁰
  haveI : NumberField K := NumberField.mk

  let e : 𝓞 K ≃+* D := NumberField.RingOfIntegers.equiv D
  haveI : Algebra.FormallyUnramified ℤ (𝓞 K) :=
    Algebra.FormallyUnramified.of_equiv (AlgEquiv.ofRingEquiv (f := e.symm) (fun n => by simp))

  have hK : Module.finrank ℚ K = 1 :=
    NumberField.finrank_eq_one_of_forall_isUnramifiedAt K (fun P _ =>
      (Algebra.formallyUnramified_iff_forall (R := ℤ) (A := 𝓞 K)).mp inferInstance
        ⟨P, inferInstance⟩)
  have hbot : (⊥ : Subalgebra ℚ K) = ⊤ := Subalgebra.bot_eq_top_iff_finrank_eq_one.mpr hK
  let gK : K ≃ₐ[ℚ] ℚ :=
    (Subalgebra.topEquiv (R := ℚ) (A := K)).symm.trans
      ((Subalgebra.equivOfEq _ _ hbot.symm).trans (Algebra.botEquiv ℚ K))
  exact ⟨e.symm.trans
    ((NumberField.RingOfIntegers.mapRingEquiv gK.toRingEquiv).trans Rat.ringOfIntegersEquiv)⟩

theorem solution
    (B : Type*) [CommRing B] [Nontrivial B] [Module.Finite ℤ B] [Module.Flat ℤ B]
    [Algebra.FormallyUnramified ℤ B] : Nonempty (B →+* ℤ) := by
  classical

  obtain ⟨Q, -, hQp, hQ⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := ℤ) (S := B) (⊥ : Ideal ℤ) (⊥ : Ideal B)
      (by rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ B)])

  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : Module.Finite ℤ (B ⧸ Q) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ Q).toLinearMap (Ideal.Quotient.mkₐ_surjective ℤ Q)

  haveI : @Algebra.FormallyUnramified ℤ (B ⧸ Q) _ _ (Ring.toIntAlgebra _) :=
    (Subsingleton.elim (Ideal.instAlgebraQuotient ℤ Q : Algebra ℤ (B ⧸ Q)) (Ring.toIntAlgebra _)) ▸
      Algebra.FormallyUnramified.comp ℤ B (B ⧸ Q)
  have hinj : Function.Injective (algebraMap ℤ (B ⧸ Q)) := by
    rw [RingHom.injective_iff_ker_eq_bot, IsScalarTower.algebraMap_eq ℤ B (B ⧸ Q),
      ← RingHom.comap_ker, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    exact hQ
  haveI : CharZero (B ⧸ Q) := charZero_of_injective_algebraMap hinj
  obtain ⟨e⟩ := Algebra.FormallyUnramified.nonempty_ringEquiv_int_of_isDomain (B ⧸ Q)
    (FractionRing (B ⧸ Q))
  exact ⟨e.toRingHom.comp (Ideal.Quotient.mk Q)⟩
