import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_NodeDescent
import Tengoku.FltAnthropic.Theorems.Thm_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing

set_option autoImplicit false

namespace ModularCurve
open _root_.ModularCurve
namespace NodeLocalized
export _root_.ModularCurve.NodeLocalized (coeffSubring)
open _root_.ModularCurve.NodeLocalized

noncomputable section

namespace CoeffDVR

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))

theorem mem_coeffSubring {x : AlgebraicClosure ℚ} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K :=
  Iff.rfl

def coeffSubringEquiv :
    coeffSubring A K ≃+* A.comap (algebraMap K (AlgebraicClosure ℚ)) where
  toFun x := ⟨⟨(x : AlgebraicClosure ℚ), ((mem_coeffSubring A K).mp x.2).2⟩,
    ((mem_coeffSubring A K).mp x.2).1⟩
  invFun v := ⟨((v : K) : AlgebraicClosure ℚ), (mem_coeffSubring A K).mpr ⟨v.2, (v : K).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem mem_of_isIntegral_int {x : AlgebraicClosure ℚ} (hx : IsIntegral ℤ x) : x ∈ A := by
  have hA : IsIntegral A x := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map (Int.castRingHom A), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap A (AlgebraicClosure ℚ)).comp (Int.castRingHom A)) (algebraMap ℤ _)]
    exact hpx
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := AlgebraicClosure ℚ)).mp hA
  rw [← hz]
  exact z.2

theorem algebraMap_ringOfIntegers_mem [NumberField K] (r : NumberField.RingOfIntegers K) :
    algebraMap (NumberField.RingOfIntegers K) K r ∈ A.comap (algebraMap K (AlgebraicClosure ℚ)) := by
  rw [ValuationSubring.mem_comap]
  have hint : IsIntegral ℤ (algebraMap (NumberField.RingOfIntegers K) K r) :=
    NumberField.RingOfIntegers.isIntegral_coe r
  apply mem_of_isIntegral_int A
  obtain ⟨p, hp, hpr⟩ := hint
  refine ⟨p, hp, ?_⟩
  have h := congrArg (algebraMap K (AlgebraicClosure ℚ)) hpr
  rw [map_zero, Polynomial.hom_eval₂,
    RingHom.ext_int (RingHom.comp _ _) (algebraMap ℤ (AlgebraicClosure ℚ))] at h
  exact h

end CoeffDVR

end

end NodeLocalized
end ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing.ModularCurve _root_.ModularCurve.NodeLocalized _root_.P2MW.S_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing.ModularCurve.NodeLocalized ModularCurve.NodeLocalized.CoeffDVR in
theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] :
    coeffSubring A K = K.toSubalgebra.toSubring ∨ IsDiscreteValuationRing ↥(coeffSubring A K) := by
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  haveI : NumberField K := NumberField.mk
  by_cases hV : A.comap (algebraMap K (AlgebraicClosure ℚ)) = ⊤
  ·
    left
    refine Subring.ext fun x => ⟨fun hx => hx.2, fun hxK => ⟨?_, hxK⟩⟩
    have : (⟨x, hxK⟩ : K) ∈ A.comap (algebraMap K (AlgebraicClosure ℚ)) := by
      rw [hV]; exact ValuationSubring.mem_top _
    exact this
  · right
    obtain ⟨v, hv, -⟩ :=
      ValuationSubring.exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem
        (A.comap (algebraMap K (AlgebraicClosure ℚ))) (algebraMap_ringOfIntegers_mem A K) hV
    have hdvr : IsDiscreteValuationRing (A.comap (algebraMap K (AlgebraicClosure ℚ))) := by
      rw [hv]

      haveI : IsLocalization.AtPrime (↥(v.valuationSubringAtPrime K)) v.asIdeal :=
        Localization.subalgebra.isLocalization_ofField K v.asIdeal.primeCompl
          v.asIdeal.primeCompl_le_nonZeroDivisors
      exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
        (NumberField.RingOfIntegers K) v.ne_bot _

    let e := (coeffSubringEquiv A K).symm
    haveI : IsPrincipalIdealRing ↥(coeffSubring A K) :=
      IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective
    haveI : IsLocalRing ↥(coeffSubring A K) := IsLocalRing.of_surjective' e.toRingHom e.surjective
    refine ⟨fun h => ?_⟩
    apply IsDiscreteValuationRing.not_a_field (A.comap (algebraMap K (AlgebraicClosure ℚ)))
    exact (IsLocalRing.isField_iff_maximalIdeal_eq).mp
      (MulEquiv.isField ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h) e.toMulEquiv)
