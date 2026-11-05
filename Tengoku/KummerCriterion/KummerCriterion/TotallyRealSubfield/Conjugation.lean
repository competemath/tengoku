module

public import Tengoku.KummerCriterion.KummerCriterion.TotallyRealSubfield.ZetaPrime
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Conjugation and unit classification

This file packages the conjugation-equivariance lemmas and the unit
classification used to remove the possible `-1` factor in the descent.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace KummerCriterion

section CyclotomicSetup

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- Complex conjugation sends a principal ideal to the principal ideal of the
conjugated generator.
@isnad1 id=eq.0h2v.s9.7d5e2968d29a from=translated src=- shape=c35559f0 vocab=79ac715c
-/
theorem conj_map_span_singleton [IsCMField K] (a : 𝓞 K) :
    (Ideal.span {a}).map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      Ideal.span {ringOfIntegersComplexConj K a} := by
  simpa using
    (Ideal.map_span ((ringOfIntegersComplexConj K).toRingEquiv.toRingHom) ({a} : Set (𝓞 K)))

/-- Complex conjugation acts trivially on ideals extended from `𝒪_{K⁺}`.
@isnad1 id=eq.0h2v.s10.2b7a35a77137 from=translated src=- shape=85b298bb vocab=17c9d3ef
-/
theorem ideal_map_conj_eq [IsCMField K]
    (I : Ideal (𝓞 (NumberField.maximalRealSubfield K))) :
    (I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))).map
        (ringOfIntegersComplexConj K).toRingEquiv.toRingHom =
      I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) := by
  rw [Ideal.map_map]
  congr
  ext x
  simp [RingHom.comp_apply, AlgEquiv.commutes]

/-- If `(a) = (c(a))`, then `c(a)` differs from `a` by a unit.
@isnad1 id=ex.3h3v.s11.b9a90090ed6c from=translated src=- shape=cf65c3d6 vocab=80686c1f
-/
theorem conj_generator_associated [IsCMField K]
    (a : 𝓞 K) (_ha : a ≠ 0) (I : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (hIa : I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = Ideal.span {a})
    (hIca : I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      Ideal.span {ringOfIntegersComplexConj K a}) :
    ∃ u : (𝓞 K)ˣ, ringOfIntegersComplexConj K a = u * a := by
  let hspan : Ideal.span {a} = Ideal.span {ringOfIntegersComplexConj K a} := hIa.symm.trans hIca
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨u, ?_⟩
  simpa [mul_comm] using hu.symm

/-- If `c(a) = u a` with `a ≠ 0`, then `c(u) u = 1`.
@isnad1 id=eq.2h3v.s10.3bf0cebfa1f8 from=translated src=- shape=750a632d vocab=2f07d183
-/
theorem conj_unit_mul_eq_one [IsCMField K]
    (a : 𝓞 K) (ha : a ≠ 0) (u : (𝓞 K)ˣ)
    (hu : ringOfIntegersComplexConj K a = u * a) :
    unitsComplexConj K u * u = 1 := by
  have hcc : ringOfIntegersComplexConj K (ringOfIntegersComplexConj K a) = a := by
    apply RingOfIntegers.ext
    simp [coe_ringOfIntegersComplexConj, complexConj_apply_apply]
  have hu1 : a = (unitsComplexConj K u : (𝓞 K)ˣ) * ringOfIntegersComplexConj K a := by
    simpa [hcc, unitsComplexConj, map_mul] using! congrArg (ringOfIntegersComplexConj K) hu
  rw [hu] at hu1
  have hu2 : a = (((unitsComplexConj K u * u : (𝓞 K)ˣ) : 𝓞 K) * a) := by
    simpa [mul_assoc] using hu1
  apply Units.ext
  apply mul_right_cancel₀ ha
  simpa [one_mul] using hu2.symm

/-- Complex conjugation sends `ζ^m` to `ζ^{-m}`.
@isnad1 id=eq.1h3v.s9.7e6b20ef9306 from=translated src=- shape=d6d29188 vocab=83399990
-/
theorem conj_zeta_pow [IsCMField K]
    {hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (m : ℕ) :
    complexConj K (hζ.unit' ^ m : (𝓞 K)ˣ) = ((hζ.unit' ^ m)⁻¹ : (𝓞 K)ˣ) := by
  have hzeta_torsion : hζ.unit' ∈ NumberField.Units.torsion K := by
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp.1.pos, ?_⟩)
    exact hζ.unit'_pow
  simpa using complexConj_torsion K
    ⟨hζ.unit' ^ m, (NumberField.Units.torsion K).pow_mem hzeta_torsion m⟩

end CyclotomicSetup

end KummerCriterion

end
