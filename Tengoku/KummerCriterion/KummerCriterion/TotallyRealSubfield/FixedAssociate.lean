module

public import Tengoku.KummerCriterion.KummerCriterion.PrimitiveRootUnits
import Tengoku.Seed.NumberTheory.NumberField.Cyclotomic.Ideal
import Tengoku.KummerCriterion.KummerCriterion.TotallyRealSubfield.Conjugation
public import Tengoku.Seed.NumberTheory.NumberField.CMField

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fixed-associate descent

This file removes the residual root-of-unity twist and produces
conjugation-fixed generators that descend to `𝒪_{K⁺}`.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField Algebra IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace KummerCriterion

section CyclotomicSetup

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

include hp_odd in
/-- Twisting by a suitable square root yields a conjugation-fixed associate.
@isnad1 id=ex.4h4v.s10.604a4d1a66e3 from=translated src=- shape=073eac3c vocab=7685450d
-/
theorem exists_conj_fixed_associate_of_zeta_pow [IsCMField K]
    {hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p}
    (a : 𝓞 K) (u : (𝓞 K)ˣ)
    (hu : ringOfIntegersComplexConj K a = u * a)
    (hclass : ∃ n : ℕ, u = hζ.unit' ^ n) :
    ∃ b : 𝓞 K, ringOfIntegersComplexConj K b = b ∧ Ideal.span {b} = Ideal.span {a} := by
  have hpo : Odd p := hp.1.odd_of_ne_two hp_odd
  obtain ⟨n, rfl⟩ := hclass
  obtain ⟨m, hm⟩ := exists_pow_eq_pow_two_mul hζ.unit'_pow hpo n
  let μ : (𝓞 K)ˣ := hζ.unit' ^ m
  have hμsq : (hζ.unit' ^ n : (𝓞 K)ˣ) = μ ^ 2 := by
    dsimp [μ]
    calc
      (hζ.unit' ^ n : (𝓞 K)ˣ) = hζ.unit' ^ (2 * m) := hm
      _ = (hζ.unit' ^ m) ^ 2 := by simp [pow_mul, mul_comm]
  let b : 𝓞 K := a * (μ : (𝓞 K)ˣ)
  refine ⟨b, ?_, ?_⟩
  · have hμconj : complexConj K μ = (μ⁻¹ : (𝓞 K)ˣ) := by
      dsimp [μ]
      simpa using conj_zeta_pow (p := p) (K := K) (hζ := hζ) m
    have hμcoe :
        ringOfIntegersComplexConj K ((μ : (𝓞 K)ˣ) : 𝓞 K) =
          ((μ⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
      apply RingOfIntegers.ext
      simpa [coe_ringOfIntegersComplexConj] using hμconj
    have huμinv : (hζ.unit' ^ n : (𝓞 K)ˣ) * μ⁻¹ = μ := by
      rw [hμsq]
      simp [pow_two, mul_assoc]
    calc
      ringOfIntegersComplexConj K b =
          ringOfIntegersComplexConj K a *
            ringOfIntegersComplexConj K ((μ : (𝓞 K)ˣ) : 𝓞 K) := by
            dsimp [b]
            simp
      _ = ((hζ.unit' ^ n : (𝓞 K)ˣ) : 𝓞 K) * a * (((μ⁻¹ : (𝓞 K)ˣ)) : 𝓞 K) := by
            dsimp [b]
            simpa [mul_assoc, hμcoe] using congrArg
              (fun x : 𝓞 K =>
                x * ringOfIntegersComplexConj K (((μ : (𝓞 K)ˣ) : 𝓞 K))) hu
      _ =
          ((((hζ.unit' ^ n : (𝓞 K)ˣ) * μ⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * a) := by
            simp [mul_assoc, mul_comm]
      _ = (μ : (𝓞 K)ˣ) * a := by rw [huμinv]
      _ = b := by dsimp [b]; simp [mul_comm]
  · rw [Ideal.span_singleton_eq_span_singleton]
    dsimp [b]
    exact (associated_mul_unit_right a (μ : (𝓞 K)ˣ) μ.isUnit).symm

/-- If `b` is fixed by conjugation, then it comes from `𝒪_{K⁺}`.
@isnad1 id=mem.1h2v.s10.9c6b04f22b46 from=translated src=- shape=cc103372 vocab=484ab035
-/
theorem mem_ringOfIntegers_of_conj_eq_self [IsCMField K]
    (b : 𝓞 K) (hb : ringOfIntegersComplexConj K b = b) :
    b ∈ Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :=
  (ringOfIntegersComplexConj_eq_self_iff K b).mp hb

end CyclotomicSetup

end KummerCriterion

end
