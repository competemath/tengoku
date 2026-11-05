module

public import Tengoku.KummerCriterion.KummerCriterion.LehmerVandiver.PrimaryUnits.Part2
import Tengoku.KummerCriterion.KummerCriterion.TotallyRealSubfield.ClassGroup
import Tengoku.Seed.Analysis.SpecialFunctions.Bernstein

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Primary units of `𝓞 K⁺`

For Vandiver Lemma 2 (primary unit decomposition), an element
`γ ∈ 𝓞 K⁺` is **primary** when it is congruent to a rational integer
modulo `𝔭⁺^p`, where `𝔭⁺` is the unique prime of `𝓞 K⁺` above `(p)`.
Equivalently (since `𝔭⁺·𝓞 K = 𝔭² = (ζ-1)^2`), this is
`γ ≡ a (mod (ζ-1)^{2p})` viewed in `𝓞 K`.

This file isolates the K⁺-side primary definition with basic API.

## References

* Washington, *Introduction to Cyclotomic Fields*, §6.4.
* Vandiver 1929, *Fermat's Last Theorem and the Second Factor in the
 Cyclotomic Class Number*.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField

namespace KummerCriterion

namespace LehmerVandiver

section PrimaryPlus

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

section RealCyclotomicUnits

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The real cyclotomic combination descends to `𝓞 K⁺`: there exists
`y ∈ 𝓞 K⁺` with `algebraMap y = realCyclotomicUnit p K k`.-/
theorem exists_realCyclotomicUnit_descent [IsCMField K] (k : ℕ) :
    ∃ y : 𝓞 (NumberField.maximalRealSubfield K),
      algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y =
      realCyclotomicUnit p K k :=
  (ringOfIntegersComplexConj_eq_self_iff K (realCyclotomicUnit p K k)).mp
    (realCyclotomicUnit_complexConj p K k)

/-- The K⁺-side real cyclotomic unit: a chosen lift of
`realCyclotomicUnit p K k` to `𝓞 K⁺`.-/
noncomputable def realCyclotomicUnitPlus [IsCMField K] (k : ℕ) :
    𝓞 (NumberField.maximalRealSubfield K) :=
  (exists_realCyclotomicUnit_descent p K k).choose

/-- `algebraMap (realCyclotomicUnitPlus p K k) = realCyclotomicUnit p K k`.-/
theorem algebraMap_realCyclotomicUnitPlus [IsCMField K] (k : ℕ) :
    algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (realCyclotomicUnitPlus p K k) =
      realCyclotomicUnit p K k :=
  (exists_realCyclotomicUnit_descent p K k).choose_spec

/-- The K⁺-side real cyclotomic unit is itself a unit when `k` is coprime
to `p`.-/
theorem isUnit_realCyclotomicUnitPlus [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    IsUnit (realCyclotomicUnitPlus p K k) := by
  have h_unit : IsUnit (realCyclotomicUnit p K k) :=
    isUnit_realCyclotomicUnit p K k hk hp_two
  rw [← algebraMap_realCyclotomicUnitPlus p K k] at h_unit
  have h_norm_unit : IsUnit (RingOfIntegers.norm (NumberField.maximalRealSubfield K)
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
        (realCyclotomicUnitPlus p K k))) :=
    h_unit.map _
  rw [RingOfIntegers.norm_algebraMap] at h_norm_unit
  have hfin_ne : Module.finrank (NumberField.maximalRealSubfield K) K ≠ 0 := by
    rw [finrank_K_over_Kplus]
    decide
  exact (isUnit_pow_iff hfin_ne).mp h_norm_unit

/-- The K⁺-side real cyclotomic unit, packaged as an element of
`(𝓞 K⁺)ˣ` when `k` is coprime to `p`.-/
noncomputable def realCyclotomicUnitPlusUnit [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (𝓞 (NumberField.maximalRealSubfield K))ˣ :=
  (isUnit_realCyclotomicUnitPlus p K k hk hp_two).unit

@[simp]
theorem realCyclotomicUnitPlusUnit_val [IsCMField K] (k : ℕ)
    (hk : k.Coprime p) (hp_two : 2 ≤ p) :
    (realCyclotomicUnitPlusUnit p K k hk hp_two : 𝓞 (NumberField.maximalRealSubfield K)) =
      realCyclotomicUnitPlus p K k :=
  IsUnit.unit_spec _

end RealCyclotomicUnits

end PrimaryPlus

end LehmerVandiver

end KummerCriterion

end
