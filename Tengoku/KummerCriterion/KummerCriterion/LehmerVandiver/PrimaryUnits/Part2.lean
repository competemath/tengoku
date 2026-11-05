module

public import Tengoku.KummerCriterion.KummerCriterion.LehmerVandiver.PrimaryUnits.Part1
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

section CyclotomicUnits

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- `cyclotomicUnit p K p = 0`, since `∑_{j=0}^{p-1} ζ^j = 0`
(cyclotomic identity).-/
theorem cyclotomicUnit_p_eq_zero : cyclotomicUnit p K p = 0 :=
  (zeta_spec p ℚ K).unit'_coe.geom_sum_eq_zero
    (Nat.lt_of_lt_of_le one_lt_two hp.1.two_le)

/-- `cyclotomicUnit p K (p - 1) = -ζ^{p-1}`.-/
theorem cyclotomicUnit_p_sub_one :
    cyclotomicUnit p K (p - 1) = -((zeta_spec p ℚ K).unit' : 𝓞 K) ^ (p - 1) := by
  have hp_pos : 1 ≤ p := hp.1.pos
  have hp_eq : (p - 1) + 1 = p := Nat.sub_add_cancel hp_pos
  have key : cyclotomicUnit p K (p - 1) +
      ((zeta_spec p ℚ K).unit' : 𝓞 K) ^ (p - 1) = 0 := by
    have hrec := cyclotomicUnit_succ p K (p - 1)
    rw [hp_eq] at hrec
    rw [← hrec, cyclotomicUnit_p_eq_zero]
  linear_combination key

end CyclotomicUnits

section RealCyclotomicUnits

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The real cyclotomic combination
`(cyclotomicUnit k) · σ(cyclotomicUnit k)` in `𝓞 K`. This is
automatically `σ`-fixed and corresponds to the K⁺-side cyclotomic
unit `(1 - ζ^k)(1 - ζ^{-k})/((1 - ζ)(1 - ζ^{-1}))`.-/
noncomputable def realCyclotomicUnit [IsCMField K] (k : ℕ) : 𝓞 K :=
  cyclotomicUnit p K k * ringOfIntegersComplexConj K (cyclotomicUnit p K k)

/-- The real cyclotomic combination is fixed by complex conjugation.-/
theorem realCyclotomicUnit_complexConj [IsCMField K] (k : ℕ) :
    ringOfIntegersComplexConj K (realCyclotomicUnit p K k) =
      realCyclotomicUnit p K k := by
  unfold realCyclotomicUnit
  rw [map_mul]
  rw [show ringOfIntegersComplexConj K
        (ringOfIntegersComplexConj K (cyclotomicUnit p K k)) =
      cyclotomicUnit p K k from by
    apply RingOfIntegers.ext
    simp]
  ring

/-- `realCyclotomicUnit k ≡ k² (mod ζ - 1)` in `𝓞 K`.-/
theorem zetaSubOne_dvd_realCyclotomicUnit_sub_sq [IsCMField K] (k : ℕ) :
    ((zeta_spec p ℚ K).unit' : 𝓞 K) - 1 ∣
      realCyclotomicUnit p K k - (k : 𝓞 K) ^ 2 := by
  have h_diff : realCyclotomicUnit p K k - (k : 𝓞 K) ^ 2 =
      cyclotomicUnit p K k *
        (ringOfIntegersComplexConj K (cyclotomicUnit p K k) - (k : 𝓞 K)) +
      (k : 𝓞 K) * (cyclotomicUnit p K k - (k : 𝓞 K)) := by
    change cyclotomicUnit p K k * ringOfIntegersComplexConj K (cyclotomicUnit p K k)
        - (k : 𝓞 K) ^ 2 = _
    ring
  rw [h_diff]
  exact dvd_add
    ((zetaSubOne_dvd_complexConj_cyclotomicUnit_sub_natCast p K k).mul_left _)
    ((zetaSubOne_dvd_cyclotomicUnit_sub_natCast p K k).mul_left _)

/-- The real cyclotomic combination is a unit when `k` is coprime to `p`.-/
theorem isUnit_realCyclotomicUnit [IsCMField K] (k : ℕ) (hk : k.Coprime p)
    (hp_two : 2 ≤ p) :
    IsUnit (realCyclotomicUnit p K k) := by
  unfold realCyclotomicUnit
  exact (isUnit_cyclotomicUnit p K k hk hp_two).mul
    ((isUnit_cyclotomicUnit p K k hk hp_two).map
      (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)

end RealCyclotomicUnits
end PrimaryPlus
end LehmerVandiver

end KummerCriterion

end
