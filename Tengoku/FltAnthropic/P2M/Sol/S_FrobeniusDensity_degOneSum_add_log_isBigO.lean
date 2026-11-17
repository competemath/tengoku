import Tengoku.FltAnthropic.Theorems.Thm_FrobeniusDensity_primeSum_toReal_add_log_isBigO
import Tengoku.FltAnthropic.Theorems.Thm_FrobeniusDensity_idealSum_ne_top
import Tengoku.FltAnthropic.Theorems.Thm_FrobeniusDensity_primeSum_eq_degOneSum_add
import Tengoku.FltAnthropic.Definitions.Def_FrobeniusDensity_PrimeSums
import Tengoku.Seed.NumberTheory.RamificationInertia.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FrobeniusDensity_degOneSum_add_log_isBigO.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 3 `p2m_open`, 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FrobeniusDensity_degOneSum_add_log_isBigO

set_option autoImplicit false

open _root_.Ideal open _root_.NumberField open _root_.Filter open _root_.Topology open _root_.Asymptotics open _root_.IsDedekindDomain open _root_.Ideal.IsDedekindDomain
open scoped ENNReal

namespace FrobeniusDensity
export _root_.FrobeniusDensity (primeSum_toReal_add_log_isBigO normRpow idealSum primeSum one_le_absNorm ratBelow ratBelow_prime liesOver_ratBelow degOneSum cutSum tailSum tailConst degOneCount_of_not_prime degOneCount ratPrimeIdeal ratPrimeIdeal_ne_bot idealSum_ne_top primeSum_eq_degOneSum_add)
open _root_.FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]
variable {K}

variable (K)

private lemma primeSum_le_idealSum (s : ℝ) : primeSum K s ≤ idealSum K s := by
  have hinj : Function.Injective
      (fun v : HeightOneSpectrum (𝓞 K) =>
        (⟨v.asIdeal, v.ne_bot⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥})) :=
    fun v w h => HeightOneSpectrum.ext (by simpa using congrArg Subtype.val h)
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj fun I => normRpow K s I.1

private lemma primeSum_ne_top {s : ℝ} (hs : 1 < s) : primeSum K s ≠ ⊤ :=
  ((primeSum_le_idealSum K s).trans_lt (idealSum_ne_top K hs).lt_top).ne

private lemma degOneSum_ne_top (S₀ : Finset ℕ) {s : ℝ} (hs : 1 < s) :
    degOneSum K S₀ s ≠ ⊤ := by
  have h1 : degOneSum K S₀ s ≤ primeSum K s := by
    rw [primeSum_eq_degOneSum_add K S₀ s, add_assoc]
    exact self_le_add_right _ _
  exact (h1.trans_lt (primeSum_ne_top K hs).lt_top).ne

private def RatBelowFiber (ℓ : ℕ) : Type _ :=
  {v : HeightOneSpectrum (𝓞 K) // ratBelow v = ℓ}

private theorem liesOver_of_ratBelow_eq {v : HeightOneSpectrum (𝓞 K)} {ℓ : ℕ}
    (h : ratBelow v = ℓ) : v.asIdeal.LiesOver (ratPrimeIdeal ℓ) :=
  h ▸ liesOver_ratBelow v

private theorem isEmpty_ratBelowFiber {ℓ : ℕ} (hℓ : ¬ ℓ.Prime) :
    IsEmpty (RatBelowFiber K ℓ) :=
  ⟨fun v => hℓ (v.2 ▸ ratBelow_prime v.1)⟩

private scoped instance (ℓ : ℕ) : Finite (RatBelowFiber K ℓ) := by
  by_cases hℓ : ℓ.Prime
  · have : Fact ℓ.Prime := ⟨hℓ⟩
    have hinj : Function.Injective (fun (v : RatBelowFiber K ℓ) =>
        (⟨v.1.asIdeal, v.1.isPrime, liesOver_of_ratBelow_eq K v.2⟩ :
          ((ratPrimeIdeal ℓ).primesOver (𝓞 K) : Set (Ideal (𝓞 K))))) :=
      fun v w h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
    have hfin : Finite ((ratPrimeIdeal ℓ).primesOver (𝓞 K) : Set (Ideal (𝓞 K))) := by
      rw [← IsDedekindDomain.coe_primesOverFinset (ratPrimeIdeal_ne_bot hℓ) (𝓞 K)]
      exact (IsDedekindDomain.primesOverFinset (ratPrimeIdeal ℓ) (𝓞 K)).finite_toSet.to_subtype
    exact Finite.of_injective _ hinj
  · have := isEmpty_ratBelowFiber K hℓ
    infer_instance

omit [NumberField K] in
private theorem toReal_term (S₀ : Finset ℕ) (s : ℝ) (ℓ : ℕ) :
    ((if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ≥0∞)) * (ℓ : ℝ≥0∞) ^ (-s)).toReal
      = (if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) := by
  rw [ENNReal.toReal_mul, apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ENNReal.toReal_natCast, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast]

end FrobeniusDensity
open scoped _root_.P2MW.S_FrobeniusDensity_degOneSum_add_log_isBigO.FrobeniusDensity

open _root_.FrobeniusDensity open _root_.P2MW.S_FrobeniusDensity_degOneSum_add_log_isBigO.FrobeniusDensity
