import Tengoku.Seed.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Tengoku.Seed.NumberTheory.Bernoulli
import Tengoku.Seed.Data.Rat.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_StarBank_eisInt_not_dvd_num.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_StarBank_eisInt_not_dvd_num

set_option autoImplicit false

open scoped ArithmeticFunction.sigma
open Finset

namespace ModularCurve
namespace W1

/--
@isnad1 id=not.1h1v.s5.8bbdcb471b56 from=translated src=- shape=27e1186b vocab=1da16793
-/
theorem eisInt_not_dvd_den_shift {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ¬ ℓ ∣ (bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)).den := by
  have hℓp : ℓ.Prime := Fact.out

  obtain ⟨m, hm⟩ := hℓp.odd_of_ne_two (by omega)
  set k₀ := (ℓ - 1) / 2 with hk₀def
  have h2k₀ : 2 * k₀ = ℓ - 1 := by omega

  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k₀

  rw [h2k₀] at hz
  have hrange : ℓ - 1 + 2 = ℓ + 1 := by omega
  rw [hrange] at hz

  set S := {p ∈ range (ℓ + 1) | p.Prime ∧ p - 1 ∣ ℓ - 1} with hSdef
  have hℓS : ℓ ∈ S := by
    simp only [hSdef, mem_filter, mem_range]
    exact ⟨Nat.lt_succ_self ℓ, hℓp, dvd_refl _⟩

  have hsplit := (add_sum_erase S (fun p => (1 : ℚ) / (p : ℚ)) hℓS).symm
  rw [hsplit] at hz

  have hz' : bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)
      = (z : ℚ) - ∑ p ∈ S.erase ℓ, (1 : ℚ) / (p : ℚ) := by
    linarith [hz]
  rw [hz', Rat.intCast_sub_den]

  have hdendvd := Rat.den_sum_dvd_prod_den (S.erase ℓ) (fun p => (1 : ℚ) / (p : ℚ))
  have hcop : (∏ p ∈ S.erase ℓ, ((1 : ℚ) / (p : ℚ)).den).Coprime ℓ := by
    refine Nat.Coprime.prod_left fun p hp => ?_
    have hpS : p ∈ S := Finset.mem_of_mem_erase hp
    have hpne : p ≠ ℓ := Finset.ne_of_mem_erase hp
    have hpp : p.Prime := (mem_filter.mp hpS).2.1
    have : ((1 : ℚ) / (p : ℚ)).den = p := by simp [hpp.ne_zero]
    rw [this]
    exact (Nat.coprime_primes hpp hℓp).mpr hpne
  intro hdvd
  exact (Nat.Prime.coprime_iff_not_dvd hℓp).mp
    (Nat.Coprime.of_dvd_left hdendvd hcop).symm hdvd

end ModularCurve.W1

/--
@isnad1 id=dvd.1h1v.s5.e8e288c22cfa from=translated src=- shape=d7ce7c75 vocab=0f52a813
-/
theorem ModularCurve.StarBank.eisInt_dvd_den {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ℓ ∣ (bernoulli (ℓ - 1)).den := by
  have hℓp : ℓ.Prime := Fact.out
  have hshift := ModularCurve.W1.eisInt_not_dvd_den_shift hℓ5

  have hℓden : ((1 : ℚ) / (ℓ : ℚ)).den = ℓ := by simp [hℓp.ne_zero]
  have hdvd : ℓ ∣ (bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)).den * (bernoulli (ℓ - 1)).den := by
    have h := Rat.sub_den_dvd (bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)) (bernoulli (ℓ - 1))
    have hsimp : bernoulli (ℓ - 1) + 1 / (ℓ : ℚ) - bernoulli (ℓ - 1) = 1 / (ℓ : ℚ) := by ring
    rw [hsimp, hℓden] at h
    exact h
  exact ((hℓp.dvd_mul).mp hdvd).resolve_left hshift

private theorem ModularCurve.StarBank.eisInt_not_dvd_num {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ¬ (ℓ : ℤ) ∣ (bernoulli (ℓ - 1)).num := by
  intro hdvd
  have hden := ModularCurve.StarBank.eisInt_dvd_den hℓ5
  have hnum : ℓ ∣ (bernoulli (ℓ - 1)).num.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have hcop := (bernoulli (ℓ - 1)).reduced
  have hgcd : ℓ ∣ Nat.gcd (bernoulli (ℓ - 1)).num.natAbs (bernoulli (ℓ - 1)).den :=
    Nat.dvd_gcd hnum hden
  unfold Nat.Coprime at hcop
  rw [hcop] at hgcd
  exact (Nat.Prime.one_lt (Fact.out : ℓ.Prime)).ne' (Nat.dvd_one.mp hgcd)

open scoped ArithmeticFunction.sigma
open Finset in

/--
@isnad1 id=not.1h1v.s5.557034d2c8c2 from=translated src=- shape=4e5e54bd vocab=b480e43c
-/
theorem solution {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ¬ (ℓ : ℤ) ∣ (bernoulli (ℓ - 1)).num :=
  ModularCurve.StarBank.eisInt_not_dvd_num hℓ5

