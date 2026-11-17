import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FormalHecke_Eigensystem
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_EisensteinChiNegThree
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_IntegralLattice
import Tengoku.FltAnthropic.Definitions.Def_PowerSeries_FormalHeckeOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FLT_OccurrenceStatement_three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FLT_OccurrenceStatement_three_dvd_coeff_heckeT_two_sub_smul_of_not_dvd

open EisensteinWeightOne

namespace LaneB

/--
@isnad1 id=eq.0h2v.s7.c926f36322f5 from=translated src=- shape=39ec5e47 vocab=43cd06c6
-/
lemma coeff_e1Chi3In {R : Type*} [CommRing R] (j : ℕ) :
    PowerSeries.coeff j (e1Chi3In R) = if j = 0 then 1 else ((6 * sigmaChi j : ℤ) : R) := by
  simp only [e1Chi3In, e1Chi3, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  split_ifs <;> simp

/--
@isnad1 id=dvd.0h3v.s8.735c5a48b98e from=translated src=- shape=c6ac899d vocab=534cef87
-/
theorem three_dvd_coeff_mul_e1Chi3In_sub {R : Type*} [CommRing R] (g : PowerSeries R) (n : ℕ) :
    (3 : R) ∣ PowerSeries.coeff n (g * e1Chi3In R) - PowerSeries.coeff n g := by
  classical
  rw [PowerSeries.coeff_mul]
  have hmem : (n, 0) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
  rw [← Finset.add_sum_erase _ _ hmem, coeff_e1Chi3In, ite_eq_left rfl, mul_one, add_sub_cancel_left]
  refine Finset.dvd_sum fun ij hij => ?_
  obtain ⟨hne, hanti⟩ := Finset.mem_erase.mp hij
  have hj : ij.2 ≠ 0 := by
    intro h0
    apply hne
    have : ij.1 = n := by simpa [h0] using Finset.HasAntidiagonal.mem_antidiagonal.mp hanti
    exact Prod.ext this h0
  rw [coeff_e1Chi3In, ite_eq_right hj]
  refine Dvd.dvd.mul_left ?_ _
  refine ⟨((2 * sigmaChi ij.2 : ℤ) : R), ?_⟩
  push_cast
  ring

/--
@isnad1 id=dvd.0h3v.s7.9a7c22ebe904 from=translated src=- shape=2fc70913 vocab=be03cac9
-/
theorem three_dvd_coeff_bridgeProduct_sub {R : Type*} [CommRing R] (a : ℕ → R) (m : ℕ) :
    (3 : R) ∣ PowerSeries.coeff m (bridgeProduct a) - a m := by
  have h := three_dvd_coeff_mul_e1Chi3In_sub (PowerSeries.mk a) m
  rwa [PowerSeries.coeff_mk] at h

/--
@isnad1 id=dvd.0h2v.s6.f42a8396cff9 from=translated src=- shape=dc2606f7 vocab=e55f4cee
-/
theorem three_dvd_natCast_sub_chiNegThree_cast (R : Type*) [CommRing R] (ℓ : ℕ) :
    (3 : R) ∣ (ℓ : R) - ((chiNegThree ℓ : ℤ) : R) := by
  have h : (3 : ℤ) ∣ (ℓ : ℤ) - chiNegThree ℓ := by
    simp only [chiNegThree]
    split_ifs <;> omega
  obtain ⟨c, hc⟩ := h
  refine ⟨(c : R), ?_⟩
  have h := congrArg (fun z : ℤ => (z : R)) hc
  push_cast at h
  convert h using 2

/--
@isnad1 id=dvd.1h5v.s9.8642288017ce from=translated src=- shape=ff05e36e vocab=0a1288dd
-/
theorem three_dvd_coeff_heckeT_two_sub_residual {R : Type*} [CommRing R] (a : ℕ → R)
    {ℓ : ℕ} (eℓ : R)
    (hrec : ∀ n : ℕ, a (ℓ * n) + eℓ * (if ℓ ∣ n then a (n / ℓ) else 0) = a ℓ * a n)
    (n : ℕ) :
    (3 : R) ∣ (PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a))
        - a ℓ * PowerSeries.coeff n (bridgeProduct a))
      - ((ℓ : R) - eℓ) * (if ℓ ∣ n then a (n / ℓ) else 0) := by
  have hA : ∀ m : ℕ, (3 : R) ∣ PowerSeries.coeff m (bridgeProduct a) - a m :=
    three_dvd_coeff_bridgeProduct_sub a
  have hD : (3 : R) ∣ (if ℓ ∣ n then PowerSeries.coeff (n / ℓ) (bridgeProduct a) else 0)
      - (if ℓ ∣ n then a (n / ℓ) else 0) := by
    split
    · exact hA (n / ℓ)
    · simp
  have hkey : (PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a))
        - a ℓ * PowerSeries.coeff n (bridgeProduct a))
      - ((ℓ : R) - eℓ) * (if ℓ ∣ n then a (n / ℓ) else 0)
      = (PowerSeries.coeff (ℓ * n) (bridgeProduct a) - a (ℓ * n))
        + (ℓ : R) * ((if ℓ ∣ n then PowerSeries.coeff (n / ℓ) (bridgeProduct a) else 0)
            - (if ℓ ∣ n then a (n / ℓ) else 0))
        - a ℓ * (PowerSeries.coeff n (bridgeProduct a) - a n) := by
    rw [PowerSeries.coeff_heckeT]
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    linear_combination hrec n
  rw [hkey]
  exact dvd_sub (dvd_add (hA (ℓ * n)) (hD.mul_left (ℓ : R))) ((hA n).mul_left (a ℓ))

end LaneB

/--
@isnad1 id=dvd.3h5v.s9.8cb4d6f137fd from=translated src=- shape=8a73196c vocab=c85ba1d5
-/
theorem solution {R : Type*} [CommRing R] {N : ℕ} {a : ℕ → R}
    (heig : FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : R)) a)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (n : ℕ) :
    (3 : R) ∣ PowerSeries.coeff n
      (PowerSeries.heckeT ℓ 2 (bridgeProduct a) - a ℓ • bridgeProduct a) := by
  have hrec : ∀ m : ℕ,
      a (ℓ * m) + ((chiNegThree ℓ : ℤ) : R) * (if ℓ ∣ m then a (m / ℓ) else 0) = a ℓ * a m := by
    simpa only [ite_eq_right hℓN] using heig.2 ℓ hℓ
  have h1 := LaneB.three_dvd_coeff_heckeT_two_sub_residual a ((chiNegThree ℓ : ℤ) : R) hrec n
  have h2 : (3 : R) ∣ ((ℓ : R) - ((chiNegThree ℓ : ℤ) : R)) * (if ℓ ∣ n then a (n / ℓ) else 0) :=
    (LaneB.three_dvd_natCast_sub_chiNegThree_cast R ℓ).mul_right _
  have hmul : (3 : R) ∣ PowerSeries.coeff n (PowerSeries.heckeT ℓ 2 (bridgeProduct a))
      - a ℓ * PowerSeries.coeff n (bridgeProduct a) := by
    have := dvd_add h1 h2
    simpa using this
  have hsm : PowerSeries.coeff n (a ℓ • bridgeProduct a) = a ℓ * PowerSeries.coeff n (bridgeProduct a) := by
    rw [map_smul, smul_eq_mul]
  rw [map_sub, hsm]
  exact hmul
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
