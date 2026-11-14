import Tengoku.Twinprime.TwinPrime.Analytic.PrimeDistribution
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite character decomposition of progression errors

The character sum includes positive integers through the stated natural
endpoint. Orthogonality applies only to a reduced residue. The principal
character and its excluded noncoprime terms are retained exactly.
-/

noncomputable section

open Finset ArithmeticFunction

namespace TwinPrime.Analytic

def characterPsi {q : ℕ} (t : ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Ioc 0 t, (vonMangoldt n : ℂ) * χ n

def noncoprimeMangoldtMass (t q : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 t with ¬ Nat.Coprime n q, vonMangoldt n

/--
@isnad1 id=le.0h2v.s4.2de71df57f06 from=translated src=- shape=5ffe46ab vocab=b4e1b820
-/
theorem noncoprimeMangoldtMass_nonneg (t q : ℕ) : 0 ≤ noncoprimeMangoldtMass t q :=
  sum_nonneg fun _ _ => vonMangoldt_nonneg

/--
@isnad1 id=eq.0h2v.s6.ef3d3ed6880d from=translated src=- shape=8f2ed2ca vocab=9fad0cfc
-/
theorem characterPsi_one (t q : ℕ) :
    characterPsi t (1 : DirichletCharacter ℂ q) =
      ((Chebyshev.psi (t : ℝ) - noncoprimeMangoldtMass t q : ℝ) : ℂ) := by
  have hchar : characterPsi t (1 : DirichletCharacter ℂ q) =
      ∑ n ∈ Ioc 0 t with Nat.Coprime n q, (vonMangoldt n : ℂ) := by
    unfold characterPsi
    rw [sum_filter]
    apply sum_congr rfl
    intro n _
    split_ifs with hn
    · rw [MulChar.one_apply ((ZMod.isUnit_iff_coprime n q).mpr hn), mul_one]
    · rw [MulChar.map_nonunit _
        (fun h => hn ((ZMod.isUnit_iff_coprime n q).mp h)), mul_zero]
  have hsum := sum_filter_add_sum_filter_not (Ioc 0 t) (fun n => Nat.Coprime n q)
    (fun n => vonMangoldt n)
  have heq : (∑ n ∈ Ioc 0 t with Nat.Coprime n q, vonMangoldt n) =
      Chebyshev.psi (t : ℝ) - noncoprimeMangoldtMass t q := by
    simpa only [Chebyshev.psi, Nat.floor_natCast, noncoprimeMangoldtMass] using
      (eq_sub_iff_add_eq.mpr hsum)
  rw [hchar, ← heq]
  simp

/-- Orthogonality retains all characters, including the principal one.
@isnad1 id=eq.2h3v.s7.7f53b544a951 from=translated src=- shape=e395b039 vocab=40caeb71
-/
theorem totient_mul_progressionPsi_eq_character_sum (t q a : ℕ)
    (hq : 0 < q) (ha : Nat.Coprime a q) :
    (Nat.totient q : ℂ) * (progressionPsi t q a : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * characterPsi t χ := by
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  have hu : IsUnit (a : ZMod q) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have heq : ∀ n : ℕ, ((a : ZMod q) = (n : ZMod q)) ↔ Nat.ModEq q n a := by
    intro n
    rw [ZMod.natCast_eq_natCast_iff]
    exact ⟨Nat.ModEq.symm, Nat.ModEq.symm⟩
  symm
  calc
    _ = ∑ n ∈ Ioc 0 t, (vonMangoldt n : ℂ) *
        ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * χ n := by
      simp only [characterPsi, mul_sum, ← mul_assoc]
      rw [sum_comm]
      apply sum_congr rfl
      intro n _
      apply sum_congr rfl
      intro χ _
      ring
    _ = ∑ n ∈ Ioc 0 t, if Nat.ModEq q n a then (vonMangoldt n : ℂ) * Nat.totient q else 0 := by
      apply sum_congr rfl
      intro n _
      simp only [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu, heq, mul_ite, mul_zero]
    _ = _ := by
      rw [← sum_filter, ← sum_mul]
      simp [progressionPsi, mul_comm]

/--
@isnad1 id=eq.2h3v.s7.9fa971fc88c9 from=translated src=- shape=19e2f9de vocab=47e6a070
-/
theorem progressionPsi_eq_character_sum (t q a : ℕ)
    (hq : 0 < q) (ha : Nat.Coprime a q) :
    (progressionPsi t q a : ℂ) =
      (∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * characterPsi t χ) /
        Nat.totient q := by
  have hφ : (Nat.totient q : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  apply (eq_div_iff hφ).mpr
  simpa only [mul_comm] using totient_mul_progressionPsi_eq_character_sum t q a hq ha

end TwinPrime.Analytic
