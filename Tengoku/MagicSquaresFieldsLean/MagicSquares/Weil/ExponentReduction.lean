import Tengoku.MagicSquaresFieldsLean.MagicSquares.Jacobi.Characters
import Tengoku.Seed.Algebra.GCDMonoid.Finset

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open scoped BigOperators Classical

/-- Removing the common divisor of the character order and all exponents
leaves a nontrivial character and primitive multiplicities. The evaluated
character product is unchanged, including at zero.-/
theorem exists_primitive_exponent_reduction
    {F : Type*} [Field F] [Fintype F]
    {r : ℕ} (chi : MulChar F ℂ) (exponents : Fin r → ℕ)
    (hpos : ∀ i, 0 < exponents i)
    (hnon : ∃ i, ¬ orderOf chi ∣ exponents i) :
    ∃ (tau : MulChar F ℂ) (reduced : Fin r → ℕ),
      2 ≤ orderOf tau ∧ (∀ i, 0 < reduced i) ∧
      (∀ p : ℕ, p.Prime → p ∣ orderOf tau → ∃ i, ¬ p ∣ reduced i) ∧
      ∀ values : Fin r → F,
        chi (∏ i, values i ^ exponents i) = tau (∏ i, values i ^ reduced i) := by
  let g := Nat.gcd (orderOf chi) (Finset.univ.gcd exponents)
  have hg : 0 < g := Nat.gcd_pos_of_pos_left _ chi.orderOf_pos
  have hgm : g ∣ orderOf chi := Nat.gcd_dvd_left _ _
  have hge (i : Fin r) : g ∣ exponents i :=
    (Nat.gcd_dvd_right _ _).trans (Finset.gcd_dvd (Finset.mem_univ i))
  have hmax {c : ℕ} (hcm : c ∣ orderOf chi) (hce : ∀ i, c ∣ exponents i) : c ∣ g :=
    Nat.dvd_gcd hcm (Finset.dvd_gcd_iff.mpr fun i _ => hce i)
  have horder : orderOf (chi ^ g) = orderOf chi / g := orderOf_pow_of_dvd hg.ne' hgm
  have hmpos : 0 < orderOf chi / g := Nat.div_pos (Nat.le_of_dvd chi.orderOf_pos hgm) hg
  have hm2 : 2 ≤ orderOf chi / g := by
    by_contra h
    have hm1 : orderOf chi / g = 1 := by omega
    have he : orderOf chi = g := by
      have hh := Nat.mul_div_cancel' hgm
      rw [hm1, mul_one] at hh
      exact hh.symm
    obtain ⟨i, hi⟩ := hnon
    exact hi (he ▸ hge i)
  refine ⟨chi ^ g, fun i => exponents i / g, by rwa [horder], ?_, ?_, ?_⟩
  · intro i
    exact Nat.div_pos (Nat.le_of_dvd (hpos i) (hge i)) hg
  · intro p hp hpm
    rw [horder] at hpm
    by_contra! h
    have hcm : g * p ∣ orderOf chi := by
      have hh := Nat.mul_dvd_mul_left g hpm
      rwa [Nat.mul_div_cancel' hgm] at hh
    have hce (i : Fin r) : g * p ∣ exponents i := by
      have hh := Nat.mul_dvd_mul_left g (h i)
      rwa [Nat.mul_div_cancel' (hge i)] at hh
    have hle := Nat.le_of_dvd hg (hmax hcm hce)
    have hp2 := hp.two_le
    nlinarith
  · intro values
    rw [chi.pow_apply' hg.ne', ← map_pow, ← Finset.prod_pow]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, Nat.div_mul_cancel (hge i)]

end MagicSquares.LN97
