import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_End_sum_range_pow_eq_zero_of_pow_eq_one_of_mul_dvd.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_End_sum_range_pow_eq_zero_of_pow_eq_one_of_mul_dvd

set_option autoImplicit false

/--
@isnad1 id=eq.2h6v.s8.43b31d43a5b6 from=translated src=- shape=bba8f2c5 vocab=26fcbff0
-/
theorem solution {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (p : ℕ) [CharP R p] (T : Module.End R V) {d n : ℕ} (hd : T ^ d = 1) (hdn : p * d ∣ n) :
    ∑ i ∈ Finset.range n, T ^ i = 0 := by
  obtain ⟨c, rfl⟩ := hdn
  have hblock : ∀ m : ℕ, ∑ i ∈ Finset.range (d * m), T ^ i = m • ∑ i ∈ Finset.range d, T ^ i := by
    intro m
    induction m with
    | zero => rw [mul_zero, Finset.sum_range_zero, zero_smul]
    | succ m ih =>
      rw [mul_add, mul_one, Finset.sum_range_add, ih, add_smul, one_smul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_add, pow_mul, hd, one_pow, one_mul]
  rw [show p * d * c = d * (p * c) by ring, hblock, mul_smul, ← Nat.cast_smul_eq_nsmul R p,
    CharP.cast_eq_zero, zero_smul]
