import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq

set_option autoImplicit false

namespace S17DW

variable {R : Type*} [CommRing R] {p : ℕ} [hp : Fact p.Prime]

/--
@isnad1 id=eq.0h4v.s7.f4e6302d3020 from=translated src=- shape=c1cfd4c2 vocab=8aa0e8ce
-/
theorem ghost_eq_sum (k : ℕ) (x : WittVector p R) :
    WittVector.ghostComponent k x =
      ∑ i ∈ Finset.range (k + 1), (p : R) ^ i * x.coeff i ^ p ^ (k - i) := by
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial]

/--
@isnad1 id=eq.3h6v.s8.d5644fda2949 from=translated src=- shape=71c95789 vocab=af2eae1d
-/
theorem coeff_eq_of_ghost_eq (hpR : (p : R) ∈ nonZeroDivisors R) (n : ℕ) (x y : WittVector p R)
    (h : ∀ k < n, WittVector.ghostComponent k x = WittVector.ghostComponent k y) :
    ∀ k < n, x.coeff k = y.coeff k := by
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih hk
  have hk' := h k hk
  rw [ghost_eq_sum, ghost_eq_sum, Finset.sum_range_succ, Finset.sum_range_succ, Nat.sub_self, pow_zero,
    pow_one, pow_one] at hk'
  have hS : ∑ i ∈ Finset.range k, (p : R) ^ i * x.coeff i ^ p ^ (k - i) =
      ∑ i ∈ Finset.range k, (p : R) ^ i * y.coeff i ^ p ^ (k - i) :=
    Finset.sum_congr rfl fun i hi => by
      rw [ih i (Finset.mem_range.1 hi) (lt_trans (Finset.mem_range.1 hi) hk)]
  rw [hS, add_right_inj] at hk'
  exact sub_eq_zero.1
    ((mem_nonZeroDivisors_iff.1 (pow_mem hpR k)).1 _ (by rw [mul_sub, hk', sub_self]))

end S17DW

universe u

/--
@isnad1 id=eq.3h6v.s8.d5644fda2949 from=translated src=- shape=71c95789 vocab=af2eae1d
-/
theorem solution
    {R : Type u} [CommRing R] (p : ℕ) [Fact p.Prime] (hp : (p : R) ∈ nonZeroDivisors R)
    (n : ℕ) (x y : WittVector p R)
    (h : ∀ k < n, WittVector.ghostComponent k x = WittVector.ghostComponent k y) :
    ∀ k < n, x.coeff k = y.coeff k :=
  S17DW.coeff_eq_of_ghost_eq hp n x y h
