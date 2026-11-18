import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.Seed.Algebra.Polynomial.Eval.Defs
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_RankinSelberg_exists_sum_cpow_mul_eval_eq_cpow_mul_eval.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_RankinSelberg_exists_sum_cpow_mul_eval_eq_cpow_mul_eval

set_option autoImplicit false

/--
@isnad1 id=ex.1h4v.s7.9d036d8e4be8 from=translated src=- shape=83e4bb20 vocab=f74884a5
-/
theorem solution
    (N : ℕ) (hN : N ≠ 0) (ι : Type) [Fintype ι] (m : ι → ℤ) (P : ι → Polynomial ℂ) :
    ∃ (m₀ : ℤ) (P₀ : Polynomial ℂ), ∀ s : ℂ,
      ∑ i, (N : ℂ) ^ ((m i : ℂ) * s) * (P i).eval ((N : ℂ) ^ (-s)) =
        (N : ℂ) ^ ((m₀ : ℂ) * s) * P₀.eval ((N : ℂ) ^ (-s)) := by
  classical
  refine ⟨((Finset.univ.sup (fun i => (m i).toNat) : ℕ) : ℤ),
    ∑ i, Polynomial.X ^ (((Finset.univ.sup (fun i => (m i).toNat) : ℕ) : ℤ) - m i).toNat * P i, ?_⟩
  intro s
  set A : ℕ := Finset.univ.sup (fun i => (m i).toNat) with hA
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [Polynomial.eval_finsetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hle : m i ≤ (A : ℤ) := by
    have h1 : (m i).toNat ≤ A := Finset.le_sup (f := fun i => (m i).toNat) (Finset.mem_univ i)
    have h2 : m i ≤ ((m i).toNat : ℤ) := Int.self_le_toNat _
    omega
  have hk : ((((A : ℤ) - m i).toNat : ℕ) : ℂ) = (A : ℂ) - (m i : ℂ) := by
    have h' := congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg (show 0 ≤ (A : ℤ) - m i by omega))
    push_cast at h'
    exact h'
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, ← Complex.cpow_nat_mul,
    show (N : ℂ) ^ ((m i : ℂ) * s) =
        (N : ℂ) ^ ((((A : ℕ) : ℤ) : ℂ) * s) * (N : ℂ) ^ ((((A : ℤ) - m i).toNat : ℂ) * -s) by
      rw [← Complex.cpow_add _ _ hN', hk]
      congr 1
      push_cast
      ring]
  ring
