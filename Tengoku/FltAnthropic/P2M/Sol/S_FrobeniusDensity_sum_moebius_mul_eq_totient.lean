import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FrobeniusDensity_sum_moebius_mul_eq_totient.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FrobeniusDensity_sum_moebius_mul_eq_totient

set_option autoImplicit false

open scoped Classical

namespace FltWs24
namespace RationalClass

variable {G : Type*} [Group G]

/--
@isnad1 id=eq.1h1v.s6.d1f5aee0749f from=translated src=- shape=48e1ce87 vocab=6fb309c8
-/
theorem sum_moebius_mul_eq_totient (n : ℕ) (hn : 0 < n) :
    ∑ f ∈ n.divisors, (ArithmeticFunction.moebius (n / f)) * (f : ℤ) = (Nat.totient n : ℤ) := by
  have key : ∀ m > 0, ∑ x ∈ m.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.fst : ℤ) * (x.snd : ℤ) = (Nat.totient m : ℤ) := by
    refine (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ)
      (f := fun k => (Nat.totient k : ℤ)) (g := fun k => (k : ℤ))).mp ?_
    intro m _
    exact_mod_cast Nat.sum_totient m
  rw [← key n hn]
  exact (Nat.sum_divisorsAntidiagonal' (fun a b => (ArithmeticFunction.moebius a : ℤ) * (b : ℤ))).symm

end FltWs24.RationalClass

/--
@isnad1 id=eq.1h1v.s6.d1f5aee0749f from=translated src=- shape=48e1ce87 vocab=6fb309c8
-/
theorem solution (n : ℕ) (hn : 0 < n) :
    ∑ f ∈ n.divisors, (ArithmeticFunction.moebius (n / f)) * (f : ℤ) = (Nat.totient n : ℤ) :=
  FltWs24.RationalClass.sum_moebius_mul_eq_totient n hn
