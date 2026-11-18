import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
import Tengoku.Seed.LinearAlgebra.LinearIndependent.Basic
import Tengoku.Seed.Algebra.BigOperators.Finprod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_eq_of_forall_finsum_cpow_neg_mul_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_eq_of_forall_finsum_cpow_neg_mul_eq

set_option autoImplicit false

/--
@isnad1 id=eq.4h3v.s7.599a4784630e from=translated src=- shape=8fa7bb7a vocab=cf8d5ef9
-/
theorem solution
    (N : ℕ) (hN : 1 < N) (a b : ℤ → ℂ)
    (ha : (Function.support a).Finite) (hb : (Function.support b).Finite)
    (h : ∀ u : ℂ, ∑ᶠ i : ℤ, (N : ℂ) ^ (-(i : ℂ) * u) * a i = ∑ᶠ i : ℤ, (N : ℂ) ^ (-(i : ℂ) * u) * b i) :
    a = b := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)

  let χ : ℤ → (Multiplicative ℂ →* ℂ) := fun i =>
    { toFun := fun u => (N : ℂ) ^ (-(i : ℂ) * Multiplicative.toAdd u)
      map_one' := by simp
      map_mul' := fun u v => by
        simp only [toAdd_mul, mul_add, Complex.cpow_add _ _ hN0] }
  have hχ : ∀ (i : ℤ) (u : Multiplicative ℂ), χ i u = (N : ℂ) ^ (-(i : ℂ) * Multiplicative.toAdd u) :=
    fun i u => rfl
  have hinj : Function.Injective χ := by
    intro i j hij
    have h1 := congrArg (fun f : Multiplicative ℂ →* ℂ => f (Multiplicative.ofAdd (1 : ℂ))) hij
    simp only [hχ, toAdd_ofAdd, mul_one] at h1
    rw [show (-(i : ℂ)) = ((-i : ℤ) : ℂ) by push_cast; ring, show (-(j : ℂ)) = ((-j : ℤ) : ℂ) by push_cast; ring,
      Complex.cpow_intCast, Complex.cpow_intCast, ← Complex.ofReal_natCast, ← Complex.ofReal_zpow,
      ← Complex.ofReal_zpow] at h1
    have h2 := Complex.ofReal_injective h1
    have h3 := zpow_right_injective₀ (a := (N : ℝ)) (by positivity) (by exact_mod_cast (show N ≠ 1 by omega)) h2
    omega
  have hli : LinearIndependent ℂ (fun i : ℤ => ((χ i : Multiplicative ℂ →* ℂ) : Multiplicative ℂ → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative ℂ) ℂ).comp χ hinj

  set S : Finset ℤ := (ha.union hb).toFinset with hS
  have haS : Function.support a ⊆ (S : Set ℤ) := by
    intro i hi; simp only [hS, Set.Finite.coe_toFinset]; exact Or.inl hi
  have hbS : Function.support b ⊆ (S : Set ℤ) := by
    intro i hi; simp only [hS, Set.Finite.coe_toFinset]; exact Or.inr hi
  have hsum : ∑ i ∈ S, (a i - b i) • ((χ i : Multiplicative ℂ →* ℂ) : Multiplicative ℂ → ℂ) = 0 := by
    funext u
    have hu := h (Multiplicative.toAdd u)
    rw [finsum_eq_sum_of_support_subset _ ((Function.support_mul_subset_right _ _).trans haS),
      finsum_eq_sum_of_support_subset _ ((Function.support_mul_subset_right _ _).trans hbS), ← sub_eq_zero,
      ← Finset.sum_sub_distrib] at hu
    rw [Finset.sum_apply, Pi.zero_apply, ← hu]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, hχ]
    ring
  have hc0 := linearIndependent_iff'.mp hli S (fun i => a i - b i) hsum
  funext i
  by_cases hi : i ∈ S
  · exact sub_eq_zero.mp (hc0 i hi)
  · have hai : a i = 0 := by
      by_contra hne; exact hi (haS hne)
    have hbi : b i = 0 := by
      by_contra hne; exact hi (hbS hne)
    rw [hai, hbi]
