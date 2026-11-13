import Tengoku.Seed.NumberTheory.EulerProduct.Basic
import Tengoku.Seed.NumberTheory.PrimeCounting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The finite smooth reciprocal Euler product This module proves the exact Euler-product identity in Lemma 2.2. -/

namespace RankAmplification

open scoped BigOperators Nat.Prime

noncomputable section

/-- The completely multiplicative reciprocal map `n ↦ 1/n`.-/
def reciprocalNatMonoidHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by
    simp only [Nat.cast_mul, mul_inv_rev]
    ring

/--
@isnad1 id=eq.0h1v.s5.77c0ef9d44db from=translated src=- shape=e81061cb vocab=7d23df18
-/
@[simp]
theorem reciprocalNatMonoidHom_apply (n : ℕ) :
    reciprocalNatMonoidHom n = (n : ℝ)⁻¹ := rfl

/-- The paper's finite Mertens product.-/
def mertensProduct (R : ℕ) : ℝ :=
  ∏ p ∈ Nat.primesLE R, (1 - (p : ℝ)⁻¹)⁻¹

/-- The convergent reciprocal sum over all positive integers whose prime factors are at most `R`.-/
def smoothReciprocalTsum (R : ℕ) : ℝ :=
  ∑' n : (R + 1).smoothNumbers, ((n.1 : ℝ)⁻¹)

/--
@isnad1 id=lt.1h1v.s5.755f43d02705 from=translated src=- shape=3071a3d3 vocab=765d5c37
-/
theorem norm_reciprocalNatMonoidHom_prime_lt_one {p : ℕ} (hp : p.Prime) :
    ‖reciprocalNatMonoidHom p‖ < 1 := by
  rw [reciprocalNatMonoidHom_apply, Real.norm_eq_abs, abs_inv, abs_of_nonneg (Nat.cast_nonneg p)]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

/-- Absolute convergence and the exact product formula over the weak cutoff `p ≤ R`.
@isnad1 id=and.0h1v.s7.1cf992b64ebe from=translated src=- shape=5bfd510b vocab=a0e2f931
-/
theorem summable_and_hasSum_smooth_reciprocals (R : ℕ) :
    Summable (fun n : (R + 1).smoothNumbers ↦ ‖((n.1 : ℝ)⁻¹)‖) ∧
      HasSum (fun n : (R + 1).smoothNumbers ↦ ((n.1 : ℝ)⁻¹)) (mertensProduct R) := by
  have h := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := reciprocalNatMonoidHom)
    (fun {_p} hp ↦ norm_reciprocalNatMonoidHom_prime_lt_one hp)
    (R + 1)
  simpa only [mertensProduct, Nat.primesLE, reciprocalNatMonoidHom_apply] using h

/-- Equality (2.1) of Lemma 2.2.
@isnad1 id=eq.0h1v.s3.65b4b6ea944a from=translated src=- shape=b70c6bb1 vocab=634f6dea
-/
theorem smoothReciprocalTsum_eq_mertensProduct (R : ℕ) :
    smoothReciprocalTsum R = mertensProduct R := by
  exact (summable_and_hasSum_smooth_reciprocals R).2.tsum_eq

/--
@isnad1 id=lt.0h1v.s3.77089121cca9 from=translated src=- shape=b9369acb vocab=0820beec
-/
theorem mertensProduct_pos (R : ℕ) : 0 < mertensProduct R := by
  unfold mertensProduct
  apply Finset.prod_pos
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primesLE hp
  have hone : (1 : ℝ) < p := by exact_mod_cast hpPrime.one_lt
  exact inv_pos.mpr (sub_pos.mpr (inv_lt_one_of_one_lt₀ hone))

/--
@isnad1 id=lt.0h1v.s3.a0e230dbaf3a from=translated src=- shape=b9369acb vocab=dd0c60ce
-/
theorem smoothReciprocalTsum_pos (R : ℕ) : 0 < smoothReciprocalTsum R := by
  rw [smoothReciprocalTsum_eq_mertensProduct]
  exact mertensProduct_pos R

end

end RankAmplification
