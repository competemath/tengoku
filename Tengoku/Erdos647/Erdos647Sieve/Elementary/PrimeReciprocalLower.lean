/-
An elementary fixed-constant lower bound for a finite prime-reciprocal sum.
This uses Mathlib's FINITE Euler product over a finite set of primes, not Mertens.
The auxiliary sum over integers supported on that finite prime set is proved
summable by the library theorem. No global summability of the harmonic series is used.
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators Topology

noncomputable section
namespace Erdos647Sieve.Elementary

/-- The prime set in the exact small-prime debit.-/
def debitPrimes (H : ℕ) : Finset ℕ := (Finset.Icc 2 H).filter Nat.Prime

/-- Finite Euler product at exponent one.-/
def finitePrimeEuler (H : ℕ) : ℝ :=
  ∏ p ∈ debitPrimes H, (1 - (p : ℝ)⁻¹)⁻¹

/-- Reciprocal of the natural-number cast is completely multiplicative, including zero.-/
def reciprocalNatHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' m n := by simp [mul_comm]

/--
@isnad1 id=lt.1h1v.s5.df2751b43d07 from=translated src=- shape=3071a3d3 vocab=e9c3dc74
-/
theorem reciprocalNatHom_prime_norm_lt_one {p : ℕ} (hp : p.Prime) :
    ‖reciprocalNatHom p‖ < 1 := by
  change ‖(p : ℝ)⁻¹‖ < 1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

/-- The finite Euler product dominates the first H terms of the harmonic series.
@isnad1 id=le.0h1v.s4.57d1f2774e12 from=translated src=- shape=d8da06ea vocab=1667fbe8
-/
theorem harmonic_sum_le_finitePrimeEuler (H : ℕ) :
    (∑ m ∈ Finset.Icc 1 H, (m : ℝ)⁻¹) ≤ finitePrimeEuler H := by
  classical
  have hs := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := reciprocalNatHom) (fun {_} hp => reciprocalNatHom_prime_norm_lt_one hp)
    (Finset.Icc 2 H)).2
  change HasSum (fun m : Nat.factoredNumbers (Finset.Icc 2 H) => ((m : ℕ) : ℝ)⁻¹)
    (finitePrimeEuler H) at hs
  let e : {m // m ∈ Finset.Icc 1 H} ↪ Nat.factoredNumbers (Finset.Icc 2 H) := {
    toFun := fun m => ⟨m.1, Nat.mem_factoredNumbers_iff_forall_le.mpr
      ⟨by have hm := (Finset.mem_Icc.mp m.2).1; omega,
       fun p hpm hp _ => Finset.mem_Icc.mpr
         ⟨hp.two_le, hpm.trans (Finset.mem_Icc.mp m.2).2⟩⟩⟩
    inj' := by
      intro m n h
      apply Subtype.ext
      exact congrArg (fun a : Nat.factoredNumbers (Finset.Icc 2 H) => (a : ℕ)) h
  }
  have hle := sum_le_hasSum ((Finset.Icc 1 H).attach.map e)
    (fun m _ => inv_nonneg.mpr (Nat.cast_nonneg (m : ℕ))) hs
  rw [Finset.sum_map] at hle
  change (∑ m ∈ (Finset.Icc 1 H).attach, (m.val : ℝ)⁻¹) ≤ finitePrimeEuler H at hle
  calc
    (∑ m ∈ Finset.Icc 1 H, (m : ℝ)⁻¹)
        = ∑ m ∈ (Finset.Icc 1 H).attach, (m.val : ℝ)⁻¹ :=
          (Finset.sum_attach (Finset.Icc 1 H) (fun m : ℕ => (m : ℝ)⁻¹)).symm
    _ ≤ finitePrimeEuler H := hle

/--
@isnad1 id=le.0h1v.s3.777723537da3 from=translated src=- shape=327d930b vocab=e47d66f5
-/
theorem log_le_finitePrimeEuler (H : ℕ) :
    Real.log (H : ℝ) ≤ finitePrimeEuler H := by
  have hh : Real.log (H : ℝ) ≤ (harmonic H : ℝ) := by
    simpa using log_le_harmonic_floor (H : ℝ) (Nat.cast_nonneg H)
  have heq : (harmonic H : ℝ) = ∑ m ∈ Finset.Icc 1 H, (m : ℝ)⁻¹ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [heq] at hh
  exact hh.trans (harmonic_sum_le_finitePrimeEuler H)

/-- A finite telescoping comparison, with no infinite-series assumption.
@isnad1 id=eq.0h1v.s6.f3f208955740 from=translated src=- shape=2f06ccc4 vocab=a4558860
-/
theorem reciprocal_remainder_telescope (n : ℕ) :
    (∑ m ∈ Finset.Icc 2 (n + 1), 1 / ((m : ℝ) * ((m : ℝ) - 1))) =
      1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show n.succ + 1 = (n + 1) + 1 by omega,
        Finset.sum_Icc_succ_top (by omega : 2 ≤ (n + 1) + 1), ih]
      push_cast
      have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
      simp only [add_sub_cancel_right]
      field_simp [h1, h2]
      ring

/--
@isnad1 id=le.1h1v.s6.bb5956c03cfd from=translated src=- shape=9585cb9f vocab=06268a03
-/
theorem prime_remainder_sum_le_one (H : ℕ) (hH : 1 ≤ H) :
    (∑ p ∈ debitPrimes H, 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 1 := by
  classical
  have hsubset : debitPrimes H ⊆ Finset.Icc 2 H := Finset.filter_subset _ _
  calc
    _ ≤ ∑ m ∈ Finset.Icc 2 H, 1 / ((m : ℝ) * ((m : ℝ) - 1)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro m hm _
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      apply one_div_nonneg.mpr
      exact mul_nonneg (by positivity) (by linarith)
    _ ≤ 1 := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : H ≠ 0)
      rw [show n.succ = n + 1 by omega, reciprocal_remainder_telescope]
      have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
      linarith

/-- The logarithmic remainder at 1/p is bounded by a telescoping summand.
@isnad1 id=le.1h1v.s6.e53fdc96ee0d from=translated src=- shape=638677c8 vocab=d22400d2
-/
theorem prime_log_factor_le (p : ℕ) (hp : 2 ≤ p) :
    -Real.log (1 - (p : ℝ)⁻¹) ≤
      (p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp1)
  have hm0 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hbase : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hbase)
  rw [Real.log_inv] at h
  calc
    _ ≤ (1 - (p : ℝ)⁻¹)⁻¹ - 1 := h
    _ = (p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      field_simp [hp0, hm0, ne_of_gt hbase]
      ring

/--
@isnad1 id=le.1h1v.s5.c43694c66631 from=translated src=- shape=caf9c160 vocab=af86b5cc
-/
theorem log_finitePrimeEuler_le (H : ℕ) (hH : 1 ≤ H) :
    Real.log (finitePrimeEuler H) ≤ (∑ p ∈ debitPrimes H, (p : ℝ)⁻¹) + 1 := by
  classical
  have hpos : ∀ p ∈ debitPrimes H, 0 < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hp2 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    apply sub_pos.mpr
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < p))
  unfold finitePrimeEuler
  rw [Real.log_prod (fun p hp => ne_of_gt (inv_pos.mpr (hpos p hp)))]
  simp only [Real.log_inv]
  calc
    _ ≤ ∑ p ∈ debitPrimes H, ((p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
      apply Finset.sum_le_sum
      intro p hp
      exact prime_log_factor_le p (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    _ = (∑ p ∈ debitPrimes H, (p : ℝ)⁻¹) +
        ∑ p ∈ debitPrimes H, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [Finset.sum_add_distrib]
    _ ≤ _ := add_le_add le_rfl (prime_remainder_sum_le_one H hH)

/-- The fixed constant -1 is obtained without knowing the value of the Mertens constant.
@isnad1 id=le.1h1v.s5.4d6e7b58335a from=translated src=- shape=b72b94fe vocab=3d23298d
-/
theorem prime_reciprocal_lower (H : ℕ) (hH : 2 ≤ H) :
    Real.log (Real.log (H : ℝ)) - 1 ≤ ∑ p ∈ debitPrimes H, (p : ℝ)⁻¹ := by
  have hlogpos : 0 < Real.log (H : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < H))
  have hmono := Real.log_le_log hlogpos (log_le_finitePrimeEuler H)
  have hupper := log_finitePrimeEuler_le H (by omega)
  linarith

end Erdos647Sieve.Elementary
end
